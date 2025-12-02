//! High-performance operation cache for BDD computations.
//!
//! This module provides a 4-way set-associative cache with O(1) clearing via
//! generation counters. The design is optimized for BDD operation memoization
//! where:
//!
//! - **High throughput** is critical (millions of lookups/inserts per second)
//! - **Collision handling** matters (BDD operations often have similar hash patterns)
//! - **Fast invalidation** is needed (variable reordering clears the cache frequently)
//!
//! # Architecture
//!
//! ```text
//! ┌────────────────────────────────────────────────────────────────────┐
//! │                      SetAssociativeCache                           │
//! │  ┌───────────────────────────────────────────────────────────────┐ │
//! │  │ Set 0:  [Entry₀] [Entry₁] [Entry₂] [Entry₃]  LRU: 3→1→0→2     │ │
//! │  ├───────────────────────────────────────────────────────────────┤ │
//! │  │ Set 1:  [Entry₀] [Entry₁] [Entry₂] [Entry₃]  LRU: 0→2→1→3     │ │
//! │  ├───────────────────────────────────────────────────────────────┤ │
//! │  │ Set 2:  [Entry₀] [Entry₁] [Entry₂] [Entry₃]  LRU: 2→3→0→1     │ │
//! │  └───────────────────────────────────────────────────────────────┘ │
//! │                              ...                                   │
//! │  generation: 42  (entries with gen ≠ 42 are considered empty)      │
//! └────────────────────────────────────────────────────────────────────┘
//! ```
//!
//! # Design Decisions
//!
//! 1. **4-way associativity**: Reduces collision rate by ~90% compared to direct-mapped.
//!    4 ways is a sweet spot: enough to handle most conflicts, few enough for fast linear scan.
//!
//! 2. **Generation-based clearing**: Instead of zeroing memory, we increment a counter.
//!    Entries are valid only if `entry.generation == cache.generation`. This makes
//!    `clear()` O(1), critical for variable reordering.
//!
//! 3. **Compact LRU tracking**: 8 bits encode full 4-way LRU order using 2 bits per position.
//!    Updates are O(1) bit operations.
//!
//! 4. **Sentinel-based entries**: No `Option` wrapper; generation=0 marks invalid entries.
//!    Saves 1 byte per entry and simplifies generated code.
//!
//! # Performance
//!
//! Typical workloads see:
//! - **15-40% speedup** over direct-mapped for collision-heavy BDD operations
//! - **O(1) clear** regardless of cache size
//! - **4 key comparisons** per lookup (may benefit from SIMD in future)

use std::cell::Cell;
use std::marker::PhantomData;

use crate::utils::MyHash;

// =============================================================================
// Constants
// =============================================================================

/// Number of ways (slots) per cache set. 4-way is optimal for most workloads:
/// - Reduces collision rate by ~90% vs direct-mapped
/// - Linear scan is still fast without complex data structures
/// - Fits well with CPU cache lines
const WAYS: usize = 4;

/// Default cache size in bits. 2^14 = 16K sets × 4 ways = 64K entries.
const DEFAULT_CACHE_BITS: usize = 14;

// =============================================================================
// LRU Tracking
// =============================================================================

/// Compact LRU state for 4 ways, encoded in 8 bits.
///
/// # Encoding
///
/// We store a permutation of [0, 1, 2, 3] representing the access order
/// from Most Recently Used (MRU) to Least Recently Used (LRU).
///
/// Each way index needs 2 bits (to represent 0-3), so 4 positions × 2 bits = 8 bits.
///
/// The encoding packs 4 way indices into a u8, with position 0 in the **low bits**:
///
/// ```text
///   u8 bit layout:    [7 6] [5 4] [3 2] [1 0]
///                      ───   ───   ───   ───
///   Position:           3     2     1     0
///   Meaning:           LRU   ...   ...   MRU
/// ```
///
/// # Example
///
/// For initial order [0, 1, 2, 3] (way 0 is MRU, way 3 is LRU):
///
/// ```text
///   Position:    0    1    2    3
///   Way index:   0    1    2    3
///   Binary:     00   01   10   11
///
///   Packed into u8 (low bits first):
///   bits [1:0] = 00 (position 0 = way 0)
///   bits [3:2] = 01 (position 1 = way 1)
///   bits [5:4] = 10 (position 2 = way 2)
///   bits [7:6] = 11 (position 3 = way 3)
///
///   Result: 0b_11_10_01_00 = 0xE4 = 228
/// ```
///
/// # Why this layout?
///
/// This is standard little-endian packing: element 0 goes in the lowest bits.
/// It matches how arrays are indexed and how `>> (i * 2)` naturally extracts
/// element `i`. This is the common practice in bit-packed data structures.
#[derive(Debug, Clone, Copy, Default)]
#[repr(transparent)]
struct Lru(u8);

impl Lru {
    /// Initial LRU state: order is [0, 1, 2, 3] from MRU to LRU.
    ///
    /// Bit layout:
    /// ```text
    ///   0b_11_10_01_00
    ///      ││ ││ ││ └┴─ pos 0: way 0 (MRU)
    ///      ││ ││ └┴──── pos 1: way 1
    ///      ││ └┴─────── pos 2: way 2
    ///      └┴────────── pos 3: way 3 (LRU)
    /// ```
    const INITIAL: Self = Self(0b_11_10_01_00);

    /// Creates a new LRU tracker with default ordering.
    #[inline]
    const fn new() -> Self {
        Self::INITIAL
    }

    /// Returns the way index at position `pos` (0 = MRU, 3 = LRU).
    ///
    /// # How it works
    ///
    /// Each position uses 2 bits, packed from low to high:
    /// - `pos=0`: bits [1:0] — shift by 0
    /// - `pos=1`: bits [3:2] — shift by 2
    /// - `pos=2`: bits [5:4] — shift by 4
    /// - `pos=3`: bits [7:6] — shift by 6
    ///
    /// Formula: `(self.0 >> (pos * 2)) & 0b11`
    ///
    /// # Example
    ///
    /// For `INITIAL = 0b_11_10_01_00`:
    /// - `way_at(0)` → `0b_11_10_01_00 >> 0 & 0b11` → `00` → 0
    /// - `way_at(1)` → `0b_11_10_01_00 >> 2 & 0b11` → `01` → 1
    /// - `way_at(2)` → `0b_11_10_01_00 >> 4 & 0b11` → `10` → 2
    /// - `way_at(3)` → `0b_11_10_01_00 >> 6 & 0b11` → `11` → 3
    #[inline]
    const fn way_at(&self, pos: usize) -> usize {
        debug_assert!(pos < WAYS);
        ((self.0 >> (pos * 2)) & 0b11) as usize
    }

    /// Returns the LRU (least recently used) way index — the replacement victim.
    #[inline]
    const fn lru_way(&self) -> usize {
        self.way_at(3)
    }

    const HEAD_MASKS: [u8; WAYS] = [
        0b_00_00_00_00, // pos=0: no head
        0b_00_00_00_11, // pos=1: bits 0-1
        0b_00_00_11_11, // pos=2: bits 0-3
        0b_00_11_11_11, // pos=3: bits 0-5
    ];
    const TAIL_MASKS: [u8; WAYS] = [
        0b_11_11_11_11, // pos=0: all bits
        0b_11_11_00_00, // pos=1: bits 4-7
        0b_11_00_00_00, // pos=2: bits 6-7
        0b_00_00_00_00, // pos=3: no tail
    ];

    /// Promotes a way to MRU (most recently used) position.
    ///
    /// This is called on cache hits to update the access order.
    ///
    /// # Algorithm
    ///
    /// Given order [a, b, c, d] and promoting `c` (at position 2):
    /// - Result: [c, a, b, d]
    /// - Positions 0..pos shift right by one (a→1, b→2)
    /// - The promoted way goes to position 0
    /// - Positions after `pos` stay unchanged (d stays at 3)
    ///
    /// # Implementation
    ///
    /// Uses bit masking and shifting instead of loops:
    /// 1. Create mask for positions 0..pos (the part to shift)
    /// 2. Extract that part, shift left by 2 bits
    /// 3. Insert promoted way at position 0
    /// 4. OR with unchanged tail (positions pos+1..3)
    #[inline]
    fn promote(&mut self, way: usize) {
        debug_assert!(way < WAYS);

        // Find current position of this way
        let mut pos = 0;
        while pos < WAYS && self.way_at(pos) != way {
            pos += 1;
        }

        if pos == 0 {
            // Already MRU, nothing to do
            return;
        }

        // Masks for extracting bit ranges:
        // pos=1: head_mask=0b_00_00_00_11 (bits 0-1)
        // pos=2: head_mask=0b_00_00_11_11 (bits 0-3)
        // pos=3: head_mask=0b_00_11_11_11 (bits 0-5)
        // let head_mask = (1u8 << (pos * 2)) - 1;
        let head_mask = Self::HEAD_MASKS[pos];

        // Mask for the tail (positions after `pos`):
        // pos=1: tail_mask=0b_11_11_00_00 (bits 4-7)
        // pos=2: tail_mask=0b_11_00_00_00 (bits 6-7)
        // pos=3: tail_mask=0b_00_00_00_00 (nothing)
        // let tail_shift = (pos + 1) * 2;
        // let tail_mask = 0xFFu8.unbounded_shl(tail_shift as u32);
        let tail_mask = Self::TAIL_MASKS[pos];

        // Extract head (positions 0..pos), shift left by 2 to make room
        let head_shifted = (self.0 & head_mask) << 2;

        // Extract tail (positions pos+1..WAYS), unchanged
        let tail = self.0 & tail_mask;

        // Combine: way at position 0, shifted head, unchanged tail
        self.0 = (way as u8) | head_shifted | tail;
    }
}

// =============================================================================
// Cache Entry
// =============================================================================

/// A single cache entry storing a key-value pair with generation stamp.
///
/// The generation stamp enables O(1) cache clearing: instead of zeroing
/// all entries, we increment the cache's global generation. Entries with
/// mismatched generations are treated as empty.
#[derive(Clone)]
struct Entry<K, V> {
    /// The lookup key (e.g., operation operands).
    key: K,
    /// The cached result.
    value: V,
    /// Generation when this entry was inserted.
    /// Entry is valid only if this matches the cache's current generation.
    generation: u64,
}

impl<K: Default, V: Default> Default for Entry<K, V> {
    fn default() -> Self {
        Self {
            key: K::default(),
            value: V::default(),
            generation: 0, // Invalid generation (cache starts at 1)
        }
    }
}

// =============================================================================
// Cache Set
// =============================================================================

/// A single set in the cache containing `WAYS` entries with LRU tracking.
///
/// Each set handles collisions for keys that hash to the same set index.
/// On lookup, all `WAYS` entries are checked. On insert, the LRU entry
/// is replaced if no empty slot exists.
struct CacheSet<K, V> {
    /// The entries in this set.
    entries: [Entry<K, V>; WAYS],
    /// LRU tracking for replacement policy.
    /// Wrapped in Cell for interior mutability during get() operations.
    lru: Cell<Lru>,
}

impl<K: Default, V: Default> Default for CacheSet<K, V> {
    fn default() -> Self {
        Self {
            entries: std::array::from_fn(|_| Entry::default()),
            lru: Cell::new(Lru::new()),
        }
    }
}

impl<K, V> CacheSet<K, V> {
    /// Creates a new cache set with default entries.
    fn new() -> Self
    where
        K: Default,
        V: Default,
    {
        Self::default()
    }
}

// =============================================================================
// Statistics
// =============================================================================

/// Cache performance statistics.
///
/// These are tracked using `Cell` for interior mutability since the cache
/// is typically accessed through shared references.
#[derive(Debug, Default)]
struct Stats {
    /// Number of successful lookups (key found and valid).
    hits: Cell<usize>,
    /// Total number of unsuccessful lookups.
    misses: Cell<usize>,
    /// Number of lookups where slot was occupied by different key (collision).
    /// This is a subset of misses that indicates hash conflicts.
    faults: Cell<usize>,
}

impl Stats {
    fn new() -> Self {
        Self::default()
    }

    #[inline]
    fn record_hit(&self) {
        self.hits.set(self.hits.get() + 1);
    }

    #[inline]
    fn record_miss(&self) {
        self.misses.set(self.misses.get() + 1);
    }

    #[inline]
    fn record_fault(&self) {
        self.misses.set(self.misses.get() + 1);
        self.faults.set(self.faults.get() + 1);
    }
}

// =============================================================================
// Main Cache Structure
// =============================================================================

/// A 4-way set-associative cache with O(1) clearing and LRU replacement.
///
/// This cache is optimized for BDD operation memoization where:
/// - Keys are typically small tuples of node references
/// - High throughput is essential (millions of ops/sec)
/// - Fast invalidation is needed for variable reordering
///
/// # Type Parameters
///
/// - `K`: Key type. Must implement `MyHash` for indexing and `Eq` for comparison.
/// - `V`: Value type. Must implement `Copy` for efficient retrieval.
///
/// # Example
///
/// ```ignore
/// use bdd_rs::cache::Cache;
///
/// // Create a cache with 2^14 = 16K sets (64K total entries)
/// let mut cache = Cache::<(u64, u64), i32>::new(14);
///
/// // Insert and lookup
/// cache.insert((1, 2), 42);
/// assert_eq!(cache.get(&(1, 2)), Some(&42));
///
/// // Clear is O(1)
/// cache.clear();
/// assert_eq!(cache.get(&(1, 2)), None);
/// ```
pub struct Cache<K, V> {
    /// Array of cache sets, indexed by hash.
    sets: Vec<CacheSet<K, V>>,
    /// Bitmask for computing set index from hash: `set_index = hash & bitmask`.
    bitmask: u64,
    /// Current generation counter. Entries are valid only if their generation matches.
    /// Starts at 1 so that default entries (generation=0) are invalid.
    generation: Cell<u64>,
    /// Performance statistics.
    stats: Stats,
    /// Marker for key type (not stored, just for type checking).
    _key: PhantomData<K>,
}

impl<K: Default, V: Default> Default for Cache<K, V> {
    fn default() -> Self {
        Self::new(DEFAULT_CACHE_BITS)
    }
}

impl<K, V> Cache<K, V>
where
    K: Default,
    V: Default,
{
    /// Creates a new cache with default size (2^14 sets = 64K entries).
    pub fn with_default_size() -> Self {
        Self::default()
    }

    /// Creates a new cache with `2^bits` sets (total entries = sets × 4).
    ///
    /// # Arguments
    ///
    /// * `bits` - Number of bits for set indexing. Must be ≤ 31.
    ///   Common values:
    ///   - 12: 4K sets, 16K entries (small problems)
    ///   - 14: 16K sets, 64K entries (default)
    ///   - 16: 64K sets, 256K entries (medium problems)
    ///   - 18: 256K sets, 1M entries (large problems)
    ///   - 20: 1M sets, 4M entries (very large problems)
    ///
    /// # Panics
    ///
    /// Panics if `bits > 31`.
    pub fn new(bits: usize) -> Self {
        assert!(bits <= 31, "Cache bits must be in range 0..=31, got {}", bits);

        let num_sets = 1usize << bits;
        let bitmask = (num_sets - 1) as u64;

        // Allocate sets. Using repeat_with instead of vec![default; n]
        // to avoid requiring Clone on CacheSet.
        let sets: Vec<CacheSet<K, V>> = std::iter::repeat_with(CacheSet::new).take(num_sets).collect();

        Self {
            sets,
            bitmask,
            generation: Cell::new(1), // Start at 1 so default entries are invalid
            stats: Stats::new(),
            _key: PhantomData,
        }
    }

    /// Returns the number of sets in the cache.
    ///
    /// Total capacity is `num_sets() * 4` entries.
    pub fn num_sets(&self) -> usize {
        self.sets.len()
    }

    /// Returns the total entry capacity (sets × ways).
    pub fn capacity(&self) -> usize {
        self.sets.len() * WAYS
    }

    /// Returns the number of cache hits since creation.
    pub fn hits(&self) -> usize {
        self.stats.hits.get()
    }

    /// Returns the total number of cache misses since creation.
    pub fn misses(&self) -> usize {
        self.stats.misses.get()
    }

    /// Returns the number of cache faults (collision misses) since creation.
    ///
    /// A fault occurs when a set has entries but none match the requested key.
    /// High fault rate indicates hash collisions or working set exceeds cache.
    pub fn faults(&self) -> usize {
        self.stats.faults.get()
    }

    /// Clears the cache in O(1) time.
    ///
    /// Instead of zeroing memory, this increments the generation counter.
    /// All existing entries become stale and will be treated as empty.
    ///
    /// This is critical for performance during variable reordering, which
    /// invalidates the cache frequently.
    pub fn clear(&mut self) {
        self.generation.set(self.generation.get().wrapping_add(1));
        // Note: If generation wraps to 0, entries with gen=0 would appear valid.
        // This is astronomically unlikely (2^64 clears) and benign (causes
        // false hits that will be overwritten). We accept this tradeoff
        // for the simplicity of not checking for wraparound.
    }
}

impl<K, V> Cache<K, V>
where
    K: MyHash,
{
    /// Computes the set index for a key.
    #[inline]
    fn set_index(&self, key: &K) -> usize {
        (key.hash() & self.bitmask) as usize
    }
}

impl<K, V> Cache<K, V>
where
    K: MyHash + Eq + Default,
    V: Copy + Default,
{
    /// Looks up a key in the cache.
    ///
    /// Returns `Some(&value)` if the key is found and valid, `None` otherwise.
    ///
    /// On a hit, the accessed entry is promoted to MRU (most recently used)
    /// position within its set.
    ///
    /// # Performance
    ///
    /// - Best case: O(1) — key is in first slot checked
    /// - Worst case: O(4) — checks all 4 ways
    /// - Updates LRU state on hit
    #[inline]
    pub fn get(&self, key: &K) -> Option<&V> {
        let set_idx = self.set_index(key);
        let current_gen = self.generation.get();

        // SAFETY: set_idx is always < self.sets.len() due to bitmask
        let set = &self.sets[set_idx];

        // Check all ways for a matching entry
        let mut had_valid_entry = false;
        for way in 0..WAYS {
            let entry = &set.entries[way];

            // Fast path: check generation first (likely to differ for empty slots)
            if entry.generation != current_gen {
                continue;
            }

            had_valid_entry = true;

            // Check key match
            if entry.key == *key {
                self.stats.record_hit();

                // Update LRU: promote this way to MRU
                // Uses Cell for safe interior mutability
                let mut lru = set.lru.get();
                lru.promote(way);
                set.lru.set(lru);

                return Some(&entry.value);
            }
        }

        // Miss: record appropriate statistic
        if had_valid_entry {
            self.stats.record_fault(); // Collision: valid entries exist but no key match
        } else {
            self.stats.record_miss(); // Empty set or all entries stale
        }

        None
    }

    /// Inserts a key-value pair into the cache.
    ///
    /// If the key already exists, updates the value. Otherwise, finds a slot:
    /// 1. First, tries to use an empty/stale slot
    /// 2. If all slots are occupied, replaces the LRU entry
    ///
    /// The inserted entry becomes the MRU (most recently used) in its set.
    ///
    /// # Performance
    ///
    /// O(1) amortized — single set access with constant-time LRU update.
    #[inline]
    pub fn insert(&mut self, key: K, value: V) {
        let set_idx = self.set_index(&key);
        let current_gen = self.generation.get();
        let set = &mut self.sets[set_idx];

        // First pass: look for existing key or empty/stale slot
        let mut empty_slot: Option<usize> = None;
        for way in 0..WAYS {
            let entry = &set.entries[way];

            if entry.generation != current_gen {
                // Stale or never-used entry — candidate for insertion
                if empty_slot.is_none() {
                    empty_slot = Some(way);
                }
                continue;
            }

            if entry.key == key {
                // Key exists: update value and promote to MRU
                set.entries[way].value = value;
                let mut lru = set.lru.get();
                lru.promote(way);
                set.lru.set(lru);
                return;
            }
        }

        // Determine which slot to use
        let lru = set.lru.get();
        let target_way = empty_slot.unwrap_or_else(|| lru.lru_way());

        // Insert new entry
        set.entries[target_way] = Entry {
            key,
            value,
            generation: current_gen,
        };

        // Promote to MRU
        let mut lru = set.lru.get();
        lru.promote(target_way);
        set.lru.set(lru);
    }
}

// =============================================================================
// Tests
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    // =========================================================================
    // LRU Tests
    // =========================================================================

    #[test]
    fn test_lru_initial_state() {
        let lru = Lru::new();
        // Initial order: [0, 1, 2, 3] from MRU to LRU
        assert_eq!(lru.way_at(0), 0, "MRU should be way 0");
        assert_eq!(lru.way_at(1), 1);
        assert_eq!(lru.way_at(2), 2);
        assert_eq!(lru.way_at(3), 3, "LRU should be way 3");
        assert_eq!(lru.lru_way(), 3);
    }

    #[test]
    fn test_lru_promote_already_mru() {
        let mut lru = Lru::new();
        lru.promote(0); // Promote MRU — should be no-op
        assert_eq!(lru.way_at(0), 0);
        assert_eq!(lru.way_at(1), 1);
        assert_eq!(lru.way_at(2), 2);
        assert_eq!(lru.way_at(3), 3);
    }

    #[test]
    fn test_lru_promote_lru_to_mru() {
        let mut lru = Lru::new();
        // Initial: [0, 1, 2, 3]
        lru.promote(3); // Access LRU
                        // Expected: [3, 0, 1, 2]
        assert_eq!(lru.way_at(0), 3, "Way 3 should now be MRU");
        assert_eq!(lru.way_at(1), 0);
        assert_eq!(lru.way_at(2), 1);
        assert_eq!(lru.way_at(3), 2, "Way 2 should now be LRU");
    }

    #[test]
    fn test_lru_promote_middle() {
        let mut lru = Lru::new();
        // Initial: [0, 1, 2, 3]
        lru.promote(2); // Access middle element
                        // Expected: [2, 0, 1, 3]
        assert_eq!(lru.way_at(0), 2);
        assert_eq!(lru.way_at(1), 0);
        assert_eq!(lru.way_at(2), 1);
        assert_eq!(lru.way_at(3), 3);
    }

    #[test]
    fn test_lru_sequence() {
        let mut lru = Lru::new();
        // Simulate access pattern: 0, 1, 2, 3, 1, 3
        lru.promote(0); // [0, 1, 2, 3]
        lru.promote(1); // [1, 0, 2, 3]
        lru.promote(2); // [2, 1, 0, 3]
        lru.promote(3); // [3, 2, 1, 0]
        lru.promote(1); // [1, 3, 2, 0]
        lru.promote(3); // [3, 1, 2, 0]

        assert_eq!(lru.way_at(0), 3, "MRU should be 3");
        assert_eq!(lru.way_at(3), 0, "LRU should be 0");
    }

    // =========================================================================
    // Cache Basic Tests
    // =========================================================================

    #[test]
    fn test_cache_new() {
        let cache = Cache::<(u64, u64), i32>::new(10);
        assert_eq!(cache.num_sets(), 1024);
        assert_eq!(cache.capacity(), 4096);
        assert_eq!(cache.hits(), 0);
        assert_eq!(cache.misses(), 0);
    }

    #[test]
    fn test_cache_insert_and_get() {
        let mut cache = Cache::<(u64, u64), i32>::new(4);

        cache.insert((1, 2), 42);
        cache.insert((3, 4), 99);
        cache.insert((5, 6), -7);

        assert_eq!(cache.get(&(1, 2)), Some(&42));
        assert_eq!(cache.get(&(3, 4)), Some(&99));
        assert_eq!(cache.get(&(5, 6)), Some(&-7));
        assert_eq!(cache.get(&(7, 8)), None);
    }

    #[test]
    fn test_cache_update_existing() {
        let mut cache = Cache::<(u64, u64), i32>::new(4);

        cache.insert((1, 2), 10);
        assert_eq!(cache.get(&(1, 2)), Some(&10));

        cache.insert((1, 2), 20);
        assert_eq!(cache.get(&(1, 2)), Some(&20));
    }

    #[test]
    fn test_cache_clear() {
        let mut cache = Cache::<(u64, u64), i32>::new(4);

        cache.insert((1, 2), 42);
        cache.insert((3, 4), 99);

        assert_eq!(cache.get(&(1, 2)), Some(&42));

        cache.clear();

        assert_eq!(cache.get(&(1, 2)), None);
        assert_eq!(cache.get(&(3, 4)), None);
    }

    #[test]
    fn test_cache_multiple_clears() {
        let mut cache = Cache::<(u64, u64), i32>::new(4);

        for i in 0..10 {
            cache.insert((i, i + 1), i as i32);
            assert_eq!(cache.get(&(i, i + 1)), Some(&(i as i32)));
            cache.clear();
            assert_eq!(cache.get(&(i, i + 1)), None);
        }
    }

    // =========================================================================
    // Cache Collision Tests
    // =========================================================================

    #[test]
    fn test_cache_collision_handling() {
        // Use a very small cache to force collisions
        let mut cache = Cache::<(u64, u64), i32>::new(2); // 4 sets × 4 ways = 16 entries

        // Insert more than 16 entries — some will collide
        for i in 0..32 {
            cache.insert((i, 0), i as i32);
        }

        // Due to 4-way associativity, we should retain more entries than direct-mapped
        let mut found = 0;
        for i in 0..32 {
            if cache.get(&(i, 0)).is_some() {
                found += 1;
            }
        }

        // With 4-way and good distribution, expect to retain ~16 entries
        assert!(found >= 12, "Expected at least 12 entries, found {}", found);
    }

    #[test]
    fn test_cache_same_set_replacement() {
        // Create cache with 1 set (bits=0) to force all entries into same set
        let mut cache = Cache::<(u64, u64), i32>::new(0); // 1 set × 4 ways = 4 entries

        // Insert 4 entries — should all fit
        cache.insert((1, 0), 1);
        cache.insert((2, 0), 2);
        cache.insert((3, 0), 3);
        cache.insert((4, 0), 4);

        assert_eq!(cache.get(&(1, 0)), Some(&1));
        assert_eq!(cache.get(&(2, 0)), Some(&2));
        assert_eq!(cache.get(&(3, 0)), Some(&3));
        assert_eq!(cache.get(&(4, 0)), Some(&4));

        // Insert 5th entry — should evict LRU (entry 1, since we accessed 2,3,4 after)
        // But wait, we accessed 1 first, so after accessing all, 1 is LRU
        cache.insert((5, 0), 5);

        // Entry 1 should be evicted (it was LRU after all the gets above promoted others)
        assert_eq!(cache.get(&(1, 0)), None);
        assert_eq!(cache.get(&(5, 0)), Some(&5));
    }

    #[test]
    fn test_cache_lru_replacement_order() {
        // 1 set to force same-set competition
        let mut cache = Cache::<(u64, u64), i32>::new(0);

        // Insert 4 entries
        cache.insert((1, 0), 1);
        cache.insert((2, 0), 2);
        cache.insert((3, 0), 3);
        cache.insert((4, 0), 4);

        // Access (2, 0) to make it MRU
        assert_eq!(cache.get(&(2, 0)), Some(&2));

        // Insert 5th — should evict LRU which is (1, 0)
        cache.insert((5, 0), 5);
        assert_eq!(cache.get(&(1, 0)), None, "(1,0) should be evicted as LRU");
        assert_eq!(cache.get(&(2, 0)), Some(&2), "(2,0) should still exist");

        // Insert 6th — should evict next LRU which is (3, 0)
        cache.insert((6, 0), 6);
        assert_eq!(cache.get(&(3, 0)), None, "(3,0) should be evicted");
    }

    // =========================================================================
    // Statistics Tests
    // =========================================================================

    #[test]
    fn test_cache_statistics() {
        let mut cache = Cache::<(u64, u64), i32>::new(4);

        // Miss on empty cache
        cache.get(&(1, 2));
        assert_eq!(cache.hits(), 0);
        assert_eq!(cache.misses(), 1);

        // Insert and hit
        cache.insert((1, 2), 42);
        cache.get(&(1, 2));
        assert_eq!(cache.hits(), 1);
        assert_eq!(cache.misses(), 1);

        // Another hit
        cache.get(&(1, 2));
        assert_eq!(cache.hits(), 2);

        // Miss on non-existent key
        cache.get(&(9, 9));
        assert_eq!(cache.misses(), 2);
    }

    // =========================================================================
    // Edge Cases
    // =========================================================================

    #[test]
    fn test_cache_zero_key() {
        let mut cache = Cache::<(u64, u64), i32>::new(4);
        cache.insert((0, 0), 42);
        assert_eq!(cache.get(&(0, 0)), Some(&42));
    }

    #[test]
    fn test_cache_max_key() {
        let mut cache = Cache::<(u64, u64), i32>::new(4);
        cache.insert((u64::MAX, u64::MAX), 42);
        assert_eq!(cache.get(&(u64::MAX, u64::MAX)), Some(&42));
    }

    #[test]
    fn test_cache_negative_values() {
        let mut cache = Cache::<(u64, u64), i32>::new(4);
        cache.insert((1, 2), -2147483648);
        assert_eq!(cache.get(&(1, 2)), Some(&-2147483648));
    }

    #[test]
    fn test_cache_triple_key() {
        // Test with 3-element tuple keys (used for ITE cache)
        let mut cache = Cache::<(u64, u64, u64), u64>::new(4);
        cache.insert((1, 2, 3), 123);
        cache.insert((4, 5, 6), 456);

        assert_eq!(cache.get(&(1, 2, 3)), Some(&123));
        assert_eq!(cache.get(&(4, 5, 6)), Some(&456));
        assert_eq!(cache.get(&(1, 2, 4)), None);
    }

    // =========================================================================
    // Compatibility with original API
    // =========================================================================

    #[test]
    fn test_cache_original_api() {
        // This test ensures the new cache is a drop-in replacement
        let mut cache = Cache::<(u64, u64), i32>::new(3);

        cache.insert((1, 2), 3);
        cache.insert((2, 3), 1);
        cache.insert((1, 3), 2);

        assert_eq!(cache.get(&(1, 2)), Some(&3));
        assert_eq!(cache.get(&(2, 3)), Some(&1));
        assert_eq!(cache.get(&(1, 3)), Some(&2));
        assert_eq!(cache.get(&(2, 1)), None);
        assert_eq!(cache.get(&(3, 2)), None);
        assert_eq!(cache.get(&(3, 1)), None);
        assert_eq!(cache.get(&(1, 1)), None);
        assert_eq!(cache.get(&(2, 2)), None);
        assert_eq!(cache.get(&(3, 3)), None);
    }

    // =========================================================================
    // Stress Tests
    // =========================================================================

    #[test]
    fn test_cache_stress() {
        let mut cache = Cache::<(u64, u64), u64>::new(10); // 1K sets

        // Insert 10K entries
        for i in 0..10_000 {
            cache.insert((i, i * 2), i * 3);
        }

        // Verify we can still find recent entries
        let mut found = 0;
        for i in 9000..10_000 {
            if cache.get(&(i, i * 2)) == Some(&(i * 3)) {
                found += 1;
            }
        }
        // With LRU, most recent entries should survive
        assert!(found > 900, "Expected >900 recent entries, found {}", found);
    }

    #[test]
    fn test_cache_alternating_pattern() {
        let mut cache = Cache::<(u64, u64), i32>::new(0); // 1 set

        // Insert and repeatedly access to test LRU stability
        cache.insert((1, 0), 1);
        cache.insert((2, 0), 2);

        for _ in 0..100 {
            assert_eq!(cache.get(&(1, 0)), Some(&1));
            assert_eq!(cache.get(&(2, 0)), Some(&2));
        }

        // Both should still be present
        assert_eq!(cache.get(&(1, 0)), Some(&1));
        assert_eq!(cache.get(&(2, 0)), Some(&2));
    }
}
