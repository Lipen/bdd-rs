//! 4-way set-associative cache with LRU replacement.
//!
//! This is the highest-performance cache implementation, providing:
//! - **4-way associativity**: ~90% fewer collisions than direct-mapped
//! - **LRU replacement**: Keeps hot entries in cache
//! - **O(1) clearing**: Generation counters instead of zeroing memory
//! - **Compact LRU**: 8 bits encode full 4-way order
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
//! # Use Cases
//!
//! - Production BDD workloads with high collision rates
//! - When cache hit rate is critical for performance
//! - Variable reordering (benefits from O(1) clear)

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
    /// - `pos=0`: bits `[1:0]` — shift by 0
    /// - `pos=1`: bits `[3:2]` — shift by 2
    /// - `pos=2`: bits `[5:4]` — shift by 4
    /// - `pos=3`: bits `[7:6]` — shift by 6
    ///
    /// Formula: `(self.0 >> (pos * 2)) & 0b11`
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

    /// Precomputed masks for head extraction (positions before `pos`).
    const HEAD_MASKS: [u8; WAYS] = {
        let mut masks = [0; WAYS];
        let mut pos = 1;
        while pos < WAYS {
            masks[pos] = (1u8 << (pos * 2)) - 1;
            pos += 1;
        }
        masks
    };

    /// Precomputed masks for tail extraction (positions after `pos`).
    const TAIL_MASKS: [u8; WAYS] = {
        let mut masks = [0; WAYS];
        let mut pos = 0;
        while pos < WAYS - 1 {
            let tail_shift = (pos + 1) * 2;
            masks[pos] = 0xFFu8.unbounded_shl(tail_shift as u32);
            pos += 1;
        }
        masks
    };

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

        // Mask for the head (positions before `pos`):
        let head_mask = Self::HEAD_MASKS[pos];

        // Mask for the tail (positions after `pos`):
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
#[derive(Clone)]
struct Entry<K, V> {
    key: K,
    value: V,
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
struct CacheSet<K, V> {
    entries: [Entry<K, V>; WAYS],
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
#[derive(Debug, Default)]
struct Stats {
    hits: Cell<usize>,
    misses: Cell<usize>,
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
/// use bdd_rs::cache::SetAssociativeCache;
///
/// // Create a cache with 2^14 = 16K sets (64K total entries)
/// let mut cache = SetAssociativeCache::<(u64, u64), i32>::new(14);
///
/// // Insert and lookup
/// cache.insert((1, 2), 42);
/// assert_eq!(cache.get(&(1, 2)), Some(&42));
///
/// // Clear is O(1)
/// cache.clear();
/// assert_eq!(cache.get(&(1, 2)), None);
/// ```
pub struct SetAssociativeCache<K, V> {
    sets: Vec<CacheSet<K, V>>,
    bitmask: u64,
    generation: Cell<u64>,
    stats: Stats,
    _key: PhantomData<K>,
}

impl<K: Default, V: Default> Default for SetAssociativeCache<K, V> {
    fn default() -> Self {
        Self::new(DEFAULT_CACHE_BITS)
    }
}

impl<K, V> SetAssociativeCache<K, V>
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

        let sets: Vec<CacheSet<K, V>> = std::iter::repeat_with(CacheSet::new).take(num_sets).collect();

        Self {
            sets,
            bitmask,
            generation: Cell::new(1),
            stats: Stats::new(),
            _key: PhantomData,
        }
    }

    /// Returns the number of sets in the cache.
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

    /// Returns the number of cache misses since creation.
    pub fn misses(&self) -> usize {
        self.stats.misses.get()
    }

    /// Returns the number of cache faults (collision misses).
    pub fn faults(&self) -> usize {
        self.stats.faults.get()
    }

    /// Clears the cache in O(1) time.
    pub fn clear(&mut self) {
        self.generation.set(self.generation.get().wrapping_add(1));
    }
}

impl<K, V> SetAssociativeCache<K, V>
where
    K: MyHash,
{
    #[inline]
    fn set_index(&self, key: &K) -> usize {
        (key.hash() & self.bitmask) as usize
    }
}

impl<K, V> SetAssociativeCache<K, V>
where
    K: MyHash + Eq,
{
    /// Looks up a key in the cache.
    ///
    /// Returns `Some(&value)` if found, `None` otherwise.
    /// On hit, the entry is promoted to MRU position.
    #[inline]
    pub fn get(&self, key: &K) -> Option<&V> {
        let set_idx = self.set_index(key);
        let current_gen = self.generation.get();
        let set = &self.sets[set_idx];

        let mut had_valid_entry = false;
        for way in 0..WAYS {
            let entry = &set.entries[way];

            if entry.generation != current_gen {
                continue;
            }

            had_valid_entry = true;

            if entry.key == *key {
                self.stats.record_hit();

                let mut lru = set.lru.get();
                lru.promote(way);
                set.lru.set(lru);

                return Some(&entry.value);
            }
        }

        if had_valid_entry {
            self.stats.record_fault();
        } else {
            self.stats.record_miss();
        }

        None
    }

    /// Inserts a key-value pair into the cache.
    ///
    /// If the key exists, updates the value. Otherwise, uses an empty slot
    /// or replaces the LRU entry.
    #[inline]
    pub fn insert(&mut self, key: K, value: V) {
        let set_idx = self.set_index(&key);
        let current_gen = self.generation.get();
        let set = &mut self.sets[set_idx];

        let mut empty_slot: Option<usize> = None;
        for way in 0..WAYS {
            let entry = &set.entries[way];

            if entry.generation != current_gen {
                if empty_slot.is_none() {
                    empty_slot = Some(way);
                }
                continue;
            }

            if entry.key == key {
                set.entries[way].value = value;
                let mut lru = set.lru.get();
                lru.promote(way);
                set.lru.set(lru);
                return;
            }
        }

        let lru = set.lru.get();
        let target_way = empty_slot.unwrap_or_else(|| lru.lru_way());

        set.entries[target_way] = Entry {
            key,
            value,
            generation: current_gen,
        };

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
        assert_eq!(lru.way_at(0), 0, "MRU should be way 0");
        assert_eq!(lru.way_at(1), 1);
        assert_eq!(lru.way_at(2), 2);
        assert_eq!(lru.way_at(3), 3, "LRU should be way 3");
        assert_eq!(lru.lru_way(), 3);
    }

    #[test]
    fn test_lru_promote_already_mru() {
        let mut lru = Lru::new();
        lru.promote(0);
        assert_eq!(lru.way_at(0), 0);
        assert_eq!(lru.way_at(1), 1);
        assert_eq!(lru.way_at(2), 2);
        assert_eq!(lru.way_at(3), 3);
    }

    #[test]
    fn test_lru_promote_lru_to_mru() {
        let mut lru = Lru::new();
        lru.promote(3);
        assert_eq!(lru.way_at(0), 3, "Way 3 should now be MRU");
        assert_eq!(lru.way_at(1), 0);
        assert_eq!(lru.way_at(2), 1);
        assert_eq!(lru.way_at(3), 2, "Way 2 should now be LRU");
    }

    #[test]
    fn test_lru_promote_middle() {
        let mut lru = Lru::new();
        lru.promote(2);
        assert_eq!(lru.way_at(0), 2);
        assert_eq!(lru.way_at(1), 0);
        assert_eq!(lru.way_at(2), 1);
        assert_eq!(lru.way_at(3), 3);
    }

    #[test]
    fn test_lru_sequence() {
        let mut lru = Lru::new();
        lru.promote(0);
        lru.promote(1);
        lru.promote(2);
        lru.promote(3);
        lru.promote(1);
        lru.promote(3);

        assert_eq!(lru.way_at(0), 3, "MRU should be 3");
        assert_eq!(lru.way_at(3), 0, "LRU should be 0");
    }

    // =========================================================================
    // Cache Basic Tests
    // =========================================================================

    #[test]
    fn test_cache_new() {
        let cache = SetAssociativeCache::<(u64, u64), i32>::new(10);
        assert_eq!(cache.num_sets(), 1024);
        assert_eq!(cache.capacity(), 4096);
        assert_eq!(cache.hits(), 0);
        assert_eq!(cache.misses(), 0);
    }

    #[test]
    fn test_cache_insert_and_get() {
        let mut cache = SetAssociativeCache::<(u64, u64), i32>::new(4);

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
        let mut cache = SetAssociativeCache::<(u64, u64), i32>::new(4);

        cache.insert((1, 2), 10);
        assert_eq!(cache.get(&(1, 2)), Some(&10));

        cache.insert((1, 2), 20);
        assert_eq!(cache.get(&(1, 2)), Some(&20));
    }

    #[test]
    fn test_cache_clear() {
        let mut cache = SetAssociativeCache::<(u64, u64), i32>::new(4);

        cache.insert((1, 2), 42);
        cache.insert((3, 4), 99);

        assert_eq!(cache.get(&(1, 2)), Some(&42));

        cache.clear();

        assert_eq!(cache.get(&(1, 2)), None);
        assert_eq!(cache.get(&(3, 4)), None);
    }

    #[test]
    fn test_cache_multiple_clears() {
        let mut cache = SetAssociativeCache::<(u64, u64), i32>::new(4);

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
        let mut cache = SetAssociativeCache::<(u64, u64), i32>::new(2);

        for i in 0..32 {
            cache.insert((i, 0), i as i32);
        }

        let mut found = 0;
        for i in 0..32 {
            if cache.get(&(i, 0)).is_some() {
                found += 1;
            }
        }

        assert!(found >= 12, "Expected at least 12 entries, found {}", found);
    }

    #[test]
    fn test_cache_same_set_replacement() {
        let mut cache = SetAssociativeCache::<(u64, u64), i32>::new(0);

        cache.insert((1, 0), 1);
        cache.insert((2, 0), 2);
        cache.insert((3, 0), 3);
        cache.insert((4, 0), 4);

        assert_eq!(cache.get(&(1, 0)), Some(&1));
        assert_eq!(cache.get(&(2, 0)), Some(&2));
        assert_eq!(cache.get(&(3, 0)), Some(&3));
        assert_eq!(cache.get(&(4, 0)), Some(&4));

        cache.insert((5, 0), 5);

        assert_eq!(cache.get(&(1, 0)), None);
        assert_eq!(cache.get(&(5, 0)), Some(&5));
    }

    #[test]
    fn test_cache_lru_replacement_order() {
        let mut cache = SetAssociativeCache::<(u64, u64), i32>::new(0);

        cache.insert((1, 0), 1);
        cache.insert((2, 0), 2);
        cache.insert((3, 0), 3);
        cache.insert((4, 0), 4);

        assert_eq!(cache.get(&(2, 0)), Some(&2));

        cache.insert((5, 0), 5);
        assert_eq!(cache.get(&(1, 0)), None, "(1,0) should be evicted as LRU");
        assert_eq!(cache.get(&(2, 0)), Some(&2), "(2,0) should still exist");

        cache.insert((6, 0), 6);
        assert_eq!(cache.get(&(3, 0)), None, "(3,0) should be evicted");
    }

    // =========================================================================
    // Statistics Tests
    // =========================================================================

    #[test]
    fn test_cache_statistics() {
        let mut cache = SetAssociativeCache::<(u64, u64), i32>::new(4);

        cache.get(&(1, 2));
        assert_eq!(cache.hits(), 0);
        assert_eq!(cache.misses(), 1);

        cache.insert((1, 2), 42);
        cache.get(&(1, 2));
        assert_eq!(cache.hits(), 1);
        assert_eq!(cache.misses(), 1);

        cache.get(&(1, 2));
        assert_eq!(cache.hits(), 2);

        cache.get(&(9, 9));
        assert_eq!(cache.misses(), 2);
    }

    // =========================================================================
    // Edge Cases
    // =========================================================================

    #[test]
    fn test_cache_zero_key() {
        let mut cache = SetAssociativeCache::<(u64, u64), i32>::new(4);
        cache.insert((0, 0), 42);
        assert_eq!(cache.get(&(0, 0)), Some(&42));
    }

    #[test]
    fn test_cache_max_key() {
        let mut cache = SetAssociativeCache::<(u64, u64), i32>::new(4);
        cache.insert((u64::MAX, u64::MAX), 42);
        assert_eq!(cache.get(&(u64::MAX, u64::MAX)), Some(&42));
    }

    #[test]
    fn test_cache_negative_values() {
        let mut cache = SetAssociativeCache::<(u64, u64), i32>::new(4);
        cache.insert((1, 2), -2147483648);
        assert_eq!(cache.get(&(1, 2)), Some(&-2147483648));
    }

    #[test]
    fn test_cache_triple_key() {
        let mut cache = SetAssociativeCache::<(u64, u64, u64), u64>::new(4);
        cache.insert((1, 2, 3), 123);
        cache.insert((4, 5, 6), 456);

        assert_eq!(cache.get(&(1, 2, 3)), Some(&123));
        assert_eq!(cache.get(&(4, 5, 6)), Some(&456));
        assert_eq!(cache.get(&(1, 2, 4)), None);
    }

    // =========================================================================
    // Stress Tests
    // =========================================================================

    #[test]
    fn test_cache_stress() {
        let mut cache = SetAssociativeCache::<(u64, u64), u64>::new(10);

        for i in 0..10_000 {
            cache.insert((i, i * 2), i * 3);
        }

        let mut found = 0;
        for i in 9000..10_000 {
            if cache.get(&(i, i * 2)) == Some(&(i * 3)) {
                found += 1;
            }
        }
        assert!(found > 900, "Expected >900 recent entries, found {}", found);
    }

    #[test]
    fn test_cache_alternating_pattern() {
        let mut cache = SetAssociativeCache::<(u64, u64), i32>::new(0);

        cache.insert((1, 0), 1);
        cache.insert((2, 0), 2);

        for _ in 0..100 {
            assert_eq!(cache.get(&(1, 0)), Some(&1));
            assert_eq!(cache.get(&(2, 0)), Some(&2));
        }

        assert_eq!(cache.get(&(1, 0)), Some(&1));
        assert_eq!(cache.get(&(2, 0)), Some(&2));
    }
}
