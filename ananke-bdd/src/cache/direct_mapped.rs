//! Direct-mapped cache with generation-based O(1) clearing.
//!
//! This cache improves on [`BasicCache`](super::BasicCache) by using generation
//! counters instead of zeroing memory on clear. This makes `clear()` O(1),
//! which is critical for BDD variable reordering.
//!
//! # Characteristics
//!
//! - **O(1) lookup and insert**: Single array access
//! - **O(1) clear**: Just increment generation counter
//! - **High collision rate**: Single slot per hash bucket
//! - **Sentinel-based**: No `Option` wrapper, uses generation=0 as invalid
//!
//! # Use Cases
//!
//! - When O(1) clear is important but you don't need high hit rates
//! - Good balance of simplicity and performance
//! - Default choice before upgrading to set-associative

use std::cell::Cell;
use std::marker::PhantomData;

use crate::utils::MyHash;

/// Default cache size in bits. 2^14 = 16K entries.
const DEFAULT_CACHE_BITS: usize = 14;

/// A single cache entry with generation stamp.
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
            generation: 0, // Invalid
        }
    }
}

/// A direct-mapped cache with O(1) clearing via generation counters.
///
/// Each key hashes to exactly one slot. When an entry is inserted, it's
/// stamped with the current generation. On lookup, entries with mismatched
/// generations are treated as empty.
///
/// # Example
///
/// ```ignore
/// use ananke_bdd::cache::DirectMappedCache;
///
/// let mut cache = DirectMappedCache::<(u64, u64), i32>::new(14);
///
/// cache.insert((1, 2), 42);
/// assert_eq!(cache.get(&(1, 2)), Some(&42));
///
/// // O(1) clear
/// cache.clear();
/// assert_eq!(cache.get(&(1, 2)), None);
/// ```
pub struct DirectMappedCache<K, V> {
    entries: Vec<Entry<K, V>>,
    bitmask: u64,
    generation: Cell<u64>,
    hits: Cell<usize>,
    misses: Cell<usize>,
    faults: Cell<usize>,
    _key: PhantomData<K>,
}

impl<K: Default, V: Default> Default for DirectMappedCache<K, V> {
    fn default() -> Self {
        Self::new(DEFAULT_CACHE_BITS)
    }
}

impl<K, V> DirectMappedCache<K, V>
where
    K: Default,
    V: Default,
{
    /// Creates a new cache with `2^bits` slots.
    pub fn new(bits: usize) -> Self {
        assert!(bits <= 31, "Cache bits must be in range 0..=31, got {}", bits);

        let size = 1usize << bits;
        let bitmask = (size - 1) as u64;

        Self {
            entries: (0..size).map(|_| Entry::default()).collect(),
            bitmask,
            generation: Cell::new(1), // Start at 1 so default entries are invalid
            hits: Cell::new(0),
            misses: Cell::new(0),
            faults: Cell::new(0),
            _key: PhantomData,
        }
    }

    /// Creates a new cache with default size.
    pub fn with_default_size() -> Self {
        Self::default()
    }

    /// Returns the number of slots in the cache.
    pub fn capacity(&self) -> usize {
        self.entries.len()
    }

    /// Returns the number of cache hits.
    pub fn hits(&self) -> usize {
        self.hits.get()
    }

    /// Returns the number of cache misses.
    pub fn misses(&self) -> usize {
        self.misses.get()
    }

    /// Returns the number of cache faults (collision misses).
    pub fn faults(&self) -> usize {
        self.faults.get()
    }

    /// Clears the cache in O(1) time.
    ///
    /// This increments the generation counter, making all existing entries stale.
    pub fn clear(&mut self) {
        self.generation.set(self.generation.get().wrapping_add(1));
    }
}

impl<K: MyHash, V> DirectMappedCache<K, V> {
    #[inline]
    fn index(&self, key: &K) -> usize {
        (key.hash() & self.bitmask) as usize
    }
}

impl<K, V> DirectMappedCache<K, V>
where
    K: MyHash + Eq,
{
    /// Looks up a key in the cache.
    #[inline]
    pub fn get(&self, key: &K) -> Option<&V> {
        let idx = self.index(key);
        let current_gen = self.generation.get();
        let entry = &self.entries[idx];

        if entry.generation != current_gen {
            // Stale or never-used entry
            self.misses.set(self.misses.get() + 1);
            return None;
        }

        if entry.key == *key {
            self.hits.set(self.hits.get() + 1);
            Some(&entry.value)
        } else {
            // Collision: slot occupied by different key
            self.misses.set(self.misses.get() + 1);
            self.faults.set(self.faults.get() + 1);
            None
        }
    }

    /// Inserts a key-value pair into the cache.
    #[inline]
    pub fn insert(&mut self, key: K, value: V) {
        let idx = self.index(&key);
        let current_gen = self.generation.get();

        self.entries[idx] = Entry {
            key,
            value,
            generation: current_gen,
        };
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_direct_mapped_insert_get() {
        let mut cache = DirectMappedCache::<(u64, u64), i32>::new(4);

        cache.insert((1, 2), 42);
        cache.insert((3, 4), 99);

        assert_eq!(cache.get(&(1, 2)), Some(&42));
        assert_eq!(cache.get(&(3, 4)), Some(&99));
        assert_eq!(cache.get(&(5, 6)), None);
    }

    #[test]
    fn test_direct_mapped_overwrite() {
        let mut cache = DirectMappedCache::<(u64, u64), i32>::new(4);

        cache.insert((1, 2), 10);
        assert_eq!(cache.get(&(1, 2)), Some(&10));

        cache.insert((1, 2), 20);
        assert_eq!(cache.get(&(1, 2)), Some(&20));
    }

    #[test]
    fn test_direct_mapped_clear_o1() {
        let mut cache = DirectMappedCache::<(u64, u64), i32>::new(4);

        cache.insert((1, 2), 42);
        cache.insert((3, 4), 99);

        assert_eq!(cache.get(&(1, 2)), Some(&42));

        cache.clear(); // O(1)

        assert_eq!(cache.get(&(1, 2)), None);
        assert_eq!(cache.get(&(3, 4)), None);
    }

    #[test]
    fn test_direct_mapped_multiple_clears() {
        let mut cache = DirectMappedCache::<(u64, u64), i32>::new(4);

        for i in 0..10 {
            cache.insert((i, i + 1), i as i32);
            assert_eq!(cache.get(&(i, i + 1)), Some(&(i as i32)));
            cache.clear();
            assert_eq!(cache.get(&(i, i + 1)), None);
        }
    }

    #[test]
    fn test_direct_mapped_collision() {
        // Very small cache to force collisions
        let mut cache = DirectMappedCache::<(u64, u64), i32>::new(2); // 4 slots

        for i in 0..16 {
            cache.insert((i, 0), i as i32);
        }

        // Only ~4 entries survive
        let mut found = 0;
        for i in 0..16 {
            if cache.get(&(i, 0)).is_some() {
                found += 1;
            }
        }
        assert!(found <= 4);
    }

    #[test]
    fn test_direct_mapped_statistics() {
        let mut cache = DirectMappedCache::<(u64, u64), i32>::new(4);

        cache.get(&(1, 2)); // Miss
        assert_eq!(cache.misses(), 1);
        assert_eq!(cache.hits(), 0);

        cache.insert((1, 2), 42);
        cache.get(&(1, 2)); // Hit
        assert_eq!(cache.hits(), 1);
    }

    #[test]
    fn test_direct_mapped_zero_key() {
        let mut cache = DirectMappedCache::<(u64, u64), i32>::new(4);
        cache.insert((0, 0), 42);
        assert_eq!(cache.get(&(0, 0)), Some(&42));
    }

    #[test]
    fn test_direct_mapped_max_key() {
        let mut cache = DirectMappedCache::<(u64, u64), i32>::new(4);
        cache.insert((u64::MAX, u64::MAX), 42);
        assert_eq!(cache.get(&(u64::MAX, u64::MAX)), Some(&42));
    }
}
