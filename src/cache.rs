use std::cell::Cell;

use crate::utils::MyHash;

/// Default cache size in bits (2^14 = 16K entries).
const DEFAULT_CACHE_BITS: usize = 14;

struct Entry<K, V> {
    key: K,
    value: V,
    generation: u64,
}

/// A hash-based cache with O(1) clearing via generation counters.
///
/// Instead of physically clearing entries, we increment a generation counter.
/// Entries are only valid if their generation matches the current one.
/// This makes `clear()` O(1) instead of O(n), which is critical for
/// performance during dynamic variable reordering where the cache is
/// invalidated frequently.
pub struct Cache<K, V> {
    data: Vec<Option<Entry<K, V>>>,
    bitmask: u64,
    generation: Cell<u64>,
    hits: Cell<usize>,   // successful lookups
    faults: Cell<usize>, // unsuccessful lookups
    misses: Cell<usize>, // total misses, including unsuccessful lookups
}

impl<K, V> Default for Cache<K, V> {
    fn default() -> Self {
        Self::new(DEFAULT_CACHE_BITS)
    }
}

impl<K, V> Cache<K, V> {
    /// Create a new cache with default size.
    pub fn with_default_size() -> Self {
        Self::default()
    }

    /// Create a new table of size `2^bits`.
    pub fn new(bits: usize) -> Self {
        assert!(bits <= 31, "Bits should be in the range 0..=31");

        let size = 1 << bits;
        let bitmask = (size - 1) as u64;

        Self {
            // data: vec![None; size],
            data: std::iter::repeat_with(|| None).take(size).collect(),
            bitmask,
            generation: Cell::new(0),
            hits: Cell::new(0),
            faults: Cell::new(0),
            misses: Cell::new(0),
        }
    }

    /// Get the number of cache hits.
    pub fn hits(&self) -> usize {
        self.hits.get()
    }
    /// Get the number of cache faults.
    pub fn faults(&self) -> usize {
        self.faults.get()
    }
    /// Get the number of cache misses.
    pub fn misses(&self) -> usize {
        self.misses.get()
    }

    /// Reset the cache.
    ///
    /// This is O(1) - we just increment the generation counter.
    /// Old entries become stale and will be treated as cache misses.
    pub fn clear(&mut self) {
        self.generation.set(self.generation.get().wrapping_add(1));
    }
}

impl<K, V> Cache<K, V>
where
    K: MyHash,
{
    fn index(&self, key: &K) -> usize {
        (key.hash() & self.bitmask) as usize
    }

    /// Get the cached result.
    pub fn get(&self, key: &K) -> Option<&V>
    where
        K: Eq,
    {
        let index = self.index(key);
        let current_gen = self.generation.get();
        match &self.data[index] {
            Some(entry) if entry.generation == current_gen => {
                if &entry.key == key {
                    self.hits.set(self.hits.get() + 1);
                    Some(&entry.value)
                } else {
                    self.faults.set(self.faults.get() + 1);
                    self.misses.set(self.misses.get() + 1);
                    None
                }
            }
            _ => {
                self.misses.set(self.misses.get() + 1);
                None
            }
        }
    }

    /// Insert a result into the cache.
    pub fn insert(&mut self, key: K, value: V) {
        let index = self.index(&key);
        let current_gen = self.generation.get();
        self.data[index] = Some(Entry {
            key,
            value,
            generation: current_gen,
        });
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_cache() {
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
}
