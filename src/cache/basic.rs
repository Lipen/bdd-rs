//! Basic direct-mapped cache with minimal overhead.
//!
//! This is the simplest fixed-size cache: a plain array where each key
//! hashes to exactly one slot. Collisions simply overwrite the previous entry.
//!
//! # Characteristics
//!
//! - **O(1) lookup and insert**: Single array access
//! - **No generation counters**: Clear is O(n)
//! - **High collision rate**: Single slot per hash bucket
//! - **Minimal memory overhead**: Just key + value + validity flag
//!
//! # Use Cases
//!
//! - When you need the absolute simplest implementation
//! - Short-lived caches that are rarely cleared
//! - Educational purposes / reference implementation

use crate::utils::MyHash;

/// A basic direct-mapped cache.
///
/// Each key hashes to exactly one slot. Collisions overwrite.
/// This is the simplest possible cache design.
pub struct BasicCache<K, V> {
    entries: Vec<Option<(K, V)>>,
    bitmask: u64,
    hits: usize,
    misses: usize,
    faults: usize,
}

impl<K, V> Default for BasicCache<K, V> {
    fn default() -> Self {
        Self::new(14)
    }
}

impl<K, V> BasicCache<K, V> {
    /// Creates a new cache with `2^bits` slots.
    pub fn new(bits: usize) -> Self {
        assert!(bits <= 31, "Cache bits must be in range 0..=31, got {}", bits);

        let size = 1usize << bits;
        let bitmask = (size - 1) as u64;

        Self {
            entries: (0..size).map(|_| None).collect(),
            bitmask,
            hits: 0,
            misses: 0,
            faults: 0,
        }
    }

    /// Returns the number of slots in the cache.
    pub fn capacity(&self) -> usize {
        self.entries.len()
    }

    /// Returns the number of cache hits.
    pub fn hits(&self) -> usize {
        self.hits
    }

    /// Returns the number of cache misses.
    pub fn misses(&self) -> usize {
        self.misses
    }

    /// Returns the number of cache faults (collision misses).
    pub fn faults(&self) -> usize {
        self.faults
    }

    /// Clears all entries. This is O(n).
    pub fn clear(&mut self) {
        for entry in &mut self.entries {
            *entry = None;
        }
    }
}

impl<K: MyHash, V> BasicCache<K, V> {
    #[inline]
    fn index(&self, key: &K) -> usize {
        (key.hash() & self.bitmask) as usize
    }
}

impl<K, V> BasicCache<K, V>
where
    K: MyHash + Eq,
    V: Copy,
{
    /// Looks up a key in the cache.
    #[inline]
    pub fn get(&mut self, key: &K) -> Option<&V> {
        let idx = self.index(key);

        match &self.entries[idx] {
            Some((k, v)) if k == key => {
                self.hits += 1;
                Some(v)
            }
            Some(_) => {
                // Slot occupied by different key
                self.faults += 1;
                self.misses += 1;
                None
            }
            None => {
                self.misses += 1;
                None
            }
        }
    }

    /// Inserts a key-value pair, overwriting any existing entry at the same slot.
    #[inline]
    pub fn insert(&mut self, key: K, value: V) {
        let idx = self.index(&key);
        self.entries[idx] = Some((key, value));
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_basic_cache_insert_get() {
        let mut cache = BasicCache::<(u64, u64), i32>::new(4);

        cache.insert((1, 2), 42);
        cache.insert((3, 4), 99);

        assert_eq!(cache.get(&(1, 2)), Some(&42));
        assert_eq!(cache.get(&(3, 4)), Some(&99));
        assert_eq!(cache.get(&(5, 6)), None);
    }

    #[test]
    fn test_basic_cache_overwrite() {
        let mut cache = BasicCache::<(u64, u64), i32>::new(4);

        cache.insert((1, 2), 10);
        assert_eq!(cache.get(&(1, 2)), Some(&10));

        cache.insert((1, 2), 20);
        assert_eq!(cache.get(&(1, 2)), Some(&20));
    }

    #[test]
    fn test_basic_cache_clear() {
        let mut cache = BasicCache::<(u64, u64), i32>::new(4);

        cache.insert((1, 2), 42);
        assert_eq!(cache.get(&(1, 2)), Some(&42));

        cache.clear();
        assert_eq!(cache.get(&(1, 2)), None);
    }

    #[test]
    fn test_basic_cache_collision() {
        // Very small cache to force collisions
        let mut cache = BasicCache::<(u64, u64), i32>::new(2); // 4 slots

        // Insert many entries - most will collide
        for i in 0..16 {
            cache.insert((i, 0), i as i32);
        }

        // Only ~4 entries survive (one per slot)
        let mut found = 0;
        for i in 0..16 {
            if cache.get(&(i, 0)).is_some() {
                found += 1;
            }
        }
        assert!(found <= 4);
    }

    #[test]
    fn test_basic_cache_statistics() {
        let mut cache = BasicCache::<(u64, u64), i32>::new(4);

        cache.get(&(1, 2)); // Miss
        assert_eq!(cache.misses(), 1);
        assert_eq!(cache.hits(), 0);

        cache.insert((1, 2), 42);
        cache.get(&(1, 2)); // Hit
        assert_eq!(cache.hits(), 1);
    }
}
