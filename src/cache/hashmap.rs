//! HashMap-based cache using the standard library.
//!
//! This is the simplest cache implementation, wrapping `std::collections::HashMap`.
//! It has the highest hit rate (no collisions) but also the highest memory usage
//! and allocation overhead.
//!
//! # Use Cases
//!
//! - Debugging: compare results against other cache implementations
//! - Small problems where simplicity matters more than performance
//! - When you need guaranteed no-collision behavior
//!
//! # Trade-offs
//!
//! - **Pros**: No collisions, simple semantics, automatic resizing
//! - **Cons**: Allocation overhead, higher memory usage, slower clear()

use std::collections::HashMap;
use std::hash::Hash;

/// A cache backed by [HashMap].
///
/// This provides the simplest semantics with no collisions, at the cost
/// of higher memory usage and allocation overhead.
pub struct HashMapCache<K, V> {
    map: HashMap<K, V>,
    hits: usize,
    misses: usize,
}

impl<K, V> Default for HashMapCache<K, V> {
    fn default() -> Self {
        Self::new(14)
    }
}

impl<K, V> HashMapCache<K, V> {
    /// Creates a new HashMap-based cache.
    ///
    /// The `bits` parameter is ignored (HashMap sizes automatically),
    /// but accepted for API compatibility with other cache types.
    pub fn new(bits: usize) -> Self {
        Self {
            map: HashMap::with_capacity(1 << bits),
            hits: 0,
            misses: 0,
        }
    }

    /// Creates a new cache with pre-allocated capacity.
    pub fn with_capacity(capacity: usize) -> Self {
        Self {
            map: HashMap::with_capacity(capacity),
            hits: 0,
            misses: 0,
        }
    }

    /// Returns the number of entries in the cache.
    pub fn len(&self) -> usize {
        self.map.len()
    }

    /// Returns true if the cache is empty.
    pub fn is_empty(&self) -> bool {
        self.map.is_empty()
    }

    /// Returns the number of cache hits.
    pub fn hits(&self) -> usize {
        self.hits
    }

    /// Returns the number of cache misses.
    pub fn misses(&self) -> usize {
        self.misses
    }

    /// Returns the number of cache faults (always 0 for HashMap).
    pub fn faults(&self) -> usize {
        0 // HashMap has no collisions
    }

    /// Clears all entries from the cache.
    ///
    /// Note: This is O(n) for HashMap, unlike generation-based caches.
    pub fn clear(&mut self) {
        self.map.clear();
    }
}

impl<K, V> HashMapCache<K, V>
where
    K: Hash + Eq,
    V: Copy,
{
    /// Looks up a key in the cache.
    #[inline]
    pub fn get(&mut self, key: &K) -> Option<&V> {
        match self.map.get(key) {
            Some(v) => {
                self.hits += 1;
                Some(v)
            }
            None => {
                self.misses += 1;
                None
            }
        }
    }

    /// Inserts a key-value pair into the cache.
    #[inline]
    pub fn insert(&mut self, key: K, value: V) {
        self.map.insert(key, value);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_hashmap_cache_basic() {
        let mut cache = HashMapCache::<(u64, u64), i32>::new(4);

        cache.insert((1, 2), 42);
        cache.insert((3, 4), 99);

        assert_eq!(cache.get(&(1, 2)), Some(&42));
        assert_eq!(cache.get(&(3, 4)), Some(&99));
        assert_eq!(cache.get(&(5, 6)), None);

        assert_eq!(cache.hits(), 2);
        assert_eq!(cache.misses(), 1);
    }

    #[test]
    fn test_hashmap_cache_clear() {
        let mut cache = HashMapCache::<(u64, u64), i32>::new(4);

        cache.insert((1, 2), 42);
        assert_eq!(cache.get(&(1, 2)), Some(&42));

        cache.clear();
        assert_eq!(cache.get(&(1, 2)), None);
        assert!(cache.is_empty());
    }

    #[test]
    fn test_hashmap_cache_no_collisions() {
        let mut cache = HashMapCache::<(u64, u64), i32>::new(2);

        // Insert many entries - HashMap will grow as needed
        for i in 0..1000 {
            cache.insert((i, 0), i as i32);
        }

        // All entries should be retrievable
        for i in 0..1000 {
            assert_eq!(cache.get(&(i, 0)), Some(&(i as i32)));
        }

        assert_eq!(cache.faults(), 0);
    }
}
