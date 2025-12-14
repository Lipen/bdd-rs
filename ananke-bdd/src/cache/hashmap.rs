//! HashMap-based cache using the standard library.
//!
//! This is the simplest cache implementation, wrapping `hashbrown::HashMap`.
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

use std::cell::Cell;
use std::hash::{BuildHasherDefault, Hash, Hasher};

use hashbrown::HashMap;

use crate::utils::MyHash;

// =============================================================================
// MyHash to std::hash::Hash adapter
// =============================================================================

/// A hasher that uses `MyHash::hash()` to produce hash values.
///
/// This bridges `MyHash` (used by other cache implementations) with
/// `std::hash::Hash` (required by `HashMap`), allowing `HashMapCache`
/// to use the same key types as other caches.
#[derive(Default)]
pub struct MyHasher {
    hash: u64,
}

impl Hasher for MyHasher {
    #[inline]
    fn finish(&self) -> u64 {
        self.hash
    }

    #[inline]
    fn write(&mut self, _bytes: &[u8]) {
        // Not used - we only use write_u64
        unreachable!("MyHasher only supports write_u64")
    }

    #[inline]
    fn write_u64(&mut self, i: u64) {
        self.hash = i;
    }
}

/// Wrapper that implements `std::hash::Hash` for any `MyHash` type.
///
/// This allows using `MyHash` types as keys in `HashMap`.
#[derive(Clone, PartialEq, Eq)]
#[repr(transparent)]
struct HashableKey<K>(K);

impl<K: MyHash> Hash for HashableKey<K> {
    #[inline]
    fn hash<H: Hasher>(&self, state: &mut H) {
        state.write_u64(self.0.hash());
    }
}

// =============================================================================
// HashMapCache
// =============================================================================

/// A cache backed by [HashMap].
///
/// This provides the simplest semantics with no collisions, at the cost
/// of higher memory usage and allocation overhead.
///
/// Uses `MyHash` for hashing (same as other cache implementations),
/// making it a drop-in replacement for debugging or comparison.
pub struct HashMapCache<K, V> {
    map: HashMap<HashableKey<K>, V, BuildHasherDefault<MyHasher>>,
    hits: Cell<usize>,
    misses: Cell<usize>,
}

impl<K, V> Default for HashMapCache<K, V> {
    fn default() -> Self {
        Self::new(14)
    }
}

impl<K, V> HashMapCache<K, V> {
    /// Creates a new HashMap-based cache.
    ///
    /// The `bits` parameter is used to pre-allocate capacity (2^bits entries),
    /// matching the behavior of other cache types.
    pub fn new(bits: usize) -> Self {
        Self {
            map: HashMap::with_capacity_and_hasher(1 << bits, BuildHasherDefault::default()),
            hits: Cell::new(0),
            misses: Cell::new(0),
        }
    }

    /// Creates a new cache with pre-allocated capacity.
    pub fn with_capacity(capacity: usize) -> Self {
        Self {
            map: HashMap::with_capacity_and_hasher(capacity, BuildHasherDefault::default()),
            hits: Cell::new(0),
            misses: Cell::new(0),
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
        self.hits.get()
    }

    /// Returns the number of cache misses.
    pub fn misses(&self) -> usize {
        self.misses.get()
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
    K: MyHash + Eq,
{
    /// Looks up a key in the cache.
    ///
    /// Uses `raw_entry` API to avoid cloning the key.
    #[inline]
    pub fn get(&self, key: &K) -> Option<&V> {
        let hash = key.hash();
        match self.map.raw_entry().from_hash(hash, |k| k.0 == *key).map(|(_, v)| v) {
            Some(v) => {
                self.hits.set(self.hits.get() + 1);
                Some(v)
            }
            None => {
                self.misses.set(self.misses.get() + 1);
                None
            }
        }
    }

    /// Inserts a key-value pair into the cache.
    #[inline]
    pub fn insert(&mut self, key: K, value: V) {
        let hash = key.hash();
        self.map
            .raw_entry_mut()
            .from_hash(hash, |k| k.0 == key)
            .insert(HashableKey(key), value);
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
