use std::cell::Cell;
use std::marker::PhantomData;

use crate::reference::Ref;
use crate::utils::{pairing2, pairing3, MyHash};

struct Entry<K, V> {
    key: K,
    value: V,
}

pub struct Cache<K, T> {
    data: Vec<Option<Entry<u64, T>>>,
    bitmask: u64,
    hits: Cell<usize>,
    misses: Cell<usize>,
    _phantom: PhantomData<K>,
}

impl<K, V> Cache<K, V> {
    /// Create a new table of size `2^bits`.
    pub fn new(bits: usize) -> Self {
        assert!(bits <= 31, "Bits should be in the range 0..=31");

        let size = 1 << bits;
        let bitmask = (size - 1) as u64;

        Self {
            // data: vec![None; size],
            data: std::iter::repeat_with(|| None).take(size).collect(),
            bitmask,
            hits: Cell::new(0),
            misses: Cell::new(0),
            _phantom: PhantomData,
        }
    }

    /// Get the number of cache hits.
    pub fn hits(&self) -> usize {
        self.hits.get()
    }
    /// Get the number of cache misses.
    pub fn misses(&self) -> usize {
        self.misses.get()
    }

    /// Reset the cache.
    pub fn clear(&mut self) {
        self.data.fill_with(|| None);
    }

    fn index(&self, key: u64) -> usize {
        (key & self.bitmask) as usize
    }

    /// Get the cached result.
    pub fn get(&mut self, key: &K) -> Option<&V>
    where
        K: MyHash,
    {
        let key = key.hash();
        let index = self.index(key);
        match &self.data[index] {
            Some(entry) if entry.key == key => {
                self.hits.set(self.hits.get() + 1);
                Some(&entry.value)
            }
            _ => {
                self.misses.set(self.misses.get() + 1);
                None
            }
        }
    }

    /// Insert a result into the cache.
    pub fn insert(&mut self, key: &K, value: V)
    where
        K: MyHash,
    {
        let k = key.hash();
        let index = self.index(k);
        self.data[index] = Some(Entry { key: k, value });
    }
}

impl MyHash for Ref {
    fn hash(&self) -> u64 {
        self.inner() as u64
    }
}

impl MyHash for (Ref, Ref) {
    fn hash(&self) -> u64 {
        pairing2(self.0.inner() as u64, self.1.inner() as u64)
    }
}

impl MyHash for (Ref, Ref, Ref) {
    fn hash(&self) -> u64 {
        pairing3(
            self.0.inner() as u64,
            self.1.inner() as u64,
            self.2.inner() as u64,
        )
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_cache() {
        let mut cache = Cache::<(u64, u64), i32>::new(3);

        cache.insert(&(1, 2), 3);
        cache.insert(&(2, 3), 1);
        cache.insert(&(1, 3), 2);

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
