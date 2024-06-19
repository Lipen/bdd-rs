use std::cell::Cell;

use crate::utils::MyHash;

struct Entry<K, V> {
    key: K,
    value: V,
}

pub struct Cache<K, T> {
    data: Vec<Option<Entry<K, T>>>,
    bitmask: u64,
    hits: Cell<usize>,
    misses: Cell<usize>,
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
        match &self.data[index] {
            Some(entry) if &entry.key == key => {
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
    pub fn insert(&mut self, key: K, value: V) {
        let index = self.index(&key);
        self.data[index] = Some(Entry { key, value });
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
