use std::borrow::Borrow;
use std::cell::Cell;
use std::fmt::Debug;

use log::debug;

use crate::reference::Ref;
use crate::utils::{pairing2, pairing3, MyHash};

struct Table<T> {
    keys: Vec<u64>,
    data: Vec<T>,
    bitmask: u64,
    hits: Cell<usize>,
    misses: Cell<usize>,
}

impl<T> Table<T>
where
    T: Default + Clone,
{
    /// Create a new table of size `2^bits`.
    pub fn new(bits: usize) -> Self {
        assert!(bits <= 31, "Bits should be in the range 0..=31");

        let size = 1 << bits;
        let bitmask = (size - 1) as u64;

        Self {
            keys: vec![0; size],
            data: vec![Default::default(); size],
            bitmask,
            hits: Cell::new(0),
            misses: Cell::new(0),
        }
    }
}

impl<T> Table<T> {
    /// Get the number of cache hits.
    pub fn hits(&self) -> usize {
        self.hits.get()
    }

    /// Get the number of cache misses.
    pub fn misses(&self) -> usize {
        self.misses.get()
    }

    pub fn clear(&mut self) {
        self.keys.fill(0);
    }

    fn index(&self, key: u64) -> usize {
        assert_ne!(key, 0, "Key should not be zero");
        (key & self.bitmask) as usize
    }

    pub fn get(&self, key: u64) -> Option<&T> {
        let index = self.index(key);
        if self.keys[index] != key {
            self.misses.set(self.misses.get() + 1);
            None
        } else {
            self.hits.set(self.hits.get() + 1);
            Some(&self.data[index])
        }
    }

    pub fn insert(&mut self, key: u64, value: T) {
        let index = self.index(key);
        self.keys[index] = key;
        self.data[index] = value;
    }
}

pub struct OpCache<K, V> {
    table: Table<i32>,
    _phantom: std::marker::PhantomData<(K, V)>,
}

impl<K, V> OpCache<K, V> {
    /// Create a new cache of size `2^bits`.
    pub fn new(bits: usize) -> Self {
        Self {
            table: Table::new(bits),
            _phantom: std::marker::PhantomData,
        }
    }

    /// Get the number of cache hits.
    pub fn hits(&self) -> usize {
        self.table.hits()
    }

    /// Get the number of cache misses.
    pub fn misses(&self) -> usize {
        self.table.misses()
    }

    /// Reset the cache.
    pub fn clear(&mut self) {
        self.table.clear();
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

impl<K> OpCache<K, Ref> {
    /// Get the cached result.
    pub fn get<Q>(&mut self, key: &Q) -> Option<Ref>
    where
        K: Borrow<Q>,
        Q: MyHash,
    {
        let k = key.borrow().hash();
        self.table.get(k).copied().map(Ref::new)
    }

    /// Insert a result into the cache.
    pub fn insert(&mut self, key: K, value: Ref)
    where
        K: MyHash + Debug,
    {
        let k = key.hash();
        debug!("caching {} for key = {:?}, k = {}", value, key, k);
        self.table.insert(k, value.get());
    }
}

impl<K> OpCache<K, i32> {
    /// Get the cached result.
    pub fn get<Q>(&mut self, key: &Q) -> Option<i32>
    where
        K: Borrow<Q>,
        Q: MyHash,
    {
        let k = key.borrow().hash();
        self.table.get(k).copied()
    }

    /// Insert a result into the cache.
    pub fn insert(&mut self, key: K, value: i32)
    where
        K: MyHash + Debug,
    {
        let k = key.hash();
        debug!("caching {} for key = {:?}, k = {}", value, key, k);
        self.table.insert(k, value);
    }
}
