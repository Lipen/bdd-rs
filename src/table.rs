use std::cmp::min;
use std::ops::{Index, IndexMut};

use crate::utils::MyHash;

pub struct Table<T> {
    data: Vec<T>,
    next: Vec<usize>,
    occupied: Vec<bool>,

    buckets: Vec<usize>,
    bitmask: u64,

    /// Index of the first *possibly* free (non-occupied) cell.
    min_free: usize,
    /// Index of the last occupied cell.
    last_index: usize,
    /// Number of occupied cells.
    real_size: usize,
}

impl<T> Table<T>
where
    T: Default + Clone,
{
    /// Create a new table of size `2^bits`.
    pub fn new(bits: usize) -> Self {
        assert!(bits <= 31, "Storage bits should be in the range 0..=31");

        let capacity = 1 << bits;
        let data = vec![T::default(); capacity];
        let next = vec![0; capacity];
        let mut occupied = vec![false; capacity];
        occupied[0] = true; // Set 0th cell as occupied (sentry).

        let buckets_bits = min(bits, 16);
        let buckets_size = 1 << buckets_bits;
        let buckets = vec![0; buckets_size];
        let bitmask = (buckets_size - 1) as u64;

        Self {
            data,
            next,
            occupied,
            buckets,
            bitmask,
            min_free: 1,
            last_index: 0,
            real_size: 0,
        }
    }
}

impl<T> Table<T> {
    pub fn capacity(&self) -> usize {
        self.data.len()
    }
    pub fn size(&self) -> usize {
        self.last_index
    }
    pub fn real_size(&self) -> usize {
        self.real_size
    }

    pub fn value(&self, index: usize) -> &T {
        assert_ne!(index, 0, "Index is 0");
        &self.data[index]
    }
    pub fn value_mut(&mut self, index: usize) -> &mut T {
        assert_ne!(index, 0, "Index is 0");
        &mut self.data[index]
    }

    pub fn is_occupied(&self, index: usize) -> bool {
        assert_ne!(index, 0, "Index is 0");
        self.occupied[index]
    }
    pub fn next(&self, index: usize) -> usize {
        assert_ne!(index, 0, "Index is 0");
        self.next[index]
    }
    pub fn set_next(&mut self, index: usize, next: usize) {
        assert_ne!(index, 0, "Index is 0");
        self.next[index] = next;
    }

    pub(crate) fn alloc(&mut self) -> usize {
        let index = (self.min_free..=self.last_index)
            .find(|&i| !self.is_occupied(i))
            .unwrap_or_else(|| {
                self.last_index += 1;
                self.last_index
            });

        if index >= self.capacity() {
            panic!("Storage is full");
        }

        self.occupied[index] = true;
        self.min_free = index + 1;
        self.real_size += 1;

        index
    }

    pub fn drop(&mut self, index: usize) {
        assert_ne!(index, 0, "Index is 0");

        self.occupied[index] = false;
        self.min_free = min(self.min_free, index);
        self.real_size -= 1;
    }

    pub fn add(&mut self, value: T) -> usize {
        let index = self.alloc();

        self.data[index] = value;
        self.next[index] = 0;

        index
    }
}

impl<T> Table<T>
where
    T: MyHash,
{
    fn bucket_index(&self, value: &T) -> usize {
        (value.hash() & self.bitmask) as usize
    }

    pub fn put(&mut self, value: T) -> usize
    where
        T: Eq,
    {
        let bucket_index = self.bucket_index(&value);
        let mut index = self.buckets[bucket_index];

        if index == 0 {
            // Create new node and put it into the bucket.
            let i = self.add(value);
            self.buckets[bucket_index] = i;
            return i;
        }

        loop {
            assert!(index > 0);

            if &value == self.value(index) {
                // The node already exists.
                return index;
            }

            let next = self.next(index);

            if next == 0 {
                // Create new node and append it to the bucket.
                let i = self.add(value);
                self.set_next(index, i);
                return i;
            } else {
                // Go to the next node in the bucket.
                index = next;
            }
        }
    }
}

impl<T> Index<usize> for Table<T> {
    type Output = T;

    fn index(&self, index: usize) -> &Self::Output {
        self.value(index)
    }
}

impl<T> IndexMut<usize> for Table<T> {
    fn index_mut(&mut self, index: usize) -> &mut Self::Output {
        self.value_mut(index)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_alloc() {
        let mut storage = Table::<()>::new(2);
        assert_eq!(storage.alloc(), 1);
        assert_eq!(storage.alloc(), 2);
        assert_eq!(storage.alloc(), 3);
    }

    #[test]
    #[should_panic(expected = "Storage is full")]
    fn test_alloc_too_much() {
        let mut storage = Table::<()>::new(2);
        assert_eq!(storage.alloc(), 1);
        assert_eq!(storage.alloc(), 2);
        assert_eq!(storage.alloc(), 3);
        storage.alloc();
    }

    #[test]
    fn test_add() {
        let mut table = Table::new(2);
        let index = table.add(42);
        assert_eq!(table[index], 42);
        assert_eq!(table.next(index), 0);
    }

    #[test]
    fn test_drop() {
        let mut storage = Table::new(2);
        let index = storage.add(42);
        assert!(storage.is_occupied(index));
        storage.drop(index);
        assert!(!storage.is_occupied(index));
    }

    #[test]
    fn test_set_next() {
        let mut storage = Table::new(2);
        let index1 = storage.add(10);
        let index2 = storage.add(20);
        storage.set_next(index1, index2);
        assert_eq!(storage.next(index1), index2);
    }

    #[test]
    fn test_put() {
        #[derive(Debug, Default, Copy, Clone, Eq, PartialEq)]
        struct Item(i32);

        impl MyHash for Item {
            fn hash(&self) -> u64 {
                self.0.unsigned_abs() as u64
            }
        }

        let mut storage = Table::new(2);
        let index1 = storage.put(Item(5));
        let index2 = storage.put(Item(-5));
        assert_ne!(index1, index2);
        assert_eq!(storage[index1], Item(5));
        assert_eq!(storage[index2], Item(-5));
        assert_eq!(storage.next(index1), index2);
    }
}
