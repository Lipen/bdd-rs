use std::cmp::min;
use std::ops::{Index, IndexMut};

use crate::utils::MyHash;

#[derive(Clone)]
struct Entry<T> {
    value: T,
    next: usize,
    occupied: bool,
}

impl<T> Entry<T> {
    /// Create a new cell with the given value.
    pub fn new(value: T) -> Self {
        Self {
            value,
            next: 0,
            occupied: false,
        }
    }
}

impl<T> Default for Entry<T>
where
    T: Default,
{
    fn default() -> Self {
        Self::new(T::default())
    }
}

impl<T> Entry<T> {
    /// Get the reference to the value.
    pub fn value(&self) -> &T {
        &self.value
    }
    /// Get the mutable reference to the value.
    pub fn value_mut(&mut self) -> &mut T {
        &mut self.value
    }

    /// Get the index of the next cell.
    pub fn next(&self) -> usize {
        self.next
    }
    /// Set the index of the next cell.
    pub fn set_next(&mut self, next: usize) {
        self.next = next;
    }

    /// Check if the cell is occupied.
    pub fn occupied(&self) -> bool {
        self.occupied
    }
    /// Set the occupied flag.
    pub fn set_occupied(&mut self, occupied: bool) {
        self.occupied = occupied;
    }
}

pub struct Table<T> {
    data: Vec<Entry<T>>,

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
    T: Default,
{
    /// Create a new table of size `2^bits`.
    pub fn new(bits: usize) -> Self {
        assert!(bits <= 31, "Storage bits should be in the range 0..=31");

        let capacity = 1 << bits;
        // let mut data = vec![Entry::default(); capacity];
        let mut data: Vec<Entry<T>> = Vec::with_capacity(capacity);
        data.resize_with(capacity, Entry::default);
        data[0].set_occupied(true); // Set 0th cell as occupied (sentry).

        let buckets_bits = min(bits, 16);
        let buckets_size = 1 << buckets_bits;
        let buckets = vec![0; buckets_size];
        let bitmask = (buckets_size - 1) as u64;

        Self {
            data,
            buckets,
            bitmask,
            min_free: 1,
            last_index: 0,
            real_size: 0,
        }
    }
}

impl<T> Table<T> {
    /// Get the capacity of the table.
    pub fn capacity(&self) -> usize {
        self.data.len()
    }
    /// Get the index of the last occupied.
    pub fn size(&self) -> usize {
        self.last_index
    }
    /// Get the number of occupied cells.
    pub fn real_size(&self) -> usize {
        self.real_size
    }

    /// Get the reference to the value at the given index.
    pub fn value(&self, index: usize) -> &T {
        assert_ne!(index, 0, "Index is 0");
        self.data[index].value()
    }
    /// Get the mutable reference to the value at the given index.
    pub fn value_mut(&mut self, index: usize) -> &mut T {
        assert_ne!(index, 0, "Index is 0");
        self.data[index].value_mut()
    }

    /// Check if the cell at the given index is occupied.
    pub fn is_occupied(&self, index: usize) -> bool {
        assert_ne!(index, 0, "Index is 0");
        self.data[index].occupied()
    }
    /// Get the index of the next cell.
    pub fn next(&self, index: usize) -> usize {
        assert_ne!(index, 0, "Index is 0");
        self.data[index].next()
    }
    /// Set the index of the next cell.
    pub fn set_next(&mut self, index: usize, next: usize) {
        assert_ne!(index, 0, "Index is 0");
        self.data[index].set_next(next);
    }

    /// Allocate a new cell in the table and return its index.
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

        self.data[index].set_occupied(true);
        self.min_free = index + 1;
        self.real_size += 1;

        index
    }

    /// Drop the value at the given index.
    pub fn drop(&mut self, index: usize) {
        assert_ne!(index, 0, "Index is 0");

        self.data[index].occupied = false;
        self.min_free = min(self.min_free, index);
        self.real_size -= 1;
    }

    /// Add a new value to the table and return its index.
    pub fn add(&mut self, value: T) -> usize {
        let index = self.alloc();

        self.data[index].value = value;
        self.data[index].next = 0;

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

    /// Put a new value into the table and return its index.
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
