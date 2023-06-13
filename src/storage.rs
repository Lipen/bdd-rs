use std::cmp::min;
use std::mem::MaybeUninit;

#[derive(Clone)]
struct Entry<T>
where
    T: Copy,
{
    value: MaybeUninit<T>,
    occupied: bool,
    next: usize,
}

impl<T> Default for Entry<T>
where
    T: Copy,
{
    fn default() -> Self {
        Self {
            value: MaybeUninit::uninit(),
            occupied: false,
            next: 0,
        }
    }
}

pub struct Storage<T>
where
    T: Copy,
{
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

impl<T> Storage<T>
where
    T: Copy,
{
    pub fn new(bits: usize) -> Self {
        assert!(bits <= 31, "Storage bits should be in the range 0..=31");

        let capacity = 1 << bits;
        let mut data = vec![Entry::default(); capacity];
        data[0].occupied = true; // Set 0th cell as occupied (sentry).

        let buckets_bits = min(bits, 16);
        let buckets = vec![0; 1 << buckets_bits];
        let bitmask = 1 << buckets_bits - 1;

        Self {
            data,
            buckets,
            bitmask,
            min_free: 1,
            last_index: 0,
            real_size: 0,
        }
    }

    pub fn capacity(&self) -> usize {
        self.data.len()
    }
    pub fn size(&self) -> usize {
        self.last_index
    }
    pub fn real_size(&self) -> usize {
        self.real_size
    }

    pub fn is_occupied(&self, index: usize) -> bool {
        self.data[index].occupied
    }
    pub fn value(&self, index: usize) -> T {
        assert!(self.is_occupied(index), "Index {} is not occupied", index);
        unsafe { self.data[index].value.assume_init() }
    }
    pub fn next(&self, index: usize) -> usize {
        self.data[index].next
    }
    pub fn set_next(&mut self, index: usize, next: usize) {
        assert_ne!(index, 0, "Index is 0");

        self.data[index].next = next;
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

        self.data[index].occupied = true;
        self.min_free = index + 1;
        self.real_size += 1;

        index
    }

    pub fn add(&mut self, value: T) -> usize {
        let index = self.alloc();

        self.data[index].value = MaybeUninit::new(value);
        self.data[index].next = 0;

        index
    }

    pub fn drop(&mut self, index: usize) {
        assert_ne!(index, 0, "Index is 0");

        self.data[index].occupied = false;
        self.min_free = min(self.min_free, index);
        self.real_size -= 1;
    }
}

pub trait MyHash {
    fn hash(&self) -> u64;
}

impl<T> Storage<T>
where
    T: Copy,
{
    fn hash(&self, value: &T) -> usize
    where
        T: MyHash,
    {
        (value.hash() & self.bitmask) as usize
    }

    pub fn put(&mut self, value: T) -> usize
    where
        T: MyHash + Eq,
    {
        let bucket_index = self.hash(&value);
        let mut index = self.buckets[bucket_index];

        if index == 0 {
            // Create new node and put it into the bucket.
            let i = self.add(value);
            self.buckets[bucket_index] = i;
            return i;
        }

        loop {
            assert!(index > 0);

            if value == self.value(index) {
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_alloc() {
        let mut storage = Storage::<()>::new(2);
        assert_eq!(storage.alloc(), 1);
        assert_eq!(storage.alloc(), 2);
        assert_eq!(storage.alloc(), 3);
    }

    #[test]
    #[should_panic(expected = "Storage is full")]
    fn test_alloc_too_much() {
        let mut storage = Storage::<()>::new(2);
        assert_eq!(storage.alloc(), 1);
        assert_eq!(storage.alloc(), 2);
        assert_eq!(storage.alloc(), 3);
        storage.alloc();
    }

    #[test]
    fn test_add_and_get() {
        let mut storage = Storage::new(2);
        let index = storage.add(42);
        assert_eq!(storage.value(index), 42);
        assert_eq!(storage.next(index), 0);
    }

    #[test]
    fn test_drop() {
        let mut storage = Storage::new(2);
        let index = storage.add(42);
        assert!(storage.is_occupied(index));
        storage.drop(index);
        assert!(!storage.is_occupied(index));
    }

    #[test]
    fn test_set_next() {
        let mut storage = Storage::new(2);
        let index1 = storage.add(10);
        let index2 = storage.add(20);
        storage.set_next(index1, index2);
        assert_eq!(storage.next(index1), index2);
    }

    #[test]
    fn test_put() {
        #[derive(Debug, Copy, Clone, Eq, PartialEq)]
        struct Item(i32);

        impl MyHash for Item {
            fn hash(&self) -> u64 {
                self.0.unsigned_abs() as u64
            }
        }

        let mut storage = Storage::new(2);
        let index1 = storage.put(Item(5));
        let index2 = storage.put(Item(-5));
        assert_ne!(index1, index2);
        assert_eq!(storage.value(index1), Item(5));
        assert_eq!(storage.value(index2), Item(-5));
        assert_eq!(storage.next(index1), index2);
    }
}
