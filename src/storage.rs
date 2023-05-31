use std::cmp::min;
use std::ops::{Index, IndexMut};

#[derive(Clone)]
pub struct Item {
    occupied: bool,
    variable: u32,
    low: i32,
    high: i32,
    next: usize,
}

impl Default for Item {
    fn default() -> Self {
        Self {
            occupied: false,
            variable: 0,
            low: 0,
            high: 0,
            next: 0,
        }
    }
}

pub struct Storage {
    data: Vec<Item>,
    /// Index of the first *possibly* free (non-occupied) cell.
    min_free: usize,
    /// Index of the last occupied cell.
    last_index: usize,
    /// Number of occupied cells.
    real_size: usize,
}

impl Storage {
    pub fn new(capacity: usize) -> Self {
        let mut storage = Storage {
            data: vec![Item::default(); capacity],
            min_free: 1,
            last_index: 0,
            real_size: 0,
        };
        storage.data[0].occupied = true; // Set 0th cell as occupied (sentry)
        storage
    }

    pub fn item(&self, index: usize) -> &Item {
        &self.data[index]
    }

    pub fn item_mut(&mut self, index: usize) -> &mut Item {
        &mut self.data[index]
    }

    pub fn is_occupied(&self, index: usize) -> bool {
        self.item(index).occupied
    }

    pub fn variable(&self, index: usize) -> u32 {
        self.item(index).variable
    }

    pub fn low(&self, index: usize) -> i32 {
        self.item(index).low
    }

    pub fn high(&self, index: usize) -> i32 {
        self.item(index).high
    }

    pub fn next(&self, index: usize) -> usize {
        self.item(index).next
    }

    pub(crate) fn alloc(&mut self) -> usize {
        let index = (self.min_free..=self.last_index)
            .find(|&i| !self.is_occupied(i))
            .unwrap_or_else(|| {
                self.last_index += 1;
                self.last_index
            });

        self.min_free = index + 1;
        self.real_size += 1;
        self[index].occupied = true;

        index
    }

    pub fn add(&mut self, v: u32, low: i32, high: i32) -> usize {
        assert_ne!(v, 0);
        assert_ne!(low, 0);
        assert_ne!(high, 0);

        let index = self.alloc();
        self[index].variable = v;
        self[index].low = low;
        self[index].high = high;
        self[index].next = 0;

        index
    }

    pub fn drop(&mut self, index: usize) {
        assert_ne!(index, 0);

        self.real_size -= 1;
        self[index].occupied = false;
        self.min_free = min(self.min_free, index);
    }

    pub fn set_next(&mut self, index: usize, next: usize) {
        assert_ne!(index, 0);

        self[index].next = next;
    }
}

impl Index<usize> for Storage {
    type Output = Item;

    fn index(&self, index: usize) -> &Self::Output {
        self.item(index)
    }
}

impl IndexMut<usize> for Storage {
    fn index_mut(&mut self, index: usize) -> &mut Self::Output {
        self.item_mut(index)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_alloc() {
        let mut storage = Storage::new(5);
        assert_eq!(storage.alloc(), 1);
        assert_eq!(storage.alloc(), 2);
        assert_eq!(storage.alloc(), 3);
        assert_eq!(storage.alloc(), 4);
    }

    #[test]
    #[should_panic(expected = "index out of bounds: the len is 5 but the index is 5")]
    fn test_alloc_too_much() {
        let mut storage = Storage::new(5);
        assert_eq!(storage.alloc(), 1);
        assert_eq!(storage.alloc(), 2);
        assert_eq!(storage.alloc(), 3);
        assert_eq!(storage.alloc(), 4);
        storage.alloc();
    }

    #[test]
    fn test_add_and_access() {
        let mut storage = Storage::new(5);
        let index = storage.add(1, 2, 3);
        assert_eq!(storage.variable(index), 1);
        assert_eq!(storage.low(index), 2);
        assert_eq!(storage.high(index), 3);
        assert_eq!(storage.next(index), 0);
    }

    #[test]
    fn test_drop() {
        let mut storage = Storage::new(5);
        let index = storage.add(1, 2, 3);
        assert!(storage.is_occupied(index));
        storage.drop(index);
        assert!(!storage.is_occupied(index));
    }

    #[test]
    fn test_set_next() {
        let mut storage = Storage::new(5);
        let index1 = storage.add(1, 2, 3);
        let index2 = storage.add(4, 5, 6);
        storage.set_next(index1, index2);
        assert_eq!(storage.next(index1), index2);
    }
}
