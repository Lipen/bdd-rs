use std::mem::MaybeUninit;

const FREE: u64 = u64::MAX;
const DEAD: u64 = u64::MAX - 1;

#[derive(Debug)]
struct Slot<T> {
    status: u64,
    value: MaybeUninit<T>,
}

impl<T> Slot<T> {
    const FREE: Self = Slot {
        status: FREE,
        value: MaybeUninit::uninit(),
    };

    pub fn is_occupied(&self) -> bool {
        self.status <= (u64::MAX >> 1)
    }
}

pub struct RawTable<T> {
    data: Box<[Slot<T>]>,
    len: usize,
    free: usize,
}

impl<T> RawTable<T> {
    pub fn new() -> Self {
        RawTable {
            data: Box::new([]),
            len: 0,
            free: 0,
        }
    }
}

impl<T> RawTable<T> {
    pub fn reserve(&mut self, additional: usize) {
        if self.free < additional {
            self.reserve_rehash(additional);
        }
    }

    fn reserve_rehash(&mut self, additional: usize) {
        let new_capacity = (self.len + additional).next_power_of_two();
        let mut new_data = Vec::with_capacity(new_capacity);
        new_data.resize_with(new_capacity, || Slot::FREE);

        // let old_data = std::mem::replace(&mut self.data, unsafe { MaybeUninit::uninit().assume_init() });
        let old_data = std::mem::replace(&mut self.data, Box::new([]));
        let new_mask = new_capacity - 1;
        for slot in old_data {
            if slot.is_occupied() {
                let hash = slot.status;
                let mut index = (hash as usize) & new_mask;
                loop {
                    let new_slot = unsafe { new_data.get_unchecked_mut(index) };
                    if new_slot.status == FREE {
                        new_slot.status = hash;
                        new_slot.value = slot.value;
                        break;
                    }
                    index = (index + 1) & new_mask;
                }
            }
        }

        self.data = new_data.into_boxed_slice();
        self.free = new_capacity - self.len;
    }

    pub fn clear(&mut self) {
        if self.len == 0 {
            return;
        }
        for slot in self.data.iter_mut() {
            let occupied = slot.is_occupied();
            slot.status = FREE;
            if occupied {
                unsafe { slot.value.assume_init_drop(); }
                self.len -= 1;
                if self.len == 0 {
                    return;
                }
            }
        }
        unreachable!()
    }

    pub fn find(&self, hash: u64, eq: impl Fn(&T) -> bool) -> Option<usize> {
        debug_assert_ne!(self.free, 0);

        if self.len == 0 {
            return None;
        }

        debug_assert!(self.data.len().is_power_of_two());
        let mask = self.data.len() - 1;
        let mut index = (hash as usize) & mask;
        let status = hash & (u64::MAX >> 1); // clear MSB

        loop {
            let slot = unsafe { self.data.get_unchecked(index) };
            if slot.status == FREE {
                return None;
            }
            if slot.status == status {
                if eq(unsafe { slot.value.assume_init_ref() }) {
                    return Some(index);
                }
            }
            // linear probing
            index = (index + 1) & mask;
        }
    }

    pub fn find_or_free(&mut self, hash: u64, eq: impl Fn(&T) -> bool) -> Result<usize, usize> {
        self.reserve(1);

        debug_assert!(self.data.len().is_power_of_two());
        let mask = self.data.len() - 1;
        let mut index = (hash as usize) & mask;
        let mut first_dead = None;
        let status = hash & (u64::MAX >> 1); // clear MSB

        loop {
            let slot = unsafe { self.data.get_unchecked(index) };
            if slot.status == FREE {
                return Err(first_dead.unwrap_or(index));
            }
            if slot.status == DEAD {
                first_dead = Some(index);
            }
            if slot.status == status {
                if eq(unsafe { slot.value.assume_init_ref() }) {
                    return Ok(index);
                }
            }
            // linear probing
            index = (index + 1) & mask;
        }
    }

    pub fn get(&self, hash: u64, eq: impl Fn(&T) -> bool) -> Option<&T> {
        let index = self.find(hash, eq)?;
        Some(unsafe { self.get_at_slot(index) })
    }

    pub fn get_mut(&mut self, hash: u64, eq: impl Fn(&T) -> bool) -> Option<&mut T> {
        let index = self.find(hash, eq)?;
        Some(unsafe { self.get_at_slot_mut(index) })
    }

    pub unsafe fn get_at_slot(&self, slot: usize) -> &T {
        debug_assert!(self.data[slot].is_occupied());
        unsafe { self.data.get_unchecked(slot).value.assume_init_ref() }
    }

    pub unsafe fn get_at_slot_mut(&mut self, slot: usize) -> &mut T {
        debug_assert!(self.data[slot].is_occupied());
        unsafe { self.data.get_unchecked_mut(slot).value.assume_init_mut() }
    }

    pub fn insert(&mut self, hash: u64, eq: impl Fn(&T) -> bool, value: T) -> Result<usize, usize> {
        match self.find_or_free(hash, eq) {
            Ok(slot) => {
                unsafe { self.insert_in_slot(hash, slot, value) };
                Ok(slot)
            }
            Err(slot) => {
                unsafe { self.insert_in_slot(hash, slot, value) };
                Err(slot)
            }
        }
    }

    pub unsafe fn insert_in_slot(&mut self, hash: u64, slot: usize, value: T) -> &mut T {
        debug_assert!(!self.data[slot].is_occupied());

        let slot = unsafe { self.data.get_unchecked_mut(slot) };
        if slot.status != DEAD {
            debug_assert!(slot.status == FREE);
            self.free -= 1;
        }
        self.len += 1;
        let res = slot.value.write(value);
        slot.status = hash & (u64::MAX >> 1);
        res
    }

    pub fn remove(&mut self, hash: u64, eq: impl Fn(&T) -> bool) -> Option<T> {
        let index = self.find(hash, eq)?;
        Some(unsafe { self.remove_at_slot(index) })
    }

    pub unsafe fn remove_at_slot(&mut self, slot: usize) -> T {
        debug_assert_ne!(self.len, 0);
        debug_assert!(self.data[slot].is_occupied());
        let next_slot_index = (slot + 1) & (self.data.len() - 1);
        let next_slot_status = unsafe { self.data.get_unchecked(next_slot_index) }.status;
        let slot = unsafe { self.data.get_unchecked_mut(slot) };
        slot.status = if next_slot_status == FREE {
            self.free += 1;
            FREE
        } else {
            DEAD
        };
        self.len -= 1;
        unsafe { slot.value.assume_init_read() }
    }

    pub fn iter(&self) -> Iter<'_, T> {
        Iter {
            iter: self.data.iter(),
            len: self.len,
        }
    }
}

pub struct Iter<'a, T> {
    iter: std::slice::Iter<'a, Slot<T>>,
    len: usize,
}

impl<'a, T> Iterator for Iter<'a, T> {
    type Item = &'a T;

    fn next(&mut self) -> Option<Self::Item> {
        if self.len == 0 {
            return None;
        }
        loop {
            let next = self.iter.next();
            debug_assert!(next.is_some());
            let slot = unsafe { next.unwrap_unchecked() };
            if slot.is_occupied() {
                self.len -= 1;
                return Some(unsafe { slot.value.assume_init_ref() });
            }
        }
    }
}

impl<'a, T> ExactSizeIterator for Iter<'a, T> {
    fn len(&self) -> usize {
        self.len
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_new() {
        let table = RawTable::<u32>::new();
        assert_eq!(table.data.len(), 0);
        assert_eq!(table.len, 0);
    }

    #[test]
    fn test_insert_get() {
        let mut table = RawTable::<u32>::new();
        let numbers = [1, 4, 0, 5, 14, 4];
        let sorted = [0, 1, 4, 5, 14];

        for number in numbers {
            match table.find_or_free(number as u64, |&x| x == number) {
                Ok(_) => assert_eq!(number, 4),
                Err(slot) => unsafe {
                    table.insert_in_slot(number as u64, slot, number);
                },
            }
        }
        assert_eq!(table.len, 5);
        assert!(table.data.len() >= 5);

        for mut number in numbers {
            assert_eq!(table.get(number as u64, |&x| x == number), Some(&number));
            assert_eq!(table.get_mut(number as u64, |&x| x == number), Some(&mut number));
        }

        let iter = table.iter();
        assert_eq!(iter.len(), 5);
        let mut res: Vec<u32> = iter.copied().collect();
        res.sort();
        assert_eq!(res, sorted);
    }

    #[test]
    fn test_clear() {
        let mut table = RawTable::<u32>::new();
        let numbers = [1, 2, 3];
        for &number in &numbers {
            match table.find_or_free(number as u64, |&x| x == number) {
                Ok(_) => {}
                Err(slot) => unsafe {
                    table.insert_in_slot(number as u64, slot, number);
                },
            }
        }
        assert_eq!(table.len, 3);

        table.clear();
        assert_eq!(table.len, 0);
        assert!(table.iter().next().is_none());
    }

    #[test]
    fn test_remove() {
        let mut table = RawTable::<u32>::new();
        let numbers = [1, 2, 3];
        for &number in &numbers {
            match table.find_or_free(number as u64, |&x| x == number) {
                Ok(_) => {}
                Err(slot) => unsafe {
                    table.insert_in_slot(number as u64, slot, number);
                },
            }
        }
        assert_eq!(table.len, 3);

        assert_eq!(table.remove(2, |&x| x == 2), Some(2));
        assert_eq!(table.len, 2);
        assert_eq!(table.get(2, |&x| x == 2), None);
    }

    #[test]
    fn test_reserve() {
        let mut table = RawTable::<u32>::new();
        table.reserve(10);
        assert!(table.data.len() >= 10);
        assert_eq!(table.len, 0);
        assert_eq!(table.free, table.data.len());
    }

    #[test]
    fn test_find() {
        let mut table = RawTable::<u32>::new();
        let numbers = [1, 2, 3];
        for &number in &numbers {
            match table.find_or_free(number as u64, |&x| x == number) {
                Ok(_) => {}
                Err(slot) => unsafe {
                    table.insert_in_slot(number as u64, slot, number);
                },
            }
        }

        let slot_2 = table.find(2, |&x| x == 2);
        assert!(slot_2.is_some());
        assert_eq!(unsafe { *table.get_at_slot(slot_2.unwrap()) }, 2);
        let slot_4 = table.find(4, |&x| x == 4);
        assert!(slot_4.is_none());
    }

    #[test]
    fn test_find_or_free() {
        let mut table = RawTable::<u32>::new();
        let numbers = [1, 2, 3];
        for &number in &numbers {
            match table.find_or_free(number as u64, |&x| x == number) {
                Ok(_) => {}
                Err(slot) => unsafe {
                    table.insert_in_slot(number as u64, slot, number);
                },
            }
        }

        let res_2 = table.find_or_free(2, |&x| x == 2);
        assert!(res_2.is_ok());
        assert_eq!(unsafe { *table.get_at_slot(res_2.unwrap()) }, 2);

        let res_4 = table.find_or_free(4, |&x| x == 4);
        assert!(res_4.is_err());
    }

    #[test]
    fn test_get_at_slot() {
        let mut table = RawTable::<u32>::new();
        let numbers = [1, 2, 3];
        for &number in numbers.iter() {
            let slot = match table.find_or_free(number as u64, |&x| x == number) {
                Ok(slot) => slot,
                Err(slot) => unsafe {
                    table.insert_in_slot(number as u64, slot, number);
                    slot
                },
            };
            unsafe {
                assert_eq!(*table.get_at_slot(slot), number);
            }
        }
    }

    #[test]
    fn test_get_at_slot_mut() {
        let mut table = RawTable::<u32>::new();
        let numbers = [1, 2, 3];
        for &number in &numbers {
            match table.find_or_free(number as u64, |&x| x == number) {
                Ok(_) => {}
                Err(slot) => unsafe {
                    table.insert_in_slot(number as u64, slot, number);
                },
            }
        }

        unsafe {
            let value = table.get_at_slot_mut(1);
            *value = 42;
            assert_eq!(*table.get_at_slot(1), 42);
        }
    }

    #[test]
    fn test_iter() {
        let mut table = RawTable::<u32>::new();
        let numbers = [1, 2, 3];
        for &number in &numbers {
            match table.find_or_free(number as u64, |&x| x == number) {
                Ok(_) => {}
                Err(slot) => unsafe {
                    table.insert_in_slot(number as u64, slot, number);
                },
            }
        }

        let iter = table.iter();
        assert_eq!(iter.len(), 3);
        let mut result: Vec<u32> = iter.copied().collect();
        result.sort();
        assert_eq!(result, numbers);
    }

    #[test]
    fn test_iter_empty() {
        let table = RawTable::<u32>::new();
        let mut iter = table.iter();
        assert_eq!(iter.len(), 0);
        assert!(iter.next().is_none());
    }
}
