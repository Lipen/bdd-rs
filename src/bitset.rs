//! Efficient bit set implementation for BDD node tracking.
//!
//! This module provides a simple, cache-efficient bit set that can be used
//! for tracking free slots and marking alive nodes during garbage collection.

/// A simple bit set backed by a vector of u64 words.
///
/// Each bit corresponds to a node index. The bit set automatically grows
/// as needed when setting bits beyond the current capacity.
#[derive(Debug, Clone)]
pub struct BitSet {
    /// Storage: each u64 holds 64 bits
    words: Vec<u64>,
    /// Number of set bits (cached for O(1) len())
    count: usize,
    /// Index of first word that might have a set bit (optimization for find_first)
    min_word: usize,
}

impl BitSet {
    /// Number of bits per word.
    const BITS_PER_WORD: usize = 64;

    /// Creates a new empty bit set with the given capacity (in bits).
    pub fn new(capacity: usize) -> Self {
        let num_words = (capacity + Self::BITS_PER_WORD - 1) / Self::BITS_PER_WORD;
        Self {
            words: vec![0; num_words],
            count: 0,
            min_word: usize::MAX,
        }
    }

    /// Creates an empty bit set with no pre-allocated capacity.
    pub fn empty() -> Self {
        Self {
            words: Vec::new(),
            count: 0,
            min_word: usize::MAX,
        }
    }

    /// Returns the number of set bits.
    #[inline]
    pub fn len(&self) -> usize {
        self.count
    }

    /// Returns true if no bits are set.
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.count == 0
    }

    /// Returns the capacity in bits.
    #[inline]
    pub fn capacity(&self) -> usize {
        self.words.len() * Self::BITS_PER_WORD
    }

    /// Ensures the bit set can hold at least `bits` bits.
    pub fn reserve(&mut self, bits: usize) {
        let needed_words = (bits + Self::BITS_PER_WORD - 1) / Self::BITS_PER_WORD;
        if needed_words > self.words.len() {
            self.words.resize(needed_words, 0);
        }
    }

    /// Gets the word index and bit position for a given bit index.
    #[inline]
    fn word_and_bit(index: usize) -> (usize, usize) {
        let word = index / Self::BITS_PER_WORD;
        let bit = index % Self::BITS_PER_WORD;
        (word, bit)
    }

    /// Returns true if the bit at the given index is set.
    #[inline]
    pub fn contains(&self, index: usize) -> bool {
        let (word_idx, bit_idx) = Self::word_and_bit(index);
        if word_idx >= self.words.len() {
            return false;
        }
        let mask = 1u64 << bit_idx;
        (self.words[word_idx] & mask) != 0
    }

    /// Sets the bit at the given index. Returns true if the bit was not previously set.
    #[inline]
    pub fn insert(&mut self, index: usize) -> bool {
        let (word_idx, bit_idx) = Self::word_and_bit(index);

        // Grow if necessary
        if word_idx >= self.words.len() {
            self.words.resize(word_idx + 1, 0);
        }

        let mask = 1u64 << bit_idx;
        let was_clear = (self.words[word_idx] & mask) == 0;

        if was_clear {
            self.words[word_idx] |= mask;
            self.count += 1;
            if word_idx < self.min_word {
                self.min_word = word_idx;
            }
        }

        was_clear
    }

    /// Clears the bit at the given index. Returns true if the bit was previously set.
    #[inline]
    pub fn remove(&mut self, index: usize) -> bool {
        let (word_idx, bit_idx) = Self::word_and_bit(index);

        if word_idx >= self.words.len() {
            return false;
        }

        let mask = 1u64 << bit_idx;
        let was_set = (self.words[word_idx] & mask) != 0;

        if was_set {
            self.words[word_idx] &= !mask;
            self.count -= 1;
            // Note: we don't update min_word here for performance
            // It's just a hint, not a guarantee
        }

        was_set
    }

    /// Finds and removes the first set bit. Returns its index, or None if empty.
    #[inline]
    pub fn pop_first(&mut self) -> Option<usize> {
        if self.count == 0 {
            return None;
        }

        // Start from min_word hint
        for word_idx in self.min_word..self.words.len() {
            let word = self.words[word_idx];
            if word != 0 {
                let bit_idx = word.trailing_zeros() as usize;
                let index = word_idx * Self::BITS_PER_WORD + bit_idx;

                // Clear the bit
                self.words[word_idx] &= !(1u64 << bit_idx);
                self.count -= 1;

                // Update min_word hint
                if self.words[word_idx] == 0 {
                    self.min_word = word_idx + 1;
                }

                return Some(index);
            }
            self.min_word = word_idx + 1;
        }

        // Should not reach here if count > 0
        self.count = 0;
        self.min_word = usize::MAX;
        None
    }

    /// Clears all bits.
    pub fn clear(&mut self) {
        for word in &mut self.words {
            *word = 0;
        }
        self.count = 0;
        self.min_word = usize::MAX;
    }

    /// Extends the bit set by setting all bits from an iterator.
    pub fn extend(&mut self, iter: impl IntoIterator<Item = usize>) {
        for index in iter {
            self.insert(index);
        }
    }

    /// Extends the bit set by setting all bits from an iterator of u32.
    pub fn extend_u32(&mut self, iter: impl IntoIterator<Item = u32>) {
        for index in iter {
            self.insert(index as usize);
        }
    }

    /// Returns an iterator over all set bit indices.
    pub fn iter(&self) -> BitSetIter<'_> {
        BitSetIter {
            bitset: self,
            word_idx: 0,
            current_word: self.words.first().copied().unwrap_or(0),
        }
    }
}

impl Default for BitSet {
    fn default() -> Self {
        Self::empty()
    }
}

/// Iterator over set bits in a BitSet.
pub struct BitSetIter<'a> {
    bitset: &'a BitSet,
    word_idx: usize,
    current_word: u64,
}

impl Iterator for BitSetIter<'_> {
    type Item = usize;

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            if self.current_word != 0 {
                let bit_idx = self.current_word.trailing_zeros() as usize;
                self.current_word &= self.current_word - 1; // Clear lowest set bit
                return Some(self.word_idx * BitSet::BITS_PER_WORD + bit_idx);
            }

            self.word_idx += 1;
            if self.word_idx >= self.bitset.words.len() {
                return None;
            }
            self.current_word = self.bitset.words[self.word_idx];
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_empty() {
        let bs = BitSet::empty();
        assert!(bs.is_empty());
        assert_eq!(bs.len(), 0);
        assert!(!bs.contains(0));
        assert!(!bs.contains(100));
    }

    #[test]
    fn test_insert_contains() {
        let mut bs = BitSet::new(100);
        assert!(!bs.contains(42));
        assert!(bs.insert(42));
        assert!(bs.contains(42));
        assert!(!bs.insert(42)); // Already set
        assert_eq!(bs.len(), 1);
    }

    #[test]
    fn test_remove() {
        let mut bs = BitSet::new(100);
        bs.insert(42);
        assert!(bs.remove(42));
        assert!(!bs.contains(42));
        assert!(!bs.remove(42)); // Already cleared
        assert_eq!(bs.len(), 0);
    }

    #[test]
    fn test_pop_first() {
        let mut bs = BitSet::new(100);
        bs.insert(5);
        bs.insert(10);
        bs.insert(3);

        assert_eq!(bs.pop_first(), Some(3));
        assert_eq!(bs.pop_first(), Some(5));
        assert_eq!(bs.pop_first(), Some(10));
        assert_eq!(bs.pop_first(), None);
        assert!(bs.is_empty());
    }

    #[test]
    fn test_auto_grow() {
        let mut bs = BitSet::empty();
        bs.insert(1000);
        assert!(bs.contains(1000));
        assert_eq!(bs.len(), 1);
    }

    #[test]
    fn test_iter() {
        let mut bs = BitSet::new(100);
        bs.insert(5);
        bs.insert(10);
        bs.insert(3);
        bs.insert(64); // Second word
        bs.insert(65);

        let indices: Vec<_> = bs.iter().collect();
        assert_eq!(indices, vec![3, 5, 10, 64, 65]);
    }

    #[test]
    fn test_extend() {
        let mut bs = BitSet::new(100);
        bs.extend([1, 5, 10, 20]);
        assert_eq!(bs.len(), 4);
        assert!(bs.contains(1));
        assert!(bs.contains(5));
        assert!(bs.contains(10));
        assert!(bs.contains(20));
    }

    #[test]
    fn test_clear() {
        let mut bs = BitSet::new(100);
        bs.insert(1);
        bs.insert(50);
        bs.insert(99);
        bs.clear();
        assert!(bs.is_empty());
        assert!(!bs.contains(1));
        assert!(!bs.contains(50));
        assert!(!bs.contains(99));
    }
}
