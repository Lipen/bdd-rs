/// [Hopcroft and Ullman pairing function][hopcroft-pairing].
///
/// ```text
/// (a, b) -> (a + b - 2) * (a + b - 1) / 2 + a
/// ```
///
/// [hopcroft-pairing]: https://en.wikipedia.org/wiki/Pairing_function#Hopcroft_and_Ullman_pairing_function
pub fn pairing_hopcroft(a: u64, b: u64) -> u64 {
    assert!(a > 0);
    assert!(b > 0);
    (a + b - 2) * (a + b - 1) / 2 + a
}

/// [Cantor pairing function][cantor-pairing].
///
/// ```text
/// (a, b) -> (a + b) * (a + b + 1) / 2 + b
/// ```
///
/// [cantor-pairing]: https://en.wikipedia.org/wiki/Pairing_function#Cantor_pairing_function
pub fn pairing_cantor(a: u64, b: u64) -> u64 {
    (a + b) * (a + b + 1) / 2 + b
}

/// [Pairing function][pairing] for two `u64` values.
///
/// Currently, we use Hopcroft & Ullman variant.
///
/// [pairing]: https://en.wikipedia.org/wiki/Pairing_function
pub fn pairing2(a: u64, b: u64) -> u64 {
    pairing_hopcroft(a, b)
}

/// Pairing function for three `u64` values.
pub fn pairing3(a: u64, b: u64, c: u64) -> u64 {
    pairing2(pairing2(a, b), c)
}

pub trait MyHash {
    // TODO: maybe return `u32` instead of `u64`? or `usize`?
    /// Perfect hash function.
    fn hash(&self) -> u64;
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_cantor() {
        // a\b  0  1  2  3  4  5
        // ----------------------
        // 0    0  2  5  9 14 20
        // 1    1  4  8 13 19
        // 2    3  7 12 18
        // 3    6 11 17
        // 4   10 16
        // 5   15
        assert_eq!(pairing_cantor(0, 0), 0);
        assert_eq!(pairing_cantor(1, 0), 1);
        assert_eq!(pairing_cantor(0, 1), 2);
        assert_eq!(pairing_cantor(2, 0), 3);
        assert_eq!(pairing_cantor(1, 1), 4);
        assert_eq!(pairing_cantor(0, 2), 5);
        assert_eq!(pairing_cantor(5, 0), 15);
        assert_eq!(pairing_cantor(0, 5), 20);
    }

    #[test]
    fn test_hopcroft() {
        // a\b  1  2  3  4  5
        // ------------------
        // 1    1  2  4  7 11
        // 2    3  5  8 12
        // 3    6  9 13
        // 4   10 14
        // 5   15
        assert_eq!(pairing_hopcroft(1, 1), 1);
        assert_eq!(pairing_hopcroft(1, 2), 2);
        assert_eq!(pairing_hopcroft(2, 1), 3);
        assert_eq!(pairing_hopcroft(1, 3), 4);
        assert_eq!(pairing_hopcroft(2, 2), 5);
        assert_eq!(pairing_hopcroft(3, 1), 6);
        assert_eq!(pairing_hopcroft(1, 5), 11);
        assert_eq!(pairing_hopcroft(5, 1), 15);
    }
}
