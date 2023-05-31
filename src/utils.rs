/// Pairing function for `u64` values.
/// https://en.wikipedia.org/wiki/Pairing_function
///
/// Cantor:
///
/// ```text
/// (a, b) -> (a + b) * (a + b + 1) / 2 + b
/// ```
///
/// Hopcroft & Ullman:
///
/// ```text
/// (a, b) -> (a + b - 2) * (a + b - 1) / 2 + a
/// ```
///
/// Currently, uses Hopcroft & Ullman variant.
pub fn pairing2(a: u64, b: u64) -> u64 {
    // Cantor:
    // assert!(a >= 0);
    // assert!(b >= 0);
    // return (a + b) * (a + b + 1) / 2 + b;

    // Hopcroft & Ullman:
    assert!(a > 0);
    assert!(b > 0);
    return (a + b - 2) * (a + b - 1) / 2 + a;
}

pub fn pairing3(a: u64, b: u64, c: u64) -> u64 {
    pairing2(pairing2(a, b), c)
}
