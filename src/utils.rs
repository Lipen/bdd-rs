use crate::reference::Ref;

/// [Cantor pairing function][cantor-pairing].
///
/// ```text
/// (a, b) -> (a + b) * (a + b + 1) / 2 + b
/// ```
///
/// [cantor-pairing]: https://en.wikipedia.org/wiki/Pairing_function#Cantor_pairing_function
pub const fn pairing_cantor(a: u64, b: u64) -> u64 {
    (a + b) * (a + b + 1) / 2 + b
}

/// [Hopcroft and Ullman pairing function][hopcroft-pairing].
///
/// ```text
/// (a, b) -> (a + b - 2) * (a + b - 1) / 2 + a
/// ```
///
/// [hopcroft-pairing]: https://en.wikipedia.org/wiki/Pairing_function#Hopcroft_and_Ullman_pairing_function
pub const fn pairing_hopcroft(a: u64, b: u64) -> u64 {
    assert!(a > 0);
    assert!(b > 0);
    (a + b - 2) * (a + b - 1) / 2 + a
}

/// [Szudzik pairing function][szudzik-pairing].
///
/// ```text
/// (a, b) -> if (a<b) then (b^2 + a) else (a^2 + a + b)
/// ```
///
/// [szudzik-pairing]: http://szudzik.com/ElegantPairing.pdf
pub const fn pairing_szudzik(a: u64, b: u64) -> u64 {
    if a < b {
        // b * b + a
        b.wrapping_mul(b).wrapping_add(a)
    } else {
        // a * a + a + b
        a.wrapping_mul(a).wrapping_add(a).wrapping_add(b)
    }
}

/// [Pairing function][pairing] for two `u64` values.
///
/// [pairing]: https://en.wikipedia.org/wiki/Pairing_function
pub const fn pairing2(a: u64, b: u64) -> u64 {
    pairing_szudzik(a, b)
}

/// Pairing function for three `u64` values.
pub const fn pairing3(a: u64, b: u64, c: u64) -> u64 {
    pairing2(pairing2(a, b), c)
}

/// Pairing function for four `u64` values.
pub const fn pairing4(a: u64, b: u64, c: u64, d: u64) -> u64 {
    pairing2(pairing2(a, b), pairing2(c, d))
}

#[inline]
pub const fn mix64(mut x: u64) -> u64 {
    // MurmurHash3 finalizer constants
    x = x.wrapping_mul(0xff51afd7ed558ccd);
    x ^= x >> 33;
    x = x.wrapping_mul(0xc4ceb9fe1a85ec53);
    x ^= x >> 33;
    x
}

/// Fast combine for two u64s.
#[inline]
pub fn combine2(a: u64, b: u64) -> u64 {
    // Choose two large odd constants (from SplitMix/Murmur)
    const C1: u64 = 0x9e3779b97f4a7c15; // golden ratio
    const C2: u64 = 0xbf58476d1ce4e5b9; // splitmix constant

    // Multiply-and-xor combining (cheap, mixes input entropy)
    let z = a.wrapping_mul(C1) ^ b.wrapping_mul(C2);
    // Finalize to avalanche bits and remove linear artifacts
    mix64(z)
}

/// Combine three values.
#[inline]
pub fn combine3(a: u64, b: u64, c: u64) -> u64 {
    // simple tree combine, but use different constants to avoid symmetry
    const D1: u64 = 0x94d049bb133111eb;
    let z = a
        .wrapping_mul(0x9e3779b97f4a7c15)
        .wrapping_add(b.wrapping_mul(0xbf58476d1ce4e5b9))
        .wrapping_add(c.wrapping_mul(D1));
    mix64(z)
}

pub trait MyHash {
    // TODO: maybe return `u32` instead of `u64`? or `usize`?
    fn hash(&self) -> u64;
}

impl MyHash for (u64, u64) {
    fn hash(&self) -> u64 {
        combine2(self.0, self.1)
    }
}

impl MyHash for (u64, u64, u64) {
    fn hash(&self) -> u64 {
        combine3(self.0, self.1, self.2)
    }
}

impl MyHash for Ref {
    fn hash(&self) -> u64 {
        mix64(self.raw() as u64)
    }
}

impl MyHash for (Ref, Ref) {
    fn hash(&self) -> u64 {
        let x = MyHash::hash(&self.0);
        let y = MyHash::hash(&self.1);
        MyHash::hash(&(x, y))
    }
}

impl MyHash for (Ref, Ref, Ref) {
    fn hash(&self) -> u64 {
        let x = MyHash::hash(&self.0);
        let y = MyHash::hash(&self.1);
        let z = MyHash::hash(&self.2);
        MyHash::hash(&(x, y, z))
    }
}

impl MyHash for (Ref, usize) {
    fn hash(&self) -> u64 {
        let x = MyHash::hash(&self.0);
        let y = self.1 as u64;
        MyHash::hash(&(x, y))
    }
}

impl MyHash for (Ref, Ref, usize) {
    fn hash(&self) -> u64 {
        let x = MyHash::hash(&self.0);
        let y = MyHash::hash(&self.1);
        let z = self.2 as u64;
        MyHash::hash(&(x, y, z))
    }
}

#[derive(Debug, Eq, PartialEq, Clone)]
pub enum OpKey {
    Ite(Ref, Ref, Ref),
    Constrain(Ref, Ref),
    Restrict(Ref, Ref),
}

impl MyHash for OpKey {
    fn hash(&self) -> u64 {
        match *self {
            OpKey::Ite(f, g, h) => MyHash::hash(&(f, g, h)),
            OpKey::Constrain(f, g) => MyHash::hash(&(f, g)),
            OpKey::Restrict(f, g) => MyHash::hash(&(f, g)),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_cantor() {
        // a\b  0  1  2  3  4
        // ------------------
        // 0    0  2  5  9 14
        // 1    1  4  8 13
        // 2    3  7 12
        // 3    6 11
        // 4   10          40
        assert_eq!(pairing_cantor(0, 0), 0);
        assert_eq!(pairing_cantor(1, 0), 1);
        assert_eq!(pairing_cantor(0, 1), 2);
        assert_eq!(pairing_cantor(2, 0), 3);
        assert_eq!(pairing_cantor(1, 1), 4);
        assert_eq!(pairing_cantor(0, 2), 5);
        assert_eq!(pairing_cantor(4, 0), 10);
        assert_eq!(pairing_cantor(0, 4), 14);
        assert_eq!(pairing_cantor(4, 4), 40);
    }

    #[test]
    fn test_hopcroft() {
        // a\b  1  2  3  4  5
        // ------------------
        // 1    1  2  4  7 11
        // 2    3  5  8 12
        // 3    6  9 13
        // 4   10 14
        // 5   15          41
        assert_eq!(pairing_hopcroft(1, 1), 1);
        assert_eq!(pairing_hopcroft(1, 2), 2);
        assert_eq!(pairing_hopcroft(2, 1), 3);
        assert_eq!(pairing_hopcroft(1, 3), 4);
        assert_eq!(pairing_hopcroft(2, 2), 5);
        assert_eq!(pairing_hopcroft(3, 1), 6);
        assert_eq!(pairing_hopcroft(1, 5), 11);
        assert_eq!(pairing_hopcroft(5, 1), 15);
        assert_eq!(pairing_hopcroft(5, 5), 41);
    }

    #[test]
    fn test_szudzik() {
        // a\b  0  1  2  3  4
        // ------------------
        // 0    0  1  4  9 16
        // 1    2  3  5 10 17
        // 2    6  7  8 11 18
        // 3   12 13 14 15 19
        // 4   20 21 22 23 24
        assert_eq!(pairing_szudzik(0, 0), 0);
        assert_eq!(pairing_szudzik(0, 1), 1);
        assert_eq!(pairing_szudzik(1, 0), 2);
        assert_eq!(pairing_szudzik(1, 1), 3);
        assert_eq!(pairing_szudzik(0, 2), 4);
        assert_eq!(pairing_szudzik(1, 2), 5);
        assert_eq!(pairing_szudzik(2, 0), 6);
        assert_eq!(pairing_szudzik(2, 1), 7);
        assert_eq!(pairing_szudzik(2, 2), 8);
        assert_eq!(pairing_szudzik(0, 4), 16);
        assert_eq!(pairing_szudzik(4, 0), 20);
        assert_eq!(pairing_szudzik(4, 4), 24);
    }

    #[test]
    fn test_combine() {
        let a = 123456789u64;
        let b = 987654321u64;
        let c = 555555555u64;

        let h1 = combine2(a, b);
        let h2 = combine2(a, b);
        assert_eq!(h1, h2, "combine2 should be deterministic");

        let h3 = combine3(a, b, c);
        let h4 = combine3(a, b, c);
        assert_eq!(h3, h4, "combine3 should be deterministic");

        assert_ne!(h1, h3, "combine2 and combine3 should produce different hashes");
    }
}
