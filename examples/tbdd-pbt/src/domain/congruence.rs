//! Congruence abstract domain.
//!
//! Tracks modular arithmetic properties of values: `x ≡ remainder (mod modulus)`.

use super::traits::{AbstractDomain, Concretizable};

/// Greatest common divisor (Euclidean algorithm).
pub(crate) fn gcd(a: u64, b: u64) -> u64 {
    if b == 0 {
        a
    } else {
        gcd(b, a % b)
    }
}

/// Congruence abstract domain: `x ≡ remainder (mod modulus)`.
///
/// Tracks modular arithmetic properties of values. Useful for:
/// - Alignment checking (pointer alignment, SIMD requirements)
/// - Parity analysis (even/odd)
/// - Periodic pattern detection
///
/// # Representation
///
/// - `(modulus, remainder)` where `0 ≤ remainder < modulus`
/// - `modulus = 0` represents top (all values)
/// - `is_bottom = true` represents bottom (no values)
///
/// # Lattice Structure
///
/// The order is defined by divisibility:
/// - `(m₁, r₁) ⊑ (m₂, r₂)` iff `m₂ | m₁` and `r₁ ≡ r₂ (mod m₂)`
///
/// For example: `(4, 0) ⊑ (2, 0)` (multiples of 4 are multiples of 2)
///
/// # Example
///
/// ```rust
/// use tbdd_pbt::domain::{Congruence, AbstractDomain};
///
/// let even = Congruence::new(2, 0);  // x ≡ 0 (mod 2)
/// let odd = Congruence::new(2, 1);   // x ≡ 1 (mod 2)
///
/// assert!(even.contains(0));
/// assert!(even.contains(4));
/// assert!(!even.contains(3));
///
/// // Join of even and odd is top
/// assert!(even.join(&odd).is_top());
///
/// // Meet of even and odd is bottom
/// assert!(even.meet(&odd).is_bottom());
/// ```
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Congruence {
    /// The modulus (`0` means any value — top).
    modulus: u64,
    /// The remainder (`0 ≤ remainder < modulus`, or `0` if top).
    remainder: u64,
    /// Whether this is bottom (empty set).
    is_bottom: bool,
}

impl Congruence {
    /// Create a congruence `x ≡ r (mod m)`.
    ///
    /// The remainder is normalized to `[0, m)`.
    pub fn new(modulus: u64, remainder: u64) -> Self {
        let remainder = if modulus > 0 { remainder % modulus } else { 0 };
        Self {
            modulus,
            remainder,
            is_bottom: false,
        }
    }

    /// Create alignment constraint `x ≡ 0 (mod m)`.
    pub fn aligned(modulus: u64) -> Self {
        Self::new(modulus, 0)
    }

    /// Create even number constraint `x ≡ 0 (mod 2)`.
    pub fn even() -> Self {
        Self::new(2, 0)
    }

    /// Create odd number constraint `x ≡ 1 (mod 2)`.
    pub fn odd() -> Self {
        Self::new(2, 1)
    }

    /// Check if a value satisfies this congruence.
    pub fn contains(&self, value: i64) -> bool {
        if self.is_bottom {
            return false;
        }
        if self.modulus == 0 {
            return true; // Top contains everything
        }
        let v = value.unsigned_abs();
        v % self.modulus == self.remainder
    }

    /// Get the modulus.
    pub fn modulus(&self) -> u64 {
        self.modulus
    }

    /// Get the remainder.
    pub fn remainder(&self) -> u64 {
        self.remainder
    }
}

impl AbstractDomain for Congruence {
    fn bottom() -> Self {
        Self {
            modulus: 0,
            remainder: 0,
            is_bottom: true,
        }
    }

    fn top() -> Self {
        Self {
            modulus: 0,
            remainder: 0,
            is_bottom: false,
        }
    }

    fn is_bottom(&self) -> bool {
        self.is_bottom
    }

    fn is_top(&self) -> bool {
        !self.is_bottom && self.modulus == 0
    }

    fn join(&self, other: &Self) -> Self {
        if self.is_bottom {
            return other.clone();
        }
        if other.is_bottom {
            return self.clone();
        }
        if self.modulus == 0 || other.modulus == 0 {
            return Self::top();
        }

        // GCD of moduli gives the common periodicity
        let new_mod = gcd(self.modulus, other.modulus);

        // Check if remainders are compatible mod gcd
        if self.remainder % new_mod != other.remainder % new_mod {
            return Self::top();
        }

        Self::new(new_mod, self.remainder % new_mod)
    }

    fn meet(&self, other: &Self) -> Self {
        if self.is_bottom || other.is_bottom {
            return Self::bottom();
        }
        if self.modulus == 0 {
            return other.clone();
        }
        if other.modulus == 0 {
            return self.clone();
        }

        // Check compatibility using Chinese Remainder Theorem
        let g = gcd(self.modulus, other.modulus);

        if self.remainder % g != other.remainder % g {
            return Self::bottom(); // No solution exists
        }

        // LCM gives the combined periodicity
        let new_mod = self.modulus / g * other.modulus;

        // For simplicity, use one of the remainders (full CRT would compute exact value)
        Self::new(new_mod, self.remainder % new_mod)
    }

    fn widen(&self, other: &Self) -> Self {
        // Congruence domain has finite height for practical moduli
        self.join(other)
    }

    fn narrow(&self, other: &Self) -> Self {
        self.meet(other)
    }

    fn leq(&self, other: &Self) -> bool {
        if self.is_bottom {
            return true;
        }
        if other.is_bottom {
            return false;
        }
        if other.modulus == 0 {
            return true; // Everything ⊑ ⊤
        }
        if self.modulus == 0 {
            return false; // ⊤ ⊑ x only if x = ⊤
        }

        // self ⊑ other iff other.modulus | self.modulus and remainders match
        self.modulus % other.modulus == 0 && self.remainder % other.modulus == other.remainder
    }
}

impl Concretizable for Congruence {
    fn concretize(&self) -> Option<i64> {
        if self.is_bottom {
            None
        } else {
            Some(self.remainder as i64)
        }
    }

    fn sample(&self, count: usize) -> Vec<i64> {
        if self.is_bottom {
            return Vec::new();
        }
        if self.modulus == 0 {
            // Top: return diverse samples
            return vec![0, 1, -1].into_iter().take(count).collect();
        }

        (0..count).map(|i| (self.remainder + i as u64 * self.modulus) as i64).collect()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_congruence_basic() {
        let even = Congruence::new(2, 0);
        let odd = Congruence::new(2, 1);

        assert!(even.contains(0));
        assert!(even.contains(2));
        assert!(!even.contains(1));

        assert!(odd.contains(1));
        assert!(!odd.contains(2));

        // Join of even and odd is top (all integers)
        let joined = even.join(&odd);
        assert!(joined.is_top());

        // Meet of even and odd is bottom
        let met = even.meet(&odd);
        assert!(met.is_bottom());
    }
}
