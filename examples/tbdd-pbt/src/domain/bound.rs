//! Bounds for interval endpoints.
//!
//! The [`Bound`] type represents interval endpoints that can be finite
//! or infinite, enabling proper handling of unbounded intervals.

use std::cmp::Ordering;
use std::fmt;

/// Bound for interval endpoints: finite values or infinities.
///
/// Used by [`Interval`](super::Interval) to represent endpoints that may be unbounded.
/// Supports arithmetic operations that correctly handle infinite values.
///
/// # Ordering
///
/// The total order is: `-∞ < finite values < +∞`.
///
/// # Arithmetic
///
/// Infinite arithmetic follows standard conventions:
/// - `∞ + finite = ∞`
/// - `-∞ + finite = -∞`
/// - `∞ + (-∞)` is undefined; we return `+∞` (over-approximation for soundness)
///
/// # Example
///
/// ```rust
/// use tbdd_pbt::domain::Bound;
///
/// let finite = Bound::Finite(42);
/// let neg_inf = Bound::NegInf;
/// let pos_inf = Bound::PosInf;
///
/// // Ordering
/// assert!(neg_inf < finite);
/// assert!(finite < pos_inf);
///
/// // Arithmetic
/// assert_eq!(finite.add(Bound::Finite(8)), Bound::Finite(50));
/// assert_eq!(pos_inf.add(finite), Bound::PosInf);
/// ```
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Bound {
    /// Negative infinity (`-∞`).
    NegInf,
    /// Finite integer value.
    Finite(i64),
    /// Positive infinity (`+∞`).
    PosInf,
}

impl Bound {
    /// Extract finite value, if any.
    pub fn as_finite(self) -> Option<i64> {
        match self {
            Bound::Finite(n) => Some(n),
            _ => None,
        }
    }

    /// Check if this bound is finite.
    pub fn is_finite(self) -> bool {
        matches!(self, Bound::Finite(_))
    }

    /// Addition of bounds.
    ///
    /// Handles infinite arithmetic: `∞ + finite = ∞`, etc.
    /// Note: `∞ + (-∞)` is undefined; we return `+∞` (over-approximation).
    pub fn add(self, other: Bound) -> Bound {
        match (self, other) {
            (Bound::Finite(a), Bound::Finite(b)) => Bound::Finite(a.saturating_add(b)),
            (Bound::NegInf, Bound::PosInf) | (Bound::PosInf, Bound::NegInf) => Bound::PosInf,
            (Bound::NegInf, _) | (_, Bound::NegInf) => Bound::NegInf,
            (Bound::PosInf, _) | (_, Bound::PosInf) => Bound::PosInf,
        }
    }

    /// Subtraction of bounds.
    pub fn sub(self, other: Bound) -> Bound {
        match (self, other) {
            (Bound::Finite(a), Bound::Finite(b)) => Bound::Finite(a.saturating_sub(b)),
            (Bound::PosInf, Bound::NegInf) => Bound::PosInf,
            (Bound::NegInf, Bound::PosInf) => Bound::NegInf,
            (Bound::PosInf, _) => Bound::PosInf,
            (Bound::NegInf, _) => Bound::NegInf,
            (_, Bound::PosInf) => Bound::NegInf,
            (_, Bound::NegInf) => Bound::PosInf,
        }
    }

    /// Negation of bound.
    pub fn neg(self) -> Bound {
        match self {
            Bound::NegInf => Bound::PosInf,
            Bound::Finite(n) => Bound::Finite(n.saturating_neg()),
            Bound::PosInf => Bound::NegInf,
        }
    }
}

impl PartialOrd for Bound {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Bound {
    fn cmp(&self, other: &Self) -> Ordering {
        match (self, other) {
            (Bound::NegInf, Bound::NegInf) => Ordering::Equal,
            (Bound::NegInf, _) => Ordering::Less,
            (_, Bound::NegInf) => Ordering::Greater,
            (Bound::PosInf, Bound::PosInf) => Ordering::Equal,
            (Bound::PosInf, _) => Ordering::Greater,
            (_, Bound::PosInf) => Ordering::Less,
            (Bound::Finite(a), Bound::Finite(b)) => a.cmp(b),
        }
    }
}

impl fmt::Display for Bound {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Bound::NegInf => write!(f, "-∞"),
            Bound::Finite(n) => write!(f, "{}", n),
            Bound::PosInf => write!(f, "+∞"),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_bound_arithmetic() {
        use Bound::*;

        // Addition
        assert_eq!(Finite(5).add(Finite(3)), Finite(8));
        assert_eq!(NegInf.add(Finite(5)), NegInf);
        assert_eq!(PosInf.add(Finite(-5)), PosInf);

        // Subtraction
        assert_eq!(Finite(5).sub(Finite(3)), Finite(2));
        assert_eq!(PosInf.sub(Finite(5)), PosInf);
        assert_eq!(Finite(5).sub(PosInf), NegInf);

        // Negation
        assert_eq!(Finite(5).neg(), Finite(-5));
        assert_eq!(NegInf.neg(), PosInf);
        assert_eq!(PosInf.neg(), NegInf);

        // Ordering
        assert!(NegInf < Finite(0));
        assert!(Finite(0) < PosInf);
        assert!(Finite(-100) < Finite(100));
    }
}
