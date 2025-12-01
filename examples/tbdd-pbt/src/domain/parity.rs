//! Parity abstract domain.
//!
//! Tracks whether values are even or odd. This is a simple but useful
//! domain for detecting off-by-one errors and ensuring correct loop indexing.

use super::interval::Interval;
use super::product::Reducible;
use super::sign::Sign;
use super::traits::{AbstractDomain, Concretizable, PredicateTransfer};
use crate::predicate::CompareOp;

/// Parity abstract domain: tracks whether values are even or odd.
///
/// A simple abstraction useful for detecting:
/// - Off-by-one errors (e.g., `i < n` vs `i <= n`)
/// - Array index parity (even/odd access patterns)
/// - Loop iteration patterns
///
/// # Lattice Structure
///
/// ```text
///       ⊤ (any)
///      / \
///   Even  Odd
///      \ /
///       ⊥
/// ```
///
/// The lattice has 4 elements:
/// - `Bottom`: empty set (no values)
/// - `Even`: all even integers (`x mod 2 = 0`)
/// - `Odd`: all odd integers (`x mod 2 = 1`)
/// - `Top`: all integers
///
/// # Key Insight
///
/// Zero is even! This means:
/// - `Parity::Even` includes 0, so `Sign::Zero` implies `Parity::Even`
/// - `Parity::Odd` excludes 0, so `Sign::Zero ∧ Parity::Odd = ⊥`
///
/// # Example
///
/// ```rust
/// use tbdd_pbt::domain::{Parity, AbstractDomain};
///
/// let even = Parity::Even;
/// let odd = Parity::Odd;
///
/// // Join gives least upper bound
/// assert_eq!(even.join(&odd), Parity::Top);
///
/// // Meet gives greatest lower bound
/// assert_eq!(even.meet(&odd), Parity::Bottom);
///
/// // Zero is even
/// assert!(Parity::Even.contains(0));
/// assert!(!Parity::Odd.contains(0));
/// ```
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Parity {
    /// Empty set — no values.
    Bottom,
    /// Even integers (`x mod 2 = 0`): ..., -4, -2, 0, 2, 4, ...
    Even,
    /// Odd integers (`x mod 2 = 1`): ..., -3, -1, 1, 3, 5, ...
    Odd,
    /// All integers.
    Top,
}

impl Parity {
    /// Check if a concrete value has this parity.
    pub fn contains(&self, value: i64) -> bool {
        match self {
            Parity::Bottom => false,
            Parity::Even => value % 2 == 0,
            Parity::Odd => value % 2 != 0,
            Parity::Top => true,
        }
    }

    /// Abstract a concrete value to its parity.
    pub fn abstract_value(value: i64) -> Self {
        if value % 2 == 0 {
            Parity::Even
        } else {
            Parity::Odd
        }
    }

    /// Get the parity of a value after adding a constant.
    ///
    /// - Even + Even = Even
    /// - Even + Odd = Odd
    /// - Odd + Odd = Even
    pub fn add_constant(&self, constant: i64) -> Self {
        match self {
            Parity::Bottom => Parity::Bottom,
            Parity::Top => Parity::Top,
            Parity::Even => {
                if constant % 2 == 0 {
                    Parity::Even
                } else {
                    Parity::Odd
                }
            }
            Parity::Odd => {
                if constant % 2 == 0 {
                    Parity::Odd
                } else {
                    Parity::Even
                }
            }
        }
    }

    /// Get the parity of a value after multiplication by a constant.
    ///
    /// - Any × Even constant = Even (if not bottom)
    /// - Even × Odd constant = Even
    /// - Odd × Odd constant = Odd
    pub fn mul_constant(&self, constant: i64) -> Self {
        match self {
            Parity::Bottom => Parity::Bottom,
            Parity::Top => {
                if constant % 2 == 0 {
                    Parity::Even // Any × even = even
                } else {
                    Parity::Top // Any × odd preserves parity
                }
            }
            Parity::Even => {
                if constant == 0 {
                    Parity::Even // 0 is even
                } else {
                    Parity::Even // Even × any non-zero = even
                }
            }
            Parity::Odd => {
                if constant % 2 == 0 {
                    Parity::Even // Odd × even = even
                } else {
                    Parity::Odd // Odd × odd = odd
                }
            }
        }
    }
}

impl AbstractDomain for Parity {
    fn bottom() -> Self {
        Parity::Bottom
    }

    fn top() -> Self {
        Parity::Top
    }

    fn is_bottom(&self) -> bool {
        matches!(self, Parity::Bottom)
    }

    fn is_top(&self) -> bool {
        matches!(self, Parity::Top)
    }

    fn join(&self, other: &Self) -> Self {
        use Parity::*;
        match (self, other) {
            (Bottom, x) | (x, Bottom) => *x,
            (Top, _) | (_, Top) => Top,
            (Even, Even) => Even,
            (Odd, Odd) => Odd,
            (Even, Odd) | (Odd, Even) => Top,
        }
    }

    fn meet(&self, other: &Self) -> Self {
        use Parity::*;
        match (self, other) {
            (Top, x) | (x, Top) => *x,
            (Bottom, _) | (_, Bottom) => Bottom,
            (Even, Even) => Even,
            (Odd, Odd) => Odd,
            (Even, Odd) | (Odd, Even) => Bottom,
        }
    }

    fn widen(&self, other: &Self) -> Self {
        // Finite domain, so widen = join
        self.join(other)
    }

    fn narrow(&self, other: &Self) -> Self {
        // Finite domain, so narrow = meet
        self.meet(other)
    }

    fn leq(&self, other: &Self) -> bool {
        use Parity::*;
        match (self, other) {
            (Bottom, _) => true,
            (_, Top) => true,
            (Even, Even) | (Odd, Odd) => true,
            _ => false,
        }
    }
}

impl PredicateTransfer for Parity {
    fn transfer(&self, op: CompareOp, constant: i64, positive: bool) -> Self {
        if self.is_bottom() {
            return Parity::Bottom;
        }

        let effective_op = if positive { op } else { op.negate() };

        // Parity can sometimes be inferred from equality constraints
        match effective_op {
            CompareOp::Eq => {
                // x == c implies x has parity of c
                let required = Parity::abstract_value(constant);
                self.meet(&required)
            }
            CompareOp::Ne => {
                // x != c doesn't give much parity info in general
                // But if we're Even and c is the only even value we could be, that's ⊥
                // This is too complex for simple intervals, so keep unchanged
                *self
            }
            // Inequalities don't directly constrain parity
            _ => *self,
        }
    }
}

impl Concretizable for Parity {
    fn concretize(&self) -> Option<i64> {
        match self {
            Parity::Bottom => None,
            Parity::Even => Some(0),
            Parity::Odd => Some(1),
            Parity::Top => Some(0),
        }
    }

    fn sample(&self, count: usize) -> Vec<i64> {
        match self {
            Parity::Bottom => vec![],
            Parity::Even => vec![0, 2, -2, 4, -4, 100, -100].into_iter().take(count).collect(),
            Parity::Odd => vec![1, -1, 3, -3, 5, -5, 99, -99].into_iter().take(count).collect(),
            Parity::Top => vec![0, 1, -1, 2, -2, 3, -3].into_iter().take(count).collect(),
        }
    }
}

// =============================================================================
// Reduction: Parity × Sign
// =============================================================================

impl Reducible<Sign> for Parity {
    /// Reduce parity using sign information.
    ///
    /// Key insight: Zero is even, so `Sign::Zero` implies `Parity::Even`.
    fn reduce(&self, sign: &Sign) -> Self {
        match (self, sign) {
            // Bottom propagates
            (Parity::Bottom, _) | (_, Sign::Bottom) => Parity::Bottom,
            // Zero is even
            (Parity::Odd, Sign::Zero) => Parity::Bottom,
            (_, Sign::Zero) => Parity::Even,
            // Other signs don't constrain parity
            _ => *self,
        }
    }
}

// =============================================================================
// Reduction: Parity × Interval
// =============================================================================

impl Reducible<Interval> for Parity {
    /// Reduce parity using interval bounds.
    ///
    /// If interval is a singleton, we know the exact parity.
    fn reduce(&self, interval: &Interval) -> Self {
        if self.is_bottom() || interval.is_bottom() {
            return Parity::Bottom;
        }

        // If interval is a singleton [c, c], we know the parity
        if let (Some(1), Some(c)) = (interval.width(), interval.concretize()) {
            let interval_parity = Parity::abstract_value(c);
            return self.meet(&interval_parity);
        }

        // Otherwise, keep current parity
        *self
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parity_basic() {
        assert!(Parity::Even.contains(0));
        assert!(Parity::Even.contains(2));
        assert!(Parity::Even.contains(-4));
        assert!(!Parity::Even.contains(1));

        assert!(Parity::Odd.contains(1));
        assert!(Parity::Odd.contains(-3));
        assert!(!Parity::Odd.contains(0));
        assert!(!Parity::Odd.contains(2));
    }

    #[test]
    fn test_parity_abstract_value() {
        assert_eq!(Parity::abstract_value(0), Parity::Even);
        assert_eq!(Parity::abstract_value(2), Parity::Even);
        assert_eq!(Parity::abstract_value(-4), Parity::Even);
        assert_eq!(Parity::abstract_value(1), Parity::Odd);
        assert_eq!(Parity::abstract_value(-3), Parity::Odd);
    }

    #[test]
    fn test_parity_join() {
        assert_eq!(Parity::Even.join(&Parity::Even), Parity::Even);
        assert_eq!(Parity::Odd.join(&Parity::Odd), Parity::Odd);
        assert_eq!(Parity::Even.join(&Parity::Odd), Parity::Top);
        assert_eq!(Parity::Bottom.join(&Parity::Even), Parity::Even);
        assert_eq!(Parity::Top.join(&Parity::Odd), Parity::Top);
    }

    #[test]
    fn test_parity_meet() {
        assert_eq!(Parity::Even.meet(&Parity::Even), Parity::Even);
        assert_eq!(Parity::Odd.meet(&Parity::Odd), Parity::Odd);
        assert_eq!(Parity::Even.meet(&Parity::Odd), Parity::Bottom);
        assert_eq!(Parity::Top.meet(&Parity::Even), Parity::Even);
        assert_eq!(Parity::Bottom.meet(&Parity::Odd), Parity::Bottom);
    }

    #[test]
    fn test_parity_leq() {
        assert!(Parity::Bottom.leq(&Parity::Even));
        assert!(Parity::Bottom.leq(&Parity::Top));
        assert!(Parity::Even.leq(&Parity::Top));
        assert!(Parity::Odd.leq(&Parity::Top));
        assert!(!Parity::Even.leq(&Parity::Odd));
        assert!(!Parity::Top.leq(&Parity::Even));
    }

    #[test]
    fn test_parity_add_constant() {
        assert_eq!(Parity::Even.add_constant(0), Parity::Even);
        assert_eq!(Parity::Even.add_constant(2), Parity::Even);
        assert_eq!(Parity::Even.add_constant(1), Parity::Odd);
        assert_eq!(Parity::Odd.add_constant(1), Parity::Even);
        assert_eq!(Parity::Odd.add_constant(2), Parity::Odd);
    }

    #[test]
    fn test_parity_mul_constant() {
        assert_eq!(Parity::Even.mul_constant(3), Parity::Even);
        assert_eq!(Parity::Odd.mul_constant(3), Parity::Odd);
        assert_eq!(Parity::Odd.mul_constant(2), Parity::Even);
        assert_eq!(Parity::Top.mul_constant(2), Parity::Even);
        assert_eq!(Parity::Top.mul_constant(3), Parity::Top);
    }

    #[test]
    fn test_parity_transfer_eq() {
        let top = Parity::Top;

        let eq_zero = top.transfer(CompareOp::Eq, 0, true);
        assert_eq!(eq_zero, Parity::Even);

        let eq_one = top.transfer(CompareOp::Eq, 1, true);
        assert_eq!(eq_one, Parity::Odd);

        let eq_five = top.transfer(CompareOp::Eq, 5, true);
        assert_eq!(eq_five, Parity::Odd);
    }

    #[test]
    fn test_parity_concretize() {
        assert_eq!(Parity::Bottom.concretize(), None);
        assert_eq!(Parity::Even.concretize(), Some(0));
        assert_eq!(Parity::Odd.concretize(), Some(1));
        assert_eq!(Parity::Top.concretize(), Some(0));
    }

    // =========================================================================
    // Reduction Tests: Parity × Sign
    // =========================================================================

    #[test]
    fn test_parity_reduce_by_sign_zero() {
        // Zero is even, so Odd reduced by Zero = ⊥
        assert_eq!(Parity::Odd.reduce(&Sign::Zero), Parity::Bottom);
        assert_eq!(Parity::Even.reduce(&Sign::Zero), Parity::Even);
        assert_eq!(Parity::Top.reduce(&Sign::Zero), Parity::Even);
    }

    #[test]
    fn test_parity_reduce_by_sign_other() {
        // Other signs don't constrain parity
        assert_eq!(Parity::Even.reduce(&Sign::Positive), Parity::Even);
        assert_eq!(Parity::Odd.reduce(&Sign::Negative), Parity::Odd);
        assert_eq!(Parity::Top.reduce(&Sign::NonZero), Parity::Top);
    }

    #[test]
    fn test_parity_reduce_by_sign_bottom() {
        // Bottom sign propagates
        assert_eq!(Parity::Even.reduce(&Sign::Bottom), Parity::Bottom);
        assert_eq!(Parity::Top.reduce(&Sign::Bottom), Parity::Bottom);
    }

    #[test]
    fn test_parity_bottom_reduce_by_any_sign() {
        // Bottom parity stays bottom
        assert_eq!(Parity::Bottom.reduce(&Sign::Positive), Parity::Bottom);
        assert_eq!(Parity::Bottom.reduce(&Sign::Zero), Parity::Bottom);
    }

    // =========================================================================
    // Reduction Tests: Parity × Interval
    // =========================================================================

    #[test]
    fn test_parity_reduce_by_singleton_interval() {
        // Singleton [5, 5] is odd
        let interval = Interval::from_bounds(5, 5);
        assert_eq!(Parity::Top.reduce(&interval), Parity::Odd);
        assert_eq!(Parity::Even.reduce(&interval), Parity::Bottom);

        // Singleton [4, 4] is even
        let interval = Interval::from_bounds(4, 4);
        assert_eq!(Parity::Top.reduce(&interval), Parity::Even);
        assert_eq!(Parity::Odd.reduce(&interval), Parity::Bottom);
    }

    #[test]
    fn test_parity_reduce_by_non_singleton_interval() {
        // Non-singleton intervals don't constrain parity
        let interval = Interval::from_bounds(0, 10);
        assert_eq!(Parity::Even.reduce(&interval), Parity::Even);
        assert_eq!(Parity::Odd.reduce(&interval), Parity::Odd);
        assert_eq!(Parity::Top.reduce(&interval), Parity::Top);
    }

    #[test]
    fn test_parity_reduce_by_bottom_interval() {
        // Bottom interval propagates
        assert_eq!(Parity::Even.reduce(&Interval::bottom()), Parity::Bottom);
        assert_eq!(Parity::Top.reduce(&Interval::bottom()), Parity::Bottom);
    }

    #[test]
    fn test_parity_bottom_reduce_by_any_interval() {
        // Bottom parity stays bottom
        assert_eq!(Parity::Bottom.reduce(&Interval::from_bounds(0, 10)), Parity::Bottom);
    }
}
