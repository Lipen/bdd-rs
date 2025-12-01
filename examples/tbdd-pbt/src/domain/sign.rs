//! Sign abstract domain.
//!
//! A simple, coarse abstraction that tracks only whether values are
//! negative, zero, or positive.

use std::cmp::Ordering;

use super::bound::Bound;
use super::interval::Interval;
use super::parity::Parity;
use super::product::Reducible;
use super::traits::{AbstractDomain, Concretizable, PredicateTransfer};
use crate::predicate::CompareOp;

/// Sign abstract domain: abstracts integers by their sign.
///
/// A simple, coarse abstraction that tracks only whether values are
/// negative, zero, or positive. Useful for detecting sign-related bugs
/// (e.g., division by zero, negative array indices).
///
/// # Lattice Structure
///
/// ```text
///           ⊤ (Top)
///        /  |  \
///      ≤0  ≠0   ≥0
///      / \  |  / \
///     <0  =0  >0
///      \   |   /
///         ⊥ (Bottom)
/// ```
///
/// The lattice has 8 elements representing different sign combinations:
/// - `Bottom`: empty set
/// - `Negative`: strictly negative (`< 0`)
/// - `Zero`: exactly zero (`= 0`)
/// - `Positive`: strictly positive (`> 0`)
/// - `NonNegative`: non-negative (`≥ 0`)
/// - `NonPositive`: non-positive (`≤ 0`)
/// - `NonZero`: non-zero (`≠ 0`)
/// - `Top`: all integers
///
/// # Example
///
/// ```rust
/// use tbdd_pbt::domain::{Sign, AbstractDomain};
///
/// let neg = Sign::Negative;
/// let pos = Sign::Positive;
///
/// // Join gives least upper bound
/// assert_eq!(neg.join(&pos), Sign::NonZero);
///
/// // Meet gives greatest lower bound
/// assert_eq!(Sign::NonNegative.meet(&Sign::NonPositive), Sign::Zero);
/// ```
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Sign {
    /// Empty set — no values.
    Bottom,
    /// Strictly negative values (`< 0`).
    Negative,
    /// Only zero (`= 0`).
    Zero,
    /// Strictly positive values (`> 0`).
    Positive,
    /// Non-negative values (`≥ 0`).
    NonNegative,
    /// Non-positive values (`≤ 0`).
    NonPositive,
    /// Non-zero values (`≠ 0`).
    NonZero,
    /// All values.
    Top,
}

impl Sign {
    /// Check if a concrete value is in this sign domain.
    pub fn contains(&self, value: i64) -> bool {
        match self {
            Sign::Bottom => false,
            Sign::Negative => value < 0,
            Sign::Zero => value == 0,
            Sign::Positive => value > 0,
            Sign::NonNegative => value >= 0,
            Sign::NonPositive => value <= 0,
            Sign::NonZero => value != 0,
            Sign::Top => true,
        }
    }

    /// Abstract a concrete value to its sign.
    pub fn abstract_value(value: i64) -> Self {
        match value.cmp(&0) {
            Ordering::Less => Sign::Negative,
            Ordering::Equal => Sign::Zero,
            Ordering::Greater => Sign::Positive,
        }
    }
}

impl AbstractDomain for Sign {
    fn bottom() -> Self {
        Sign::Bottom
    }

    fn top() -> Self {
        Sign::Top
    }

    fn is_bottom(&self) -> bool {
        matches!(self, Sign::Bottom)
    }

    fn is_top(&self) -> bool {
        matches!(self, Sign::Top)
    }

    fn join(&self, other: &Self) -> Self {
        use Sign::*;

        if self == other {
            return *self;
        }
        if self.is_bottom() {
            return *other;
        }
        if other.is_bottom() {
            return *self;
        }
        if self.is_top() || other.is_top() {
            return Top;
        }

        match (self, other) {
            (Negative, Zero) | (Zero, Negative) => NonPositive,
            (Positive, Zero) | (Zero, Positive) => NonNegative,
            (Negative, Positive) | (Positive, Negative) => NonZero,
            (NonNegative, Negative) | (Negative, NonNegative) => Top,
            (NonPositive, Positive) | (Positive, NonPositive) => Top,
            (NonNegative, NonPositive) | (NonPositive, NonNegative) => Top,
            (NonZero, Zero) | (Zero, NonZero) => Top,
            (NonNegative, Positive) | (Positive, NonNegative) => NonNegative,
            (NonNegative, Zero) | (Zero, NonNegative) => NonNegative,
            (NonPositive, Negative) | (Negative, NonPositive) => NonPositive,
            (NonPositive, Zero) | (Zero, NonPositive) => NonPositive,
            (NonZero, Negative) | (Negative, NonZero) => NonZero,
            (NonZero, Positive) | (Positive, NonZero) => NonZero,
            (NonZero, NonNegative) | (NonNegative, NonZero) => Top,
            (NonZero, NonPositive) | (NonPositive, NonZero) => Top,
            _ => Top,
        }
    }

    fn meet(&self, other: &Self) -> Self {
        use Sign::*;

        if self == other {
            return *self;
        }
        if self.is_bottom() || other.is_bottom() {
            return Bottom;
        }
        if self.is_top() {
            return *other;
        }
        if other.is_top() {
            return *self;
        }

        match (self, other) {
            (NonNegative, NonPositive) | (NonPositive, NonNegative) => Zero,
            (NonNegative, NonZero) | (NonZero, NonNegative) => Positive,
            (NonPositive, NonZero) | (NonZero, NonPositive) => Negative,
            (NonNegative, Positive) | (Positive, NonNegative) => Positive,
            (NonNegative, Zero) | (Zero, NonNegative) => Zero,
            (NonPositive, Negative) | (Negative, NonPositive) => Negative,
            (NonPositive, Zero) | (Zero, NonPositive) => Zero,
            (NonZero, Negative) | (Negative, NonZero) => Negative,
            (NonZero, Positive) | (Positive, NonZero) => Positive,
            _ => Bottom,
        }
    }

    fn widen(&self, other: &Self) -> Self {
        // Sign domain is finite, so widening = join
        self.join(other)
    }

    fn narrow(&self, other: &Self) -> Self {
        // Sign domain is finite, so narrowing = meet
        self.meet(other)
    }

    fn leq(&self, other: &Self) -> bool {
        use Sign::*;

        if self.is_bottom() || other.is_top() {
            return true;
        }
        if self.is_top() || other.is_bottom() {
            return false;
        }

        match (self, other) {
            (Negative, NonPositive) | (Negative, NonZero) => true,
            (Positive, NonNegative) | (Positive, NonZero) => true,
            (Zero, NonNegative) | (Zero, NonPositive) => true,
            (a, b) => a == b,
        }
    }
}

impl PredicateTransfer for Sign {
    fn transfer(&self, op: CompareOp, constant: i64, positive: bool) -> Self {
        use Sign::*;

        if self.is_bottom() {
            return Bottom;
        }

        let effective_op = if positive { op } else { op.negate() };

        // Infer sign constraint from predicate
        let constraint = match (effective_op, constant.cmp(&0)) {
            (CompareOp::Lt, Ordering::Less) => Negative,
            (CompareOp::Lt, Ordering::Equal) => Negative,
            (CompareOp::Lt, Ordering::Greater) => Top,
            (CompareOp::Le, Ordering::Less) => Negative,
            (CompareOp::Le, Ordering::Equal) => NonPositive,
            (CompareOp::Le, Ordering::Greater) => Top,
            (CompareOp::Gt, Ordering::Less) => Top,
            (CompareOp::Gt, Ordering::Equal) => Positive,
            (CompareOp::Gt, Ordering::Greater) => Positive,
            (CompareOp::Ge, Ordering::Less) => Top,
            (CompareOp::Ge, Ordering::Equal) => NonNegative,
            (CompareOp::Ge, Ordering::Greater) => Positive,
            (CompareOp::Eq, Ordering::Less) => Negative,
            (CompareOp::Eq, Ordering::Equal) => Zero,
            (CompareOp::Eq, Ordering::Greater) => Positive,
            (CompareOp::Ne, Ordering::Equal) => NonZero,
            (CompareOp::Ne, _) => Top,
        };

        self.meet(&constraint)
    }
}

impl Concretizable for Sign {
    fn concretize(&self) -> Option<i64> {
        match self {
            Sign::Bottom => None,
            Sign::Negative => Some(-1),
            Sign::Zero => Some(0),
            Sign::Positive => Some(1),
            Sign::NonNegative => Some(0),
            Sign::NonPositive => Some(0),
            Sign::NonZero => Some(1),
            Sign::Top => Some(0),
        }
    }

    fn sample(&self, count: usize) -> Vec<i64> {
        match self {
            Sign::Bottom => Vec::new(),
            Sign::Negative => vec![-1, -10, -100].into_iter().take(count).collect(),
            Sign::Zero => vec![0],
            Sign::Positive => vec![1, 10, 100].into_iter().take(count).collect(),
            Sign::NonNegative => vec![0, 1, 10].into_iter().take(count).collect(),
            Sign::NonPositive => vec![0, -1, -10].into_iter().take(count).collect(),
            Sign::NonZero => vec![1, -1, 10, -10].into_iter().take(count).collect(),
            Sign::Top => vec![0, 1, -1, 10, -10].into_iter().take(count).collect(),
        }
    }
}

// =============================================================================
// Reduction: Sign × Interval
// =============================================================================

impl Reducible<Interval> for Sign {
    /// Reduce sign using interval bounds.
    ///
    /// # Examples
    ///
    /// - `Top.reduce([5, 10])` → `Positive`
    /// - `Top.reduce([-10, -5])` → `Negative`
    /// - `Top.reduce([0, 0])` → `Zero`
    /// - `NonZero.reduce([0, 10])` → `Positive` (0 excluded by NonZero)
    fn reduce(&self, interval: &Interval) -> Self {
        use Sign::*;

        if self.is_bottom() || interval.is_bottom() {
            return Bottom;
        }

        // Determine what signs the interval can have
        let can_be_negative = interval.low() < Bound::Finite(0);
        let can_be_zero = interval.contains(0);
        let can_be_positive = interval.high() > Bound::Finite(0);

        // Combine with current sign knowledge
        let interval_sign = match (can_be_negative, can_be_zero, can_be_positive) {
            (false, false, false) => Bottom,
            (true, false, false) => Negative,
            (false, true, false) => Zero,
            (false, false, true) => Positive,
            (true, true, false) => NonPositive,
            (false, true, true) => NonNegative,
            (true, false, true) => NonZero,
            (true, true, true) => Top,
        };

        // Meet with our current sign
        self.meet(&interval_sign)
    }
}

// =============================================================================
// Reduction: Sign × Parity
// =============================================================================

impl Reducible<Parity> for Sign {
    /// Reduce sign using parity information.
    ///
    /// Key insight: Zero is even, so `Parity::Odd` implies non-zero.
    fn reduce(&self, parity: &Parity) -> Self {
        match (self, parity) {
            // Bottom propagates
            (Sign::Bottom, _) | (_, Parity::Bottom) => Sign::Bottom,
            // Odd values can't be zero
            (Sign::Zero, Parity::Odd) => Sign::Bottom,
            (Sign::NonNegative, Parity::Odd) => Sign::Positive,
            (Sign::NonPositive, Parity::Odd) => Sign::Negative,
            (Sign::Top, Parity::Odd) => Sign::NonZero,
            // Even doesn't constrain sign (could be 0, 2, -2, etc.)
            _ => *self,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_sign_basic() {
        use Sign::*;

        assert!(Negative.contains(-1));
        assert!(!Negative.contains(0));

        assert_eq!(Negative.join(&Positive), NonZero);
        assert_eq!(Negative.join(&Zero), NonPositive);

        assert_eq!(NonNegative.meet(&NonPositive), Zero);
        assert_eq!(NonNegative.meet(&NonZero), Positive);
    }

    #[test]
    fn test_sign_transfer() {
        use Sign::*;

        let top = Top;

        let lt0 = top.transfer(CompareOp::Lt, 0, true);
        assert_eq!(lt0, Negative);

        let ge0 = top.transfer(CompareOp::Ge, 0, true);
        assert_eq!(ge0, NonNegative);
    }

    // =========================================================================
    // Reduction Tests: Sign reduced by Interval
    // =========================================================================

    #[test]
    fn test_sign_reduce_top_by_positive_interval() {
        // Top reduced by [5, 10] → Positive
        let sign = Sign::Top;
        let reduced = sign.reduce(&Interval::from_bounds(5, 10));

        assert_eq!(reduced, Sign::Positive);
    }

    #[test]
    fn test_sign_reduce_top_by_negative_interval() {
        // Top reduced by [-10, -5] → Negative
        let sign = Sign::Top;
        let reduced = sign.reduce(&Interval::from_bounds(-10, -5));

        assert_eq!(reduced, Sign::Negative);
    }

    #[test]
    fn test_sign_reduce_top_by_zero_interval() {
        // Top reduced by [0, 0] → Zero
        let sign = Sign::Top;
        let reduced = sign.reduce(&Interval::from_bounds(0, 0));

        assert_eq!(reduced, Sign::Zero);
    }

    #[test]
    fn test_sign_reduce_top_by_nonnegative_interval() {
        // Top reduced by [0, 10] → NonNegative
        let sign = Sign::Top;
        let reduced = sign.reduce(&Interval::from_bounds(0, 10));

        assert_eq!(reduced, Sign::NonNegative);
    }

    #[test]
    fn test_sign_reduce_top_by_nonpositive_interval() {
        // Top reduced by [-10, 0] → NonPositive
        let sign = Sign::Top;
        let reduced = sign.reduce(&Interval::from_bounds(-10, 0));

        assert_eq!(reduced, Sign::NonPositive);
    }

    #[test]
    fn test_sign_reduce_top_by_spanning_interval() {
        // Top reduced by [-10, 10] → Top (all signs possible)
        let sign = Sign::Top;
        let reduced = sign.reduce(&Interval::from_bounds(-10, 10));

        assert_eq!(reduced, Sign::Top);
    }

    #[test]
    fn test_sign_reduce_nonzero_by_nonnegative_interval() {
        // NonZero reduced by [0, 10] → Positive (0 excluded by NonZero)
        let sign = Sign::NonZero;
        let reduced = sign.reduce(&Interval::from_bounds(0, 10));

        assert_eq!(reduced, Sign::Positive);
    }

    #[test]
    fn test_sign_reduce_nonzero_by_nonpositive_interval() {
        // NonZero reduced by [-10, 0] → Negative (0 excluded by NonZero)
        let sign = Sign::NonZero;
        let reduced = sign.reduce(&Interval::from_bounds(-10, 0));

        assert_eq!(reduced, Sign::Negative);
    }

    #[test]
    fn test_sign_reduce_nonnegative_by_positive_interval() {
        // NonNegative reduced by [5, 10] → Positive
        let sign = Sign::NonNegative;
        let reduced = sign.reduce(&Interval::from_bounds(5, 10));

        assert_eq!(reduced, Sign::Positive);
    }

    #[test]
    fn test_sign_reduce_positive_by_negative_interval_is_bottom() {
        // Positive reduced by [-10, -5] → ⊥ (no overlap)
        let sign = Sign::Positive;
        let reduced = sign.reduce(&Interval::from_bounds(-10, -5));

        assert!(reduced.is_bottom());
    }

    #[test]
    fn test_sign_reduce_negative_by_positive_interval_is_bottom() {
        // Negative reduced by [5, 10] → ⊥ (no overlap)
        let sign = Sign::Negative;
        let reduced = sign.reduce(&Interval::from_bounds(5, 10));

        assert!(reduced.is_bottom());
    }

    #[test]
    fn test_sign_reduce_zero_by_nonzero_interval_is_bottom() {
        // Zero reduced by [5, 10] → ⊥ (0 not in interval)
        let sign = Sign::Zero;
        let reduced = sign.reduce(&Interval::from_bounds(5, 10));

        assert!(reduced.is_bottom());
    }

    #[test]
    fn test_sign_reduce_by_bottom_interval() {
        // Any sign reduced by ⊥ interval → ⊥
        let sign = Sign::Top;
        let reduced = sign.reduce(&Interval::bottom());

        assert!(reduced.is_bottom());
    }

    #[test]
    fn test_sign_bottom_reduce_by_any_interval() {
        // ⊥ sign reduced by any interval → ⊥
        let sign = Sign::Bottom;
        let reduced = sign.reduce(&Interval::from_bounds(0, 10));

        assert!(reduced.is_bottom());
    }
}
