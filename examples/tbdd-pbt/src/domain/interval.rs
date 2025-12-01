//! Interval abstract domain.
//!
//! The interval domain tracks lower and upper bounds for numeric values.
//! It's simple and efficient, but loses relational information between variables.

use std::cmp;
use std::fmt;

use super::bound::Bound;
use super::parity::Parity;
use super::product::Reducible;
use super::sign::Sign;
use super::traits::{AbstractDomain, Concretizable, PredicateTransfer};
use crate::predicate::CompareOp;

/// Interval abstract domain: represents values as `[low, high]`.
///
/// The interval domain tracks lower and upper bounds for numeric values.
/// It's simple and efficient, but loses relational information between variables.
///
/// # Lattice Structure
///
/// - **Order** (`⊑`): `[l₁, h₁] ⊑ [l₂, h₂]` iff `l₂ ≤ l₁ ∧ h₁ ≤ h₂` (containment)
/// - **Join** (`⊔`): `[l₁, h₁] ⊔ [l₂, h₂] = [min(l₁, l₂), max(h₁, h₂)]` (convex hull)
/// - **Meet** (`⊓`): `[l₁, h₁] ⊓ [l₂, h₂] = [max(l₁, l₂), min(h₁, h₂)]` (intersection)
/// - **Bottom** (`⊥`): Empty interval (represented as `[+∞, -∞]`)
/// - **Top** (`⊤`): `[-∞, +∞]`
///
/// # Widening Strategy
///
/// When the new bound exceeds the old, jump to infinity:
/// - If `b.low < a.low`, set `low = -∞`
/// - If `b.high > a.high`, set `high = +∞`
///
/// This ensures termination on infinite ascending chains.
///
/// # Example
///
/// ```rust
/// use tbdd_pbt::domain::{Interval, Bound, AbstractDomain};
///
/// let a = Interval::from_bounds(0, 10);
/// let b = Interval::from_bounds(5, 15);
///
/// let joined = a.join(&b);
/// assert_eq!(joined.low(), Bound::Finite(0));
/// assert_eq!(joined.high(), Bound::Finite(15));
///
/// let met = a.meet(&b);
/// assert_eq!(met.low(), Bound::Finite(5));
/// assert_eq!(met.high(), Bound::Finite(10));
/// ```
#[derive(Clone, PartialEq, Eq, Hash)]
pub struct Interval {
    low: Bound,
    high: Bound,
}

impl Interval {
    /// Create an interval `[low, high]`.
    ///
    /// If `low > high`, returns bottom (empty interval).
    pub fn new(low: Bound, high: Bound) -> Self {
        if low > high {
            Self::bottom()
        } else {
            Self { low, high }
        }
    }

    /// Create an interval from finite bounds `[min, max]`.
    pub fn from_bounds(min: i64, max: i64) -> Self {
        Self::new(Bound::Finite(min), Bound::Finite(max))
    }

    /// Create a singleton interval `[c, c]`.
    pub fn constant(c: i64) -> Self {
        Self::from_bounds(c, c)
    }

    /// Get the lower bound.
    pub fn low(&self) -> Bound {
        self.low
    }

    /// Get the upper bound.
    pub fn high(&self) -> Bound {
        self.high
    }

    /// Check if interval contains a value.
    pub fn contains(&self, value: i64) -> bool {
        if self.is_bottom() {
            return false;
        }
        let v = Bound::Finite(value);
        self.low <= v && v <= self.high
    }

    /// Get the width of the interval (number of values), if finite.
    pub fn width(&self) -> Option<u64> {
        match (self.low, self.high) {
            (Bound::Finite(l), Bound::Finite(h)) if l <= h => Some((h - l) as u64 + 1),
            _ => None,
        }
    }

    /// Addition of intervals: `[a, b] + [c, d] = [a+c, b+d]`.
    pub fn add(&self, other: &Self) -> Self {
        if self.is_bottom() || other.is_bottom() {
            return Self::bottom();
        }
        Self::new(self.low.add(other.low), self.high.add(other.high))
    }

    /// Subtraction of intervals: `[a, b] - [c, d] = [a-d, b-c]`.
    pub fn sub(&self, other: &Self) -> Self {
        if self.is_bottom() || other.is_bottom() {
            return Self::bottom();
        }
        Self::new(self.low.sub(other.high), self.high.sub(other.low))
    }

    /// Negation of interval: `-[a, b] = [-b, -a]`.
    pub fn neg(&self) -> Self {
        if self.is_bottom() {
            return Self::bottom();
        }
        Self::new(self.high.neg(), self.low.neg())
    }

    /// Multiplication of intervals.
    ///
    /// Computes the convex hull of all pairwise products of bounds.
    pub fn mul(&self, other: &Self) -> Self {
        if self.is_bottom() || other.is_bottom() {
            return Self::bottom();
        }

        // For finite intervals, compute exact bounds
        match (self.low, self.high, other.low, other.high) {
            (Bound::Finite(a), Bound::Finite(b), Bound::Finite(c), Bound::Finite(d)) => {
                let products = [a.saturating_mul(c), a.saturating_mul(d), b.saturating_mul(c), b.saturating_mul(d)];
                let min = *products.iter().min().unwrap();
                let max = *products.iter().max().unwrap();
                Self::from_bounds(min, max)
            }
            // For infinite bounds, return top (safe over-approximation)
            _ => Self::top(),
        }
    }
}

impl AbstractDomain for Interval {
    fn bottom() -> Self {
        Self {
            low: Bound::PosInf,
            high: Bound::NegInf,
        }
    }

    fn top() -> Self {
        Self {
            low: Bound::NegInf,
            high: Bound::PosInf,
        }
    }

    fn is_bottom(&self) -> bool {
        self.low > self.high
    }

    fn is_top(&self) -> bool {
        self.low == Bound::NegInf && self.high == Bound::PosInf
    }

    fn join(&self, other: &Self) -> Self {
        if self.is_bottom() {
            return other.clone();
        }
        if other.is_bottom() {
            return self.clone();
        }
        Self {
            low: cmp::min(self.low, other.low),
            high: cmp::max(self.high, other.high),
        }
    }

    fn meet(&self, other: &Self) -> Self {
        Self::new(cmp::max(self.low, other.low), cmp::min(self.high, other.high))
    }

    fn widen(&self, other: &Self) -> Self {
        if self.is_bottom() {
            return other.clone();
        }
        if other.is_bottom() {
            return self.clone();
        }
        Self {
            low: if other.low < self.low { Bound::NegInf } else { self.low },
            high: if other.high > self.high { Bound::PosInf } else { self.high },
        }
    }

    fn narrow(&self, other: &Self) -> Self {
        if self.is_bottom() || other.is_bottom() {
            return Self::bottom();
        }
        Self::new(
            if self.low == Bound::NegInf { other.low } else { self.low },
            if self.high == Bound::PosInf { other.high } else { self.high },
        )
    }

    fn leq(&self, other: &Self) -> bool {
        if self.is_bottom() {
            return true;
        }
        if other.is_bottom() {
            return false;
        }
        other.low <= self.low && self.high <= other.high
    }
}

impl PredicateTransfer for Interval {
    fn transfer(&self, op: CompareOp, constant: i64, positive: bool) -> Self {
        if self.is_bottom() {
            return Self::bottom();
        }

        let effective_op = if positive { op } else { op.negate() };
        let c = Bound::Finite(constant);

        let constraint = match effective_op {
            CompareOp::Lt => Self::new(Bound::NegInf, Bound::Finite(constant - 1)),
            CompareOp::Le => Self::new(Bound::NegInf, c),
            CompareOp::Gt => Self::new(Bound::Finite(constant + 1), Bound::PosInf),
            CompareOp::Ge => Self::new(c, Bound::PosInf),
            CompareOp::Eq => Self::constant(constant),
            CompareOp::Ne => {
                // Cannot represent the hole exactly — return unchanged (sound)
                return self.clone();
            }
        };

        self.meet(&constraint)
    }
}

impl Concretizable for Interval {
    fn concretize(&self) -> Option<i64> {
        if self.is_bottom() {
            return None;
        }
        // Prefer values near zero, then midpoint
        if self.contains(0) {
            Some(0)
        } else {
            match (self.low, self.high) {
                (Bound::Finite(l), Bound::Finite(h)) => Some(l + (h - l) / 2),
                (Bound::Finite(l), Bound::PosInf) => Some(l),
                (Bound::NegInf, Bound::Finite(h)) => Some(h),
                _ => Some(0),
            }
        }
    }

    fn sample(&self, count: usize) -> Vec<i64> {
        if self.is_bottom() || count == 0 {
            return Vec::new();
        }

        let mut samples = Vec::new();

        // Include boundaries if finite
        if let Bound::Finite(l) = self.low {
            samples.push(l);
        }
        if let Bound::Finite(h) = self.high {
            if samples.last() != Some(&h) {
                samples.push(h);
            }
        }

        // Include zero if in range
        if self.contains(0) && !samples.contains(&0) {
            samples.push(0);
        }

        // Add midpoint for finite intervals
        if let (Bound::Finite(l), Bound::Finite(h)) = (self.low, self.high) {
            let mid = l + (h - l) / 2;
            if !samples.contains(&mid) {
                samples.push(mid);
            }

            // Fill remaining with spread values
            if samples.len() < count && h > l {
                let step = (h - l) / (count as i64 + 1);
                if step > 0 {
                    for i in 1..count as i64 {
                        let val = l + i * step;
                        if !samples.contains(&val) {
                            samples.push(val);
                        }
                    }
                }
            }
        }

        samples.truncate(count);
        samples.sort();
        samples
    }
}

impl fmt::Debug for Interval {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.is_bottom() {
            write!(f, "⊥")
        } else if self.is_top() {
            write!(f, "⊤")
        } else {
            write!(f, "[{}, {}]", self.low, self.high)
        }
    }
}

impl fmt::Display for Interval {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(self, f)
    }
}

// =============================================================================
// Reduction: Interval × Sign
// =============================================================================

impl Reducible<Sign> for Interval {
    /// Reduce interval using sign information.
    ///
    /// # Examples
    ///
    /// - `[-10, 10].reduce(Positive)` → `[1, 10]`
    /// - `[-10, 10].reduce(Negative)` → `[-10, -1]`
    /// - `[-10, 10].reduce(Zero)` → `[0, 0]`
    /// - `[-10, 10].reduce(NonNegative)` → `[0, 10]`
    fn reduce(&self, sign: &Sign) -> Self {
        if self.is_bottom() || sign.is_bottom() {
            return Self::bottom();
        }

        match sign {
            Sign::Bottom => Self::bottom(),
            Sign::Negative => {
                // Value must be < 0
                let new_high = self.high.min(Bound::Finite(-1));
                Self::new(self.low, new_high)
            }
            Sign::Zero => {
                // Value must be exactly 0
                if self.contains(0) {
                    Self::constant(0)
                } else {
                    Self::bottom()
                }
            }
            Sign::Positive => {
                // Value must be > 0
                let new_low = self.low.max(Bound::Finite(1));
                Self::new(new_low, self.high)
            }
            Sign::NonNegative => {
                // Value must be >= 0
                let new_low = self.low.max(Bound::Finite(0));
                Self::new(new_low, self.high)
            }
            Sign::NonPositive => {
                // Value must be <= 0
                let new_high = self.high.min(Bound::Finite(0));
                Self::new(self.low, new_high)
            }
            Sign::NonZero => {
                // Value must be != 0; can't express this precisely, keep as-is
                // In a more sophisticated implementation, we could split [a,b] into
                // [a,-1] ∪ [1,b], but intervals are convex.
                self.clone()
            }
            Sign::Top => self.clone(),
        }
    }
}

// =============================================================================
// Reduction: Interval × Parity
// =============================================================================

impl Reducible<Parity> for Interval {
    /// Reduce interval using parity information.
    ///
    /// This is a weak reduction since intervals are convex.
    fn reduce(&self, parity: &Parity) -> Self {
        if self.is_bottom() || parity.is_bottom() {
            return Interval::bottom();
        }

        // Intervals are convex, so we can't exclude odd/even values from the middle.
        // The best we can do is check if the interval is entirely even/odd incompatible.

        // Check if interval width is 1 (singleton)
        if let (Some(1), Some(c)) = (self.width(), self.concretize()) {
            let value_parity = Parity::abstract_value(c);
            if value_parity.meet(parity).is_bottom() {
                return Interval::bottom();
            }
        }

        // Otherwise, keep interval as-is
        self.clone()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_interval_basic() {
        let a = Interval::from_bounds(0, 10);
        let b = Interval::from_bounds(5, 15);

        assert!(a.contains(0));
        assert!(a.contains(10));
        assert!(!a.contains(-1));

        let joined = a.join(&b);
        assert_eq!(joined.low(), Bound::Finite(0));
        assert_eq!(joined.high(), Bound::Finite(15));

        let met = a.meet(&b);
        assert_eq!(met.low(), Bound::Finite(5));
        assert_eq!(met.high(), Bound::Finite(10));
    }

    #[test]
    fn test_interval_bottom() {
        let a = Interval::from_bounds(0, 5);
        let b = Interval::from_bounds(10, 15);

        let met = a.meet(&b);
        assert!(met.is_bottom());
    }

    #[test]
    fn test_interval_transfer() {
        let top = Interval::top();

        let lt10 = top.transfer(CompareOp::Lt, 10, true);
        assert!(lt10.contains(9));
        assert!(!lt10.contains(10));

        let ge5 = lt10.transfer(CompareOp::Ge, 5, true);
        assert_eq!(ge5.low(), Bound::Finite(5));
        assert_eq!(ge5.high(), Bound::Finite(9));
    }

    #[test]
    fn test_interval_widening() {
        let a = Interval::from_bounds(0, 0);
        let b = Interval::from_bounds(0, 1);
        let c = Interval::from_bounds(0, 2);

        let widened = a.widen(&b);
        assert_eq!(widened.low(), Bound::Finite(0));
        assert_eq!(widened.high(), Bound::PosInf); // Widened to infinity

        let _narrowed = widened.narrow(&c);
        // Narrowing should recover precision
    }

    // =========================================================================
    // Reduction Tests: Interval reduced by Sign
    // =========================================================================

    #[test]
    fn test_interval_reduce_by_positive() {
        // [-10, 10] reduced by Positive → [1, 10]
        let interval = Interval::from_bounds(-10, 10);
        let reduced = interval.reduce(&Sign::Positive);

        assert_eq!(reduced.low(), Bound::Finite(1));
        assert_eq!(reduced.high(), Bound::Finite(10));
    }

    #[test]
    fn test_interval_reduce_by_negative() {
        // [-10, 10] reduced by Negative → [-10, -1]
        let interval = Interval::from_bounds(-10, 10);
        let reduced = interval.reduce(&Sign::Negative);

        assert_eq!(reduced.low(), Bound::Finite(-10));
        assert_eq!(reduced.high(), Bound::Finite(-1));
    }

    #[test]
    fn test_interval_reduce_by_zero() {
        // [-10, 10] reduced by Zero → [0, 0]
        let interval = Interval::from_bounds(-10, 10);
        let reduced = interval.reduce(&Sign::Zero);

        assert_eq!(reduced.low(), Bound::Finite(0));
        assert_eq!(reduced.high(), Bound::Finite(0));
    }

    #[test]
    fn test_interval_reduce_by_zero_not_in_range() {
        // [5, 10] reduced by Zero → ⊥ (no zero in range)
        let interval = Interval::from_bounds(5, 10);
        let reduced = interval.reduce(&Sign::Zero);

        assert!(reduced.is_bottom());
    }

    #[test]
    fn test_interval_reduce_by_nonnegative() {
        // [-10, 10] reduced by NonNegative → [0, 10]
        let interval = Interval::from_bounds(-10, 10);
        let reduced = interval.reduce(&Sign::NonNegative);

        assert_eq!(reduced.low(), Bound::Finite(0));
        assert_eq!(reduced.high(), Bound::Finite(10));
    }

    #[test]
    fn test_interval_reduce_by_nonpositive() {
        // [-10, 10] reduced by NonPositive → [-10, 0]
        let interval = Interval::from_bounds(-10, 10);
        let reduced = interval.reduce(&Sign::NonPositive);

        assert_eq!(reduced.low(), Bound::Finite(-10));
        assert_eq!(reduced.high(), Bound::Finite(0));
    }

    #[test]
    fn test_interval_reduce_by_nonzero() {
        // [-10, 10] reduced by NonZero → [-10, 10] (can't express hole)
        let interval = Interval::from_bounds(-10, 10);
        let reduced = interval.reduce(&Sign::NonZero);

        // Intervals are convex, can't represent {x | x ≠ 0}
        assert_eq!(reduced.low(), Bound::Finite(-10));
        assert_eq!(reduced.high(), Bound::Finite(10));
    }

    #[test]
    fn test_interval_reduce_positive_by_negative_is_bottom() {
        // [5, 10] reduced by Negative → ⊥ (no overlap)
        let interval = Interval::from_bounds(5, 10);
        let reduced = interval.reduce(&Sign::Negative);

        assert!(reduced.is_bottom());
    }

    #[test]
    fn test_interval_reduce_negative_by_positive_is_bottom() {
        // [-10, -5] reduced by Positive → ⊥ (no overlap)
        let interval = Interval::from_bounds(-10, -5);
        let reduced = interval.reduce(&Sign::Positive);

        assert!(reduced.is_bottom());
    }

    #[test]
    fn test_interval_reduce_by_top() {
        // [-10, 10] reduced by Top → [-10, 10] (no change)
        let interval = Interval::from_bounds(-10, 10);
        let reduced = interval.reduce(&Sign::Top);

        assert_eq!(reduced.low(), Bound::Finite(-10));
        assert_eq!(reduced.high(), Bound::Finite(10));
    }

    #[test]
    fn test_interval_reduce_by_bottom() {
        // [-10, 10] reduced by Bottom → ⊥
        let interval = Interval::from_bounds(-10, 10);
        let reduced = interval.reduce(&Sign::Bottom);

        assert!(reduced.is_bottom());
    }

    #[test]
    fn test_interval_bottom_reduce_by_any() {
        // ⊥ reduced by any sign → ⊥
        let interval = Interval::bottom();
        let reduced = interval.reduce(&Sign::Positive);

        assert!(reduced.is_bottom());
    }
}
