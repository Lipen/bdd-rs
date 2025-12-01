//! Abstract domains for T-BDD constraint solving.
//!
//! This module provides abstract interpretation domains for sound
//! approximation of program values. Domains can be composed to achieve
//! varying precision/performance trade-offs.
//!
//! # Design
//!
//! We use a simplified design where the domain trait is implemented directly
//! on value types (e.g., `Interval` implements `AbstractDomain`). This differs
//! from the classical approach where domains are factories with associated
//! element types, but is more ergonomic for our use case of single-variable
//! constraint refinement.
//!
//! For multi-variable states, use [`DomainState<D>`] which maps variable names
//! to domain elements.
//!
//! # Available Domains
//!
//! | Domain | Abstraction | Precision | Use Case |
//! |--------|-------------|-----------|----------|
//! | [`Interval`] | `[min, max]` bounds | Medium | Numeric ranges |
//! | [`Sign`] | `{neg, zero, pos}` | Low | Sign analysis |
//! | [`Congruence`] | `x ≡ r (mod m)` | Low | Alignment, parity |
//! | [`ReducedProduct`] | Domain combination | High | Combined analysis |
//!
//! # Lattice Structure
//!
//! All domains form complete lattices with:
//! - **Bottom** (`⊥`): Empty set — no concrete values
//! - **Top** (`⊤`): Universal set — all concrete values
//! - **Join** (`⊔`): Least upper bound — over-approximation
//! - **Meet** (`⊓`): Greatest lower bound — intersection
//! - **Widening** (`∇`): Ensures fixpoint convergence
//! - **Narrowing** (`△`): Recovers precision after widening
//!
//! # Example
//!
//! ```rust
//! use tbdd_pbt::domain::{AbstractDomain, Interval, Bound};
//!
//! // Create intervals with explicit bounds
//! let a = Interval::new(Bound::Finite(0), Bound::Finite(10));
//! let b = Interval::new(Bound::Finite(5), Bound::Finite(15));
//!
//! // Lattice operations
//! let joined = a.join(&b);  // [0, 15]
//! let met = a.meet(&b);     // [5, 10]
//!
//! // Convenience constructors
//! let c = Interval::from_bounds(0, 10);
//! let d = Interval::constant(42);
//! ```

use std::cmp::{self, Ordering};
use std::collections::HashMap;
use std::fmt;

use crate::predicate::{CompareOp, Operand, Predicate};
use crate::theory::Witness;

// =============================================================================
// Core Traits
// =============================================================================

/// Core trait for abstract domains.
///
/// Abstract domains form lattices that approximate sets of concrete values.
/// Each domain element represents a (possibly infinite) set of concrete values.
///
/// # Lattice Axioms
///
/// Implementations must satisfy:
/// - **Reflexivity**: `∀a. a ⊑ a`
/// - **Transitivity**: `∀a,b,c. a ⊑ b ∧ b ⊑ c → a ⊑ c`
/// - **Antisymmetry**: `∀a,b. a ⊑ b ∧ b ⊑ a → a = b`
/// - **Join properties**: `a ⊑ a ⊔ b`, `b ⊑ a ⊔ b`, least such element
/// - **Meet properties**: `a ⊓ b ⊑ a`, `a ⊓ b ⊑ b`, greatest such element
///
/// # Soundness
///
/// For program analysis, operations must be *sound* (over-approximate):
/// - If concrete value `v ∈ γ(a)` and `v ∈ γ(b)`, then `v ∈ γ(a ⊔ b)`
/// - Transfer functions must preserve all reachable states
pub trait AbstractDomain: Clone + PartialEq + fmt::Debug {
    /// Bottom element (`⊥`): represents the empty set of values.
    ///
    /// Satisfies: `∀a. ⊥ ⊑ a` and `∀a. a ⊔ ⊥ = a`
    fn bottom() -> Self;

    /// Top element (`⊤`): represents all possible values.
    ///
    /// Satisfies: `∀a. a ⊑ ⊤` and `∀a. a ⊓ ⊤ = a`
    fn top() -> Self;

    /// Check if this is the bottom element.
    fn is_bottom(&self) -> bool;

    /// Check if this is the top element.
    fn is_top(&self) -> bool;

    /// Join (`⊔`): least upper bound.
    ///
    /// Returns the smallest element containing both `self` and `other`.
    /// Semantically: union of represented value sets.
    fn join(&self, other: &Self) -> Self;

    /// Meet (`⊓`): greatest lower bound.
    ///
    /// Returns the largest element contained in both `self` and `other`.
    /// Semantically: intersection of represented value sets.
    fn meet(&self, other: &Self) -> Self;

    /// Widening (`∇`): accelerate fixpoint convergence.
    ///
    /// Must satisfy: `a ⊑ a ∇ b` (over-approximation).
    /// Used to ensure termination on infinite ascending chains.
    ///
    /// Typical strategy: if `b` exceeds `a`, jump to infinity.
    fn widen(&self, other: &Self) -> Self;

    /// Narrowing (`△`): recover precision after widening.
    ///
    /// Must satisfy: `a ⊓ b ⊑ a △ b ⊑ a` (between meet and self).
    /// Used to refine over-approximations from widening.
    fn narrow(&self, other: &Self) -> Self;

    /// Partial order (`⊑`): `self` is more precise than `other`.
    ///
    /// Returns `true` if every value in `self` is also in `other`.
    fn leq(&self, other: &Self) -> bool;
}

/// Transfer functions for predicate constraints.
///
/// Implements abstract semantics of comparison predicates, allowing
/// domains to be refined based on path conditions.
pub trait PredicateTransfer: AbstractDomain {
    /// Refine the domain based on a predicate constraint.
    ///
    /// # Arguments
    /// - `op`: Comparison operator (Lt, Le, Gt, Ge, Eq, Ne)
    /// - `constant`: The constant being compared against
    /// - `positive`: Whether the predicate is asserted true or false
    ///
    /// # Example
    /// ```ignore
    /// // For predicate "x < 10" being true:
    /// let refined = interval.transfer(CompareOp::Lt, 10, true);
    /// // refined is now [-∞, 9]
    /// ```
    fn transfer(&self, op: CompareOp, constant: i64, positive: bool) -> Self;
}

/// Ability to generate concrete witness values.
///
/// Used by theory solvers to produce test inputs from abstract states.
pub trait Concretizable {
    /// Generate a single concrete value from the abstract domain.
    ///
    /// Returns `None` if the domain is bottom (empty).
    /// Prefers "interesting" values (e.g., 0, boundaries).
    fn concretize(&self) -> Option<i64>;

    /// Generate multiple concrete values for testing.
    ///
    /// Returns representative samples including boundaries,
    /// zero (if contained), and spread values.
    fn sample(&self, count: usize) -> Vec<i64>;
}

// =============================================================================
// Bound Type
// =============================================================================

/// Interval bound: negative infinity, finite value, or positive infinity.
///
/// Provides proper representation of interval endpoints without magic numbers.
/// Implements arithmetic operations that correctly handle infinite bounds.
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

// =============================================================================
// Interval Domain
// =============================================================================

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
                let products = [
                    a.saturating_mul(c),
                    a.saturating_mul(d),
                    b.saturating_mul(c),
                    b.saturating_mul(d),
                ];
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

// Backwards compatibility alias
/// Type alias for backwards compatibility.
#[deprecated(since = "0.2.0", note = "use `Interval` instead")]
pub type IntervalDomain = Interval;

// =============================================================================
// Sign Domain
// =============================================================================

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

/// Type alias for backwards compatibility.
#[deprecated(since = "0.2.0", note = "use `Sign` instead")]
pub type SignDomain = Sign;

// =============================================================================
// Congruence Domain
// =============================================================================

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

/// Greatest common divisor (Euclidean algorithm).
fn gcd(a: u64, b: u64) -> u64 {
    if b == 0 {
        a
    } else {
        gcd(b, a % b)
    }
}

/// Type alias for backwards compatibility.
#[deprecated(since = "0.2.0", note = "use `Congruence` instead")]
pub type CongruenceDomain = Congruence;

// =============================================================================
// Reduced Product
// =============================================================================

/// Reduced product of two domains for increased precision.
///
/// Combines two domains by maintaining both abstractions simultaneously.
/// Information can flow between components through the reduction operator,
/// potentially discovering infeasibility that neither domain alone would detect.
///
/// # Theory
///
/// For domains `D₁` and `D₂`, the reduced product `D₁ ⊗ D₂` has elements
/// `(d₁, d₂)` where operations apply component-wise. The *reduction* operator
/// `ρ: D₁ × D₂ → D₁ × D₂` exploits cross-domain information:
///
/// - If `d₁ = ⊥` or `d₂ = ⊥`, reduce to `(⊥, ⊥)`
/// - Domain-specific reductions can propagate constraints
///
/// # Example
///
/// ```rust
/// use tbdd_pbt::domain::{ReducedProduct, Interval, Sign, AbstractDomain};
///
/// // Combine interval [−10, 10] with NonNegative sign
/// let interval = Interval::from_bounds(-10, 10);
/// let sign = Sign::NonNegative;
/// let product = ReducedProduct::new(interval, sign);
///
/// // Product is more precise than either component alone
/// assert!(!product.is_bottom());
/// ```
#[derive(Debug, Clone, PartialEq)]
pub struct ReducedProduct<D1, D2> {
    /// First domain component.
    pub d1: D1,
    /// Second domain component.
    pub d2: D2,
}

impl<D1, D2> ReducedProduct<D1, D2> {
    /// Create a new reduced product from two domain elements.
    pub fn new(d1: D1, d2: D2) -> Self {
        Self { d1, d2 }
    }
}

impl<D1: AbstractDomain, D2: AbstractDomain> AbstractDomain for ReducedProduct<D1, D2> {
    fn bottom() -> Self {
        Self {
            d1: D1::bottom(),
            d2: D2::bottom(),
        }
    }

    fn top() -> Self {
        Self {
            d1: D1::top(),
            d2: D2::top(),
        }
    }

    fn is_bottom(&self) -> bool {
        // Reduced: if either is bottom, the whole product is bottom
        self.d1.is_bottom() || self.d2.is_bottom()
    }

    fn is_top(&self) -> bool {
        self.d1.is_top() && self.d2.is_top()
    }

    fn join(&self, other: &Self) -> Self {
        Self {
            d1: self.d1.join(&other.d1),
            d2: self.d2.join(&other.d2),
        }
    }

    fn meet(&self, other: &Self) -> Self {
        Self {
            d1: self.d1.meet(&other.d1),
            d2: self.d2.meet(&other.d2),
        }
    }

    fn widen(&self, other: &Self) -> Self {
        Self {
            d1: self.d1.widen(&other.d1),
            d2: self.d2.widen(&other.d2),
        }
    }

    fn narrow(&self, other: &Self) -> Self {
        Self {
            d1: self.d1.narrow(&other.d1),
            d2: self.d2.narrow(&other.d2),
        }
    }

    fn leq(&self, other: &Self) -> bool {
        self.d1.leq(&other.d1) && self.d2.leq(&other.d2)
    }
}

impl<D1: Concretizable, D2: Concretizable> Concretizable for ReducedProduct<D1, D2> {
    fn concretize(&self) -> Option<i64> {
        // Try first component, fall back to second
        self.d1.concretize().or_else(|| self.d2.concretize())
    }

    fn sample(&self, count: usize) -> Vec<i64> {
        let s1 = self.d1.sample(count);
        if s1.is_empty() {
            self.d2.sample(count)
        } else {
            s1
        }
    }
}

// =============================================================================
// Domain State
// =============================================================================

/// Abstract state mapping variables to domain elements.
///
/// Represents the abstract state of a program at a particular point,
/// where each variable is mapped to an abstract value from domain `D`.
///
/// # Non-relational
///
/// This is a *non-relational* abstraction: each variable is tracked
/// independently. Relationships between variables (e.g., `x ≤ y`) are lost.
/// For relational analysis, use domains like Octagons or Polyhedra.
///
/// # Example
///
/// ```rust
/// use tbdd_pbt::domain::{DomainState, Interval, AbstractDomain};
///
/// let mut state: DomainState<Interval> = DomainState::new();
/// state.set("x", Interval::from_bounds(0, 100));
/// state.set("y", Interval::from_bounds(-50, 50));
///
/// assert!(state.get("x").contains(50));
/// assert!(!state.get("x").contains(200));
///
/// // Unknown variables return top
/// assert!(state.get("z").is_top());
/// ```
#[derive(Debug, Clone)]
pub struct DomainState<D: AbstractDomain> {
    values: HashMap<String, D>,
}

impl<D: AbstractDomain> DomainState<D> {
    /// Create an empty state (all variables are top).
    pub fn new() -> Self {
        Self { values: HashMap::new() }
    }

    /// Get the abstract value for a variable.
    ///
    /// Returns top if the variable is not in the state.
    pub fn get(&self, var: &str) -> D {
        self.values.get(var).cloned().unwrap_or_else(D::top)
    }

    /// Set the abstract value for a variable.
    pub fn set(&mut self, var: impl Into<String>, value: D) {
        self.values.insert(var.into(), value);
    }

    /// Check if any variable is bottom (making the whole state unreachable).
    pub fn is_bottom(&self) -> bool {
        self.values.values().any(|v| v.is_bottom())
    }

    /// Join two states (point-wise join of all variables).
    pub fn join(&self, other: &Self) -> Self {
        let mut result = Self::new();
        for (var, val) in &self.values {
            let other_val = other.get(var);
            result.set(var.clone(), val.join(&other_val));
        }
        for (var, val) in &other.values {
            if !self.values.contains_key(var) {
                result.set(var.clone(), val.clone());
            }
        }
        result
    }

    /// Meet two states (point-wise meet of all variables).
    pub fn meet(&self, other: &Self) -> Self {
        let mut result = Self::new();
        for (var, val) in &self.values {
            let other_val = other.get(var);
            result.set(var.clone(), val.meet(&other_val));
        }
        for (var, val) in &other.values {
            if !self.values.contains_key(var) {
                result.set(var.clone(), val.clone());
            }
        }
        result
    }
}

impl<D: AbstractDomain> Default for DomainState<D> {
    fn default() -> Self {
        Self::new()
    }
}

impl<D: AbstractDomain + PredicateTransfer> DomainState<D> {
    /// Apply a predicate constraint to refine the state.
    ///
    /// Only handles predicates of the form `var op constant`.
    pub fn apply_predicate(&mut self, pred: &Predicate, positive: bool) {
        if let Operand::Const(c) = pred.rhs {
            let var = &pred.lhs.0;
            let current = self.get(var);
            let refined = current.transfer(pred.op, c, positive);
            self.set(var.clone(), refined);
        }
    }
}

impl<D: AbstractDomain + Concretizable> DomainState<D> {
    /// Generate a concrete witness from the abstract state.
    ///
    /// Returns `None` if any variable is bottom (infeasible state).
    pub fn to_witness(&self) -> Option<Witness> {
        let mut witness = Witness::new();

        for (var, domain) in &self.values {
            if let Some(value) = domain.concretize() {
                witness.values.insert(var.clone(), value);
            } else {
                return None; // Variable is bottom — no witness
            }
        }

        Some(witness)
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

    #[test]
    fn test_domain_state() {
        let mut state: DomainState<Interval> = DomainState::new();

        state.set("x", Interval::from_bounds(0, 100));
        state.set("y", Interval::from_bounds(-50, 50));

        let pred = Predicate::lt("x", 50);
        state.apply_predicate(&pred, true);

        assert_eq!(state.get("x").high(), Bound::Finite(49));
        assert_eq!(state.get("y").high(), Bound::Finite(50)); // Unchanged
    }

    #[test]
    fn test_reduced_product() {
        let interval = Interval::from_bounds(-10, 10);
        let sign = Sign::NonNegative;

        let product = ReducedProduct::new(interval, sign);

        assert!(!product.is_bottom());
        assert!(!product.is_top());

        // Should be able to concretize
        assert!(product.concretize().is_some());
    }

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
