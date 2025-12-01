//! Core abstract domain traits.
//!
//! This module defines the fundamental traits for abstract interpretation:
//! - [`AbstractDomain`]: Lattice operations for abstract values.
//! - [`PredicateTransfer`]: Refining abstract values from predicate constraints.
//! - [`Concretizable`]: Generating concrete values from abstract domains.

use crate::predicate::CompareOp;

/// Abstract domain trait for lattice operations.
///
/// An abstract domain is a mathematical structure used in abstract interpretation
/// to approximate program states. It forms a complete lattice with:
///
/// - A partial order (`⊑`, implemented via [`leq`](Self::leq))
/// - A least element (`⊥`, via [`bottom`](Self::bottom))
/// - A greatest element (`⊤`, via [`top`](Self::top))
/// - Join (`⊔`, via [`join`](Self::join)) — least upper bound
/// - Meet (`⊓`, via [`meet`](Self::meet)) — greatest lower bound
///
/// Additionally, infinite ascending chains require acceleration via:
/// - Widening (`∇`, via [`widen`](Self::widen)) — ensures termination
/// - Narrowing (`△`, via [`narrow`](Self::narrow)) — recovers precision after widening
///
/// # Example
///
/// ```rust
/// use tbdd_pbt::domain::{AbstractDomain, Interval};
///
/// let a = Interval::from_bounds(0, 10);
/// let b = Interval::from_bounds(5, 20);
///
/// // Join: least upper bound
/// let joined = a.join(&b);  // [0, 20]
///
/// // Meet: greatest lower bound
/// let met = a.meet(&b);     // [5, 10]
///
/// // Lattice order
/// assert!(a.leq(&joined));  // a ⊑ (a ⊔ b)
/// assert!(met.leq(&a));     // (a ⊓ b) ⊑ a
/// ```
pub trait AbstractDomain: Clone {
    /// Create the bottom element (`⊥`).
    ///
    /// Bottom represents the empty set of concrete values (infeasible state).
    fn bottom() -> Self;

    /// Create the top element (`⊤`).
    ///
    /// Top represents all possible concrete values (no information).
    fn top() -> Self;

    /// Check if this is the bottom element.
    fn is_bottom(&self) -> bool;

    /// Check if this is the top element.
    fn is_top(&self) -> bool;

    /// Join (least upper bound, `⊔`).
    ///
    /// Returns the smallest element that is greater than or equal to both.
    /// Used when merging states at control flow joins.
    fn join(&self, other: &Self) -> Self;

    /// Meet (greatest lower bound, `⊓`).
    ///
    /// Returns the largest element that is less than or equal to both.
    /// Used when intersecting constraints.
    fn meet(&self, other: &Self) -> Self;

    /// Widening operator (`∇`).
    ///
    /// Accelerates convergence by jumping to a safe over-approximation.
    /// Essential for termination when analyzing infinite-state systems.
    ///
    /// **Invariant:** `a ⊔ b ⊑ a ∇ b`
    fn widen(&self, other: &Self) -> Self;

    /// Narrowing operator (`△`).
    ///
    /// Recovers precision lost during widening by iteratively refining.
    ///
    /// **Invariant:** `a ⊓ b ⊑ a △ b ⊑ a`
    fn narrow(&self, other: &Self) -> Self;

    /// Lattice ordering (`⊑`).
    ///
    /// Returns `true` if `self` is less than or equal to `other` in the lattice.
    /// Semantically: every concrete value in `self` is also in `other`.
    fn leq(&self, other: &Self) -> bool;
}

/// Transfer function for predicate constraints.
///
/// Refines an abstract value based on assuming a predicate holds (or doesn't).
/// This is the foundation of path-sensitive analysis — different paths through
/// conditionals produce different abstract states.
///
/// # Example
///
/// ```rust
/// use tbdd_pbt::domain::{AbstractDomain, PredicateTransfer, Interval, Bound};
/// use tbdd_pbt::predicate::CompareOp;
///
/// let interval = Interval::top();
///
/// // Assume x < 10
/// let refined = interval.transfer(CompareOp::Lt, 10, true);
/// assert_eq!(refined.high(), Bound::Finite(9));
///
/// // Assume NOT(x < 10), i.e., x >= 10
/// let refined = interval.transfer(CompareOp::Lt, 10, false);
/// assert_eq!(refined.low(), Bound::Finite(10));
/// ```
pub trait PredicateTransfer: AbstractDomain {
    /// Refine the domain based on a predicate `var op constant`.
    ///
    /// # Parameters
    ///
    /// - `op`: The comparison operator (`<`, `≤`, `>`, `≥`, `=`, `≠`).
    /// - `constant`: The constant being compared against.
    /// - `positive`: Whether the predicate is asserted (`true`) or negated (`false`).
    ///
    /// # Returns
    ///
    /// The refined domain, typically `self ⊓ constraint`.
    fn transfer(&self, op: CompareOp, constant: i64, positive: bool) -> Self;
}

/// Convert abstract values to concrete witnesses.
///
/// Used for test case generation: given an abstract state, produce
/// concrete values that satisfy the abstracted constraints.
pub trait Concretizable {
    /// Generate a single concrete value from the abstract domain.
    ///
    /// Returns `None` if the domain is bottom (empty set).
    fn concretize(&self) -> Option<i64>;

    /// Sample multiple concrete values from the abstract domain.
    ///
    /// Attempts to generate `count` diverse values, though fewer may
    /// be returned if the domain doesn't contain enough distinct values.
    fn sample(&self, count: usize) -> Vec<i64>;
}
