//! Numeric abstract domain trait and utilities.

use super::domain::AbstractDomain;
use super::expr::{NumExpr, NumPred};
use std::collections::HashMap;
use std::fmt::Debug;
use std::hash::Hash;

/// Numeric abstract domain for integer/real variables.
///
/// This trait extends `AbstractDomain` with operations specific to
/// numeric program analysis.
pub trait NumericDomain: AbstractDomain {
    /// Variable identifier type.
    type Var: Clone + Eq + Hash + Debug;

    /// Numeric value type.
    type Value: Clone + Debug + PartialOrd;

    /// Create element representing a constant assignment: var = value.
    fn constant(&self, var: &Self::Var, value: Self::Value) -> Self::Element;

    /// Create element representing an interval constraint: var ∈ [low, high].
    fn interval(&self, var: &Self::Var, low: Self::Value, high: Self::Value) -> Self::Element;

    /// Apply assignment: var := expr.
    ///
    /// Returns a new abstract element where `var` is bound to the result of `expr`.
    fn assign(
        &self,
        elem: &Self::Element,
        var: &Self::Var,
        expr: &NumExpr<Self::Var, Self::Value>,
    ) -> Self::Element;

    /// Assume a predicate holds: elem ∧ pred.
    ///
    /// Refines the abstract element by adding constraint `pred`.
    fn assume(
        &self,
        elem: &Self::Element,
        pred: &NumPred<Self::Var, Self::Value>,
    ) -> Self::Element;

    /// Project out a variable (existential quantification): ∃var. elem.
    ///
    /// Removes all constraints on `var`.
    fn project(&self, elem: &Self::Element, var: &Self::Var) -> Self::Element;

    /// Get the constant value of a variable if it's uniquely determined.
    fn get_constant(&self, elem: &Self::Element, var: &Self::Var) -> Option<Self::Value>;

    /// Get the interval bounds for a variable: [low, high].
    fn get_bounds(
        &self,
        elem: &Self::Element,
        var: &Self::Var,
    ) -> Option<(Self::Value, Self::Value)>;

    /// Rename variables using a substitution map.
    fn rename(&self, elem: &Self::Element, _subst: &HashMap<Self::Var, Self::Var>) -> Self::Element {
        // Default implementation: identity (can be overridden for efficiency)
        elem.clone()
    }

    /// Check if element is infeasible (bottom).
    fn is_infeasible(&self, elem: &Self::Element) -> bool {
        self.is_bottom(elem)
    }
}
