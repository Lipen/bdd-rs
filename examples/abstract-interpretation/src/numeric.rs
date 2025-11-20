//! Numeric abstract domain trait and utilities.

use std::collections::HashMap;
use std::fmt::Debug;
use std::hash::Hash;

use super::domain::AbstractDomain;
use super::expr::{NumExpr, NumPred};

/// Numeric abstract domain for integer/real variables.
///
/// This trait extends `AbstractDomain` with operations specific to
/// numeric program analysis.
pub trait NumericDomain: AbstractDomain {
    /// Variable identifier type.
    type Var: Clone + Eq + Hash + Debug;

    /// Numeric value type.
    type Value: Clone + Debug + PartialOrd;

    /// Create element representing a constant assignment: `var = value`.
    fn constant(&self, var: &Self::Var, value: Self::Value) -> Self::Element;

    /// Create element representing an interval constraint: `var ∈ [low, high]`.
    fn interval(&self, var: &Self::Var, low: Self::Value, high: Self::Value) -> Self::Element;

    /// Apply assignment: `var := expr`.
    ///
    /// Returns a new abstract element where `var` is bound to the result of `expr`.
    fn assign(&self, elem: &Self::Element, var: &Self::Var, expr: &NumExpr<Self::Var, Self::Value>) -> Self::Element;

    /// Assume a predicate holds: `elem ∧ pred`.
    ///
    /// Refines the abstract element by adding constraint `pred`.
    fn assume(&self, elem: &Self::Element, pred: &NumPred<Self::Var, Self::Value>) -> Self::Element;

    /// Project out a variable (existential quantification): `∃var. elem`.
    ///
    /// Removes all constraints on `var`.
    fn project(&self, elem: &Self::Element, var: &Self::Var) -> Self::Element;

    /// Get the constant value of a variable if it's uniquely determined.
    fn get_constant(&self, elem: &Self::Element, var: &Self::Var) -> Option<Self::Value>;

    /// Get the interval bounds for a variable: `[low, high]`.
    fn get_bounds(&self, elem: &Self::Element, var: &Self::Var) -> Option<(Self::Value, Self::Value)>;

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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::expr::NumExpr;
    use crate::interval::{Bound, Interval, IntervalDomain, IntervalElement};

    #[test]
    fn test_numeric_domain_constant() {
        let domain = IntervalDomain;
        let elem = domain.constant(&"x".to_string(), 42);

        assert_eq!(elem.get("x"), Interval::constant(42));
        assert_eq!(domain.get_constant(&elem, &"x".to_string()), Some(42));
    }

    #[test]
    fn test_numeric_domain_interval() {
        let domain = IntervalDomain;
        let elem = domain.interval(&"x".to_string(), -10, 10);

        assert_eq!(elem.get("x"), Interval::new(Bound::Finite(-10), Bound::Finite(10)));
        assert_eq!(domain.get_bounds(&elem, &"x".to_string()), Some((-10, 10)));
    }

    #[test]
    fn test_numeric_domain_assign() {
        let domain = IntervalDomain;
        let mut elem = IntervalElement::new();
        elem.set("x".to_string(), Interval::constant(5));

        // y := x + 10
        let expr = NumExpr::Add(Box::new(NumExpr::Var("x".to_string())), Box::new(NumExpr::Const(10)));
        let result = domain.assign(&elem, &"y".to_string(), &expr);

        assert_eq!(result.get("x"), Interval::constant(5));
        assert_eq!(result.get("y"), Interval::constant(15));
    }

    #[test]
    fn test_numeric_domain_assign_complex() {
        let domain = IntervalDomain;
        let mut elem = IntervalElement::new();
        elem.set("x".to_string(), Interval::new(Bound::Finite(0), Bound::Finite(10)));
        elem.set("y".to_string(), Interval::new(Bound::Finite(5), Bound::Finite(15)));

        // z := x + y
        let expr = NumExpr::Add(Box::new(NumExpr::Var("x".to_string())), Box::new(NumExpr::Var("y".to_string())));
        let result = domain.assign(&elem, &"z".to_string(), &expr);

        assert_eq!(result.get("z"), Interval::new(Bound::Finite(5), Bound::Finite(25)));
    }

    #[test]
    fn test_numeric_domain_assume() {
        let domain = IntervalDomain;
        let elem = domain.interval(&"x".to_string(), -10, 10);

        // assume(x >= 0)
        let pred = crate::expr::NumPred::Ge(NumExpr::Var("x".to_string()), NumExpr::Const(0));
        let refined = domain.assume(&elem, &pred);

        assert_eq!(refined.get("x"), Interval::new(Bound::Finite(0), Bound::Finite(10)));
    }

    #[test]
    fn test_numeric_domain_assume_contradiction() {
        let domain = IntervalDomain;
        let elem = domain.interval(&"x".to_string(), 0, 10);

        // assume(x < 0) - contradiction
        let pred = crate::expr::NumPred::Lt(NumExpr::Var("x".to_string()), NumExpr::Const(0));
        let refined = domain.assume(&elem, &pred);

        assert!(domain.is_infeasible(&refined));
    }

    #[test]
    fn test_numeric_domain_project() {
        let domain = IntervalDomain;
        let mut elem = IntervalElement::new();
        elem.set("x".to_string(), Interval::constant(5));
        elem.set("y".to_string(), Interval::constant(10));

        let projected = domain.project(&elem, &"x".to_string());

        // x should be removed, y should remain
        assert_eq!(projected.get("x"), Interval::top());
        assert_eq!(projected.get("y"), Interval::constant(10));
    }

    #[test]
    fn test_numeric_domain_multiple_constraints() {
        let domain = IntervalDomain;
        let elem = domain.interval(&"x".to_string(), -100, 100);

        // assume(x >= 0)
        let pred1 = crate::expr::NumPred::Ge(NumExpr::Var("x".to_string()), NumExpr::Const(0));
        let refined1 = domain.assume(&elem, &pred1);

        // assume(x <= 50)
        let pred2 = crate::expr::NumPred::Le(NumExpr::Var("x".to_string()), NumExpr::Const(50));
        let refined2 = domain.assume(&refined1, &pred2);

        assert_eq!(refined2.get("x"), Interval::new(Bound::Finite(0), Bound::Finite(50)));
        assert_eq!(domain.get_bounds(&refined2, &"x".to_string()), Some((0, 50)));
    }

    #[test]
    fn test_numeric_domain_arithmetic_precision() {
        let domain = IntervalDomain;
        let mut elem = IntervalElement::new();
        elem.set("x".to_string(), Interval::new(Bound::Finite(1), Bound::Finite(2)));

        // y := x * x (should be [1, 4])
        let expr = NumExpr::Mul(Box::new(NumExpr::Var("x".to_string())), Box::new(NumExpr::Var("x".to_string())));
        let result = domain.assign(&elem, &"y".to_string(), &expr);

        assert_eq!(result.get("y"), Interval::new(Bound::Finite(1), Bound::Finite(4)));
    }
}
