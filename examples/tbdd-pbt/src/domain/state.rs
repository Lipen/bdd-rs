//! Multi-variable abstract state.
//!
//! Maps variables to abstract domain elements for program analysis.

use std::collections::HashMap;

use super::traits::{AbstractDomain, Concretizable, PredicateTransfer};
use crate::predicate::{Operand, Predicate};
use crate::theory::Witness;

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
    use crate::domain::{Bound, Interval};
    use crate::predicate::Predicate;

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
}
