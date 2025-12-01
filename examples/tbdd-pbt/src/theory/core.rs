//! Core theory solver types and traits.
//!
//! This module defines the fundamental interface for constraint solving:
//! - [`SolveResult`]: Outcome of solving (Sat/Unsat/Unknown)
//! - [`Witness`]: Concrete variable assignments satisfying constraints
//! - [`ConstraintSolver`]: Trait for theory solvers

use std::collections::HashMap;

use bdd_rs::types::Var;

use crate::predicate::PredicateUniverse;

/// Result of constraint solving.
///
/// Theory solvers return one of three outcomes when analyzing constraint systems.
#[derive(Debug, Clone)]
pub enum SolveResult {
    /// Constraints are satisfiable with the given witness.
    ///
    /// The [`Witness`] provides concrete values for each variable that
    /// satisfy all constraints in the system.
    Sat(Witness),

    /// Constraints are unsatisfiable.
    ///
    /// No assignment of values can satisfy all constraints simultaneously.
    /// This can happen when:
    /// - Interval constraints are contradictory (`x > 10 ∧ x < 5`)
    /// - Relational constraints form a negative cycle (`x < y < z < x`)
    /// - Array indices are provably out of bounds
    Unsat,

    /// Solver cannot determine satisfiability.
    ///
    /// The constraint system is outside the solver's decidable fragment.
    /// Common causes:
    /// - Variable-to-variable comparisons with interval solver
    /// - Non-linear arithmetic
    /// - Constraints involving unsupported operations
    Unknown,
}

/// Concrete witness: variable assignments satisfying constraints.
///
/// A witness maps variable names to concrete integer values that satisfy
/// a set of constraints. Used for:
/// - Test case generation (values to test with)
/// - Counterexample extraction (values showing property violation)
/// - Debugging constraint systems
///
/// # Example
///
/// ```rust
/// use tbdd_pbt::theory::Witness;
///
/// let witness = Witness::new()
///     .with("x", 5)
///     .with("y", 10);
///
/// assert_eq!(witness.get("x"), Some(5));
/// assert_eq!(witness.get("y"), Some(10));
/// assert_eq!(witness.get("z"), None);
/// ```
#[derive(Debug, Clone, Default)]
pub struct Witness {
    /// Variable name → concrete value mapping.
    pub values: HashMap<String, i64>,
}

impl Witness {
    /// Create an empty witness.
    pub fn new() -> Self {
        Self { values: HashMap::new() }
    }

    /// Get the value assigned to a variable.
    pub fn get(&self, var: &str) -> Option<i64> {
        self.values.get(var).copied()
    }

    /// Builder pattern: add a variable assignment.
    pub fn with(mut self, var: impl Into<String>, value: i64) -> Self {
        self.values.insert(var.into(), value);
        self
    }
}

/// Theory solver interface.
///
/// A constraint solver takes BDD variable assignments (which predicates are
/// true/false along a path) and determines if the path is feasible in the
/// underlying theory (e.g., linear integer arithmetic).
///
/// # Theory Combination
///
/// Different solvers handle different constraint fragments:
/// - [`IntervalSolver`](super::IntervalSolver): `x op constant`
/// - [`RelationalSolver`](super::RelationalSolver): `x op y`
/// - [`ModularSolver`](super::ModularSolver): `x % d == r`
/// - [`ArrayBoundsSolver`](super::ArrayBoundsSolver): Array index bounds
/// - [`BitwiseSolver`](super::BitwiseSolver): Bit-level properties
///
/// Use [`CombinedSolver`](super::CombinedSolver) to chain multiple solvers.
///
/// # Example
///
/// ```rust
/// use std::collections::HashMap;
/// use bdd_rs::bdd::Bdd;
/// use tbdd_pbt::predicate::{Predicate, PredicateUniverse};
/// use tbdd_pbt::theory::{ConstraintSolver, IntervalSolver, SolveResult};
///
/// let bdd = Bdd::default();
/// let mut universe = PredicateUniverse::new();
///
/// // Register predicates
/// let var1 = universe.register(Predicate::ge("x", 0), &bdd);
/// let var2 = universe.register(Predicate::lt("x", 100), &bdd);
///
/// // Create assignments (which predicates are true on this path)
/// let mut assignments = HashMap::new();
/// assignments.insert(var1, true);   // x >= 0
/// assignments.insert(var2, true);   // x < 100
///
/// // Solve
/// let solver = IntervalSolver::new();
/// match solver.solve(&assignments, &universe) {
///     SolveResult::Sat(witness) => {
///         let x = witness.get("x").unwrap();
///         assert!(x >= 0 && x < 100);
///     }
///     _ => panic!("Expected Sat"),
/// }
/// ```
pub trait ConstraintSolver {
    /// Solve the constraint system defined by predicate assignments.
    ///
    /// # Parameters
    ///
    /// - `assignments`: Maps BDD variables to their boolean values along a path.
    /// - `universe`: Registry mapping BDD variables to their predicate definitions.
    ///
    /// # Returns
    ///
    /// - [`SolveResult::Sat(witness)`](SolveResult::Sat): Path is feasible; witness provides concrete values.
    /// - [`SolveResult::Unsat`]: Path is infeasible (contradictory constraints).
    /// - [`SolveResult::Unknown`]: Solver cannot decide (constraint outside decidable fragment).
    fn solve(&self, assignments: &HashMap<Var, bool>, universe: &PredicateUniverse) -> SolveResult;
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn witness_builder_pattern() {
        let w = Witness::new().with("x", 10).with("y", 20).with("z", 30);

        assert_eq!(w.get("x"), Some(10));
        assert_eq!(w.get("y"), Some(20));
        assert_eq!(w.get("z"), Some(30));
    }

    #[test]
    fn witness_missing_variable() {
        let w = Witness::new().with("x", 10);
        assert_eq!(w.get("y"), None);
    }

    #[test]
    fn witness_default_is_empty() {
        let w = Witness::default();
        assert!(w.values.is_empty());
    }
}
