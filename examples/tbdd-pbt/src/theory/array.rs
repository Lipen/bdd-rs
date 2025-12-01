//! Array bounds constraint solver.
//!
//! Validates array indexing constraints to ensure safe array access.

use std::collections::HashMap;

use bdd_rs::types::Var;

use super::core::{ConstraintSolver, SolveResult};
use super::interval::{Interval, IntervalSolver};
use crate::predicate::PredicateUniverse;

/// Array constraint: index must be in bounds `[0, length)`.
#[derive(Debug, Clone)]
pub struct ArrayConstraint {
    /// Index variable name.
    pub index: String,
    /// Array length (or length variable).
    pub length: ArrayLength,
}

/// Array length can be a constant or a variable.
#[derive(Debug, Clone)]
pub enum ArrayLength {
    /// Fixed-size array.
    Const(i64),
    /// Variable-length array.
    Var(String),
}

/// Solver for array bounds constraints.
///
/// Ensures array indices are in bounds: `0 <= index < length`.
/// Supports both constant and variable-length arrays.
///
/// # Example
///
/// ```rust
/// use std::collections::HashMap;
/// use bdd_rs::bdd::Bdd;
/// use tbdd_pbt::predicate::{Predicate, PredicateUniverse};
/// use tbdd_pbt::theory::{ArrayBoundsSolver, ArrayLength, ConstraintSolver, SolveResult};
///
/// let bdd = Bdd::default();
/// let mut universe = PredicateUniverse::new();
///
/// let var1 = universe.register(Predicate::ge("i", 0), &bdd);
/// let var2 = universe.register(Predicate::lt("i", 10), &bdd);
///
/// let mut solver = ArrayBoundsSolver::new();
/// solver.register_array("arr", "i", ArrayLength::Const(10));
///
/// let mut assignments = HashMap::new();
/// assignments.insert(var1, true);
/// assignments.insert(var2, true);
///
/// match solver.solve(&assignments, &universe) {
///     SolveResult::Sat(w) => {
///         let i = w.get("i").unwrap();
///         assert!(i >= 0 && i < 10);
///     }
///     _ => panic!("Expected Sat"),
/// }
/// ```
pub struct ArrayBoundsSolver {
    /// Array constraints indexed by array name.
    arrays: HashMap<String, ArrayConstraint>,
    /// Interval solver for underlying arithmetic.
    interval_solver: IntervalSolver,
}

impl ArrayBoundsSolver {
    /// Create a new array bounds solver.
    pub fn new() -> Self {
        Self {
            arrays: HashMap::new(),
            interval_solver: IntervalSolver::with_bounds(0, i64::MAX / 2),
        }
    }

    /// Register an array with its index variable and length.
    pub fn register_array(&mut self, array_name: impl Into<String>, index: impl Into<String>, length: ArrayLength) {
        self.arrays.insert(
            array_name.into(),
            ArrayConstraint {
                index: index.into(),
                length,
            },
        );
    }

    /// Check if an index is in bounds given interval constraints.
    fn check_bounds(&self, intervals: &HashMap<String, Interval>, constraint: &ArrayConstraint) -> bool {
        let Some(index_interval) = intervals.get(&constraint.index) else {
            return true; // No constraint on index
        };

        // Index must be >= 0
        if index_interval.max < 0 {
            return false;
        }

        // Index must be < length
        match &constraint.length {
            ArrayLength::Const(len) => index_interval.min < *len,
            ArrayLength::Var(len_var) => {
                // If we have length constraints, check them
                if let Some(len_interval) = intervals.get(len_var) {
                    // index.min < length.max (conservative)
                    index_interval.min < len_interval.max
                } else {
                    true // Assume unbounded length
                }
            }
        }
    }
}

impl Default for ArrayBoundsSolver {
    fn default() -> Self {
        Self::new()
    }
}

impl ConstraintSolver for ArrayBoundsSolver {
    /// Solve constraints with array bounds checking.
    ///
    /// # Algorithm
    ///
    /// Layers array safety verification on top of interval solving.
    ///
    /// **Safety invariant:** For `arr[index]`, require `0 <= index < arr.length`.
    ///
    /// ## Steps
    ///
    /// 1. **Base solve** — Use [`IntervalSolver`] to get a candidate witness.
    ///
    /// 2. **Verify bounds** — For each registered array:
    ///    - `index >= 0` (no negative indexing)
    ///    - `index < length` (no buffer overflow)
    ///    - For variable-length arrays, use interval bounds conservatively.
    ///
    /// 3. **Return** — `Sat(witness)` if all checks pass, else `Unsat`.
    ///
    /// # Example
    ///
    /// ```text
    /// Array: arr[i], length=10
    /// Constraints: i >= 0, i < 10
    /// Witness: i=5 → 0 <= 5 < 10 ✓ → Sat
    ///
    /// Constraints: i >= 10
    /// Witness: i=10 → 10 < 10 ✗ → Unsat
    /// ```
    fn solve(&self, assignments: &HashMap<Var, bool>, universe: &PredicateUniverse) -> SolveResult {
        // Step 1: Delegate to interval solver for basic constraint satisfaction
        let result = self.interval_solver.solve(assignments, universe);
        let SolveResult::Sat(witness) = result else {
            return result; // Propagate Unsat or Unknown from base solver
        };

        // Step 2: Convert witness to point intervals for bounds checking
        // Each concrete value v becomes the interval [v, v]
        let intervals: HashMap<String, Interval> = witness.values.iter().map(|(k, &v)| (k.clone(), Interval::new(v, v))).collect();

        // Step 3: Verify all array bounds constraints
        for (_, constraint) in &self.arrays {
            if !self.check_bounds(&intervals, constraint) {
                // Array access would be out of bounds!
                return SolveResult::Unsat;
            }
        }

        // All array accesses are safe
        SolveResult::Sat(witness)
    }
}

#[cfg(test)]
mod tests {
    use bdd_rs::bdd::Bdd;

    use super::*;
    use crate::predicate::Predicate;

    #[test]
    fn valid_index() {
        let bdd = Bdd::default();
        let mut universe = crate::predicate::PredicateUniverse::new();

        let p1 = Predicate::ge("index", 0);
        let p2 = Predicate::lt("index", 10);
        let var1 = universe.register(p1, &bdd);
        let var2 = universe.register(p2, &bdd);

        let mut solver = ArrayBoundsSolver::new();
        solver.register_array("arr", "index", ArrayLength::Const(10));

        let mut assignments = HashMap::new();
        assignments.insert(var1, true);
        assignments.insert(var2, true);

        match solver.solve(&assignments, &universe) {
            SolveResult::Sat(witness) => {
                let idx = witness.get("index").unwrap();
                assert!(idx >= 0 && idx < 10, "index={} should be in [0, 10)", idx);
            }
            other => panic!("Expected Sat, got {:?}", other),
        }
    }

    #[test]
    fn out_of_bounds_high() {
        let bdd = Bdd::default();
        let mut universe = crate::predicate::PredicateUniverse::new();

        let p1 = Predicate::ge("index", 10);
        let var1 = universe.register(p1, &bdd);

        let mut solver = ArrayBoundsSolver::new();
        solver.register_array("arr", "index", ArrayLength::Const(10));

        let mut assignments = HashMap::new();
        assignments.insert(var1, true);

        // Should be Unsat because index >= 10 is out of bounds for array of size 10
        assert!(matches!(solver.solve(&assignments, &universe), SolveResult::Unsat));
    }

    #[test]
    fn out_of_bounds_negative() {
        let bdd = Bdd::default();
        let mut universe = crate::predicate::PredicateUniverse::new();

        let p1 = Predicate::lt("index", 0);
        let var1 = universe.register(p1, &bdd);

        let mut solver = ArrayBoundsSolver::new();
        solver.register_array("arr", "index", ArrayLength::Const(10));

        let mut assignments = HashMap::new();
        assignments.insert(var1, true);

        // Should be Unsat because negative index
        assert!(matches!(solver.solve(&assignments, &universe), SolveResult::Unsat));
    }

    #[test]
    fn variable_length_array() {
        let bdd = Bdd::default();
        let mut universe = crate::predicate::PredicateUniverse::new();

        let p1 = Predicate::ge("index", 0);
        let p2 = Predicate::lt("index", 5);
        let p3 = Predicate::gt("len", 5);
        let var1 = universe.register(p1, &bdd);
        let var2 = universe.register(p2, &bdd);
        let var3 = universe.register(p3, &bdd);

        let mut solver = ArrayBoundsSolver::new();
        solver.register_array("arr", "index", ArrayLength::Var("len".to_string()));

        let mut assignments = HashMap::new();
        assignments.insert(var1, true);
        assignments.insert(var2, true);
        assignments.insert(var3, true);

        match solver.solve(&assignments, &universe) {
            SolveResult::Sat(witness) => {
                let idx = witness.get("index").unwrap();
                assert!(idx >= 0 && idx < 5, "index={} should be in [0, 5)", idx);
            }
            other => panic!("Expected Sat, got {:?}", other),
        }
    }
}
