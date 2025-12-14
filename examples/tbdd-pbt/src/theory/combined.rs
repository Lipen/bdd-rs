//! Combined/chained constraint solvers.
//!
//! Provides solver composition for handling multiple constraint types.

use std::collections::HashMap;

use ananke_bdd::types::Var;

use super::core::{ConstraintSolver, SolveResult};
use super::interval::IntervalSolver;
use super::relational::RelationalSolver;
use crate::predicate::PredicateUniverse;

/// Combined solver that chains multiple theory solvers.
///
/// First checks each solver for unsatisfiability, then generates
/// a witness from the most capable solver that succeeds.
///
/// # Example
///
/// ```rust
/// use tbdd_pbt::theory::{CombinedSolver, IntervalSolver, RelationalSolver};
///
/// let combined = CombinedSolver::new(
///     IntervalSolver::new(),
///     RelationalSolver::new(),
/// );
/// ```
pub struct CombinedSolver<S1, S2>
where
    S1: ConstraintSolver,
    S2: ConstraintSolver,
{
    solver1: S1,
    solver2: S2,
}

impl<S1, S2> CombinedSolver<S1, S2>
where
    S1: ConstraintSolver,
    S2: ConstraintSolver,
{
    /// Create a combined solver from two component solvers.
    pub fn new(solver1: S1, solver2: S2) -> Self {
        Self { solver1, solver2 }
    }
}

impl<S1, S2> ConstraintSolver for CombinedSolver<S1, S2>
where
    S1: ConstraintSolver,
    S2: ConstraintSolver,
{
    /// Solve by chaining multiple theory solvers.
    ///
    /// # Algorithm
    ///
    /// Sequential solver composition inspired by Nelson-Oppen.
    ///
    /// ## Strategy
    ///
    /// 1. **UNSAT propagation** — If *any* solver returns `Unsat`, propagate it.
    ///    (Sound because each solver is sound — no false `Unsat`.)
    ///
    /// 2. **SAT selection** — Return the first `Sat` witness found.
    ///
    /// 3. **UNKNOWN fallback** — If both return `Unknown`, propagate it.
    ///
    /// # Example
    ///
    /// ```text
    /// IntervalSolver handles: x > 0, y < 100
    /// RelationalSolver handles: x < y
    /// Combined: can solve {x > 0, y < 100, x < y}
    /// ```
    ///
    /// # Limitations
    ///
    /// - Witness from `S1` might not satisfy `S2`'s implicit constraints.
    /// - Full Nelson-Oppen requires witness exchange (not implemented).
    fn solve(&self, assignments: &HashMap<Var, bool>, universe: &PredicateUniverse) -> SolveResult {
        // Step 1: Try solver1 first
        let result1 = self.solver1.solve(assignments, universe);
        if matches!(result1, SolveResult::Unsat) {
            return SolveResult::Unsat;
        }

        // Try solver2
        let result2 = self.solver2.solve(assignments, universe);
        if matches!(result2, SolveResult::Unsat) {
            return SolveResult::Unsat;
        }

        // Return the first Sat witness we got
        match result1 {
            SolveResult::Sat(w) => SolveResult::Sat(w),
            _ => result2,
        }
    }
}

/// Convenience type for interval + relational solving.
///
/// Combines [`IntervalSolver`] for `x op constant` constraints with
/// [`RelationalSolver`] for `x op y` constraints.
pub type IntervalRelationalSolver = CombinedSolver<IntervalSolver, RelationalSolver>;

impl IntervalRelationalSolver {
    /// Create a combined interval + relational solver with default bounds.
    pub fn default_combined() -> Self {
        Self::new(IntervalSolver::new(), RelationalSolver::new())
    }

    /// Create a combined solver with custom bounds.
    pub fn with_bounds(min: i64, max: i64) -> Self {
        Self::new(IntervalSolver::with_bounds(min, max), RelationalSolver::with_bounds(min, max))
    }
}

#[cfg(test)]
mod tests {
    use ananke_bdd::bdd::Bdd;

    use super::*;
    use crate::predicate::Predicate;

    #[test]
    fn interval_relational_combined() {
        let bdd = Bdd::default();
        let mut universe = crate::predicate::PredicateUniverse::new();

        // Interval constraint: x in [0, 100]
        let p1 = Predicate::ge("x", 0);
        let p2 = Predicate::le("x", 100);
        let var1 = universe.register(p1, &bdd);
        let var2 = universe.register(p2, &bdd);

        let solver = IntervalRelationalSolver::with_bounds(0, 100);

        let mut assignments = HashMap::new();
        assignments.insert(var1, true);
        assignments.insert(var2, true);

        match solver.solve(&assignments, &universe) {
            SolveResult::Sat(witness) => {
                let x = witness.get("x").unwrap();
                assert!(x >= 0 && x <= 100, "x={} should be in [0, 100]", x);
            }
            other => panic!("Expected Sat, got {:?}", other),
        }
    }

    #[test]
    fn unsat_from_first_solver() {
        let bdd = Bdd::default();
        let mut universe = crate::predicate::PredicateUniverse::new();

        // Contradictory interval constraint
        let p1 = Predicate::gt("x", 100);
        let p2 = Predicate::lt("x", 50);
        let var1 = universe.register(p1, &bdd);
        let var2 = universe.register(p2, &bdd);

        let solver = IntervalRelationalSolver::with_bounds(0, 200);

        let mut assignments = HashMap::new();
        assignments.insert(var1, true);
        assignments.insert(var2, true);

        assert!(matches!(solver.solve(&assignments, &universe), SolveResult::Unsat));
    }
}
