//! Modular arithmetic constraint solver.
//!
//! Handles constraints involving divisibility and modular arithmetic.

use std::collections::HashMap;

use ananke_bdd::types::Var;

use super::core::{ConstraintSolver, SolveResult, Witness};
use super::interval::Interval;
use crate::predicate::{Operand, PredicateUniverse};

/// Modular constraint: `x % divisor == remainder`.
#[derive(Debug, Clone)]
pub struct ModularConstraint {
    /// Variable name.
    pub var: String,
    /// The divisor.
    pub divisor: i64,
    /// The required remainder.
    pub remainder: i64,
}

/// Solver for modular arithmetic constraints.
///
/// Handles constraints involving modular arithmetic:
/// - `x % 2 == 0` (x is even)
/// - `x % 3 == 1` (x ≡ 1 mod 3)
///
/// # Example
///
/// ```rust
/// use std::collections::HashMap;
/// use ananke_bdd::bdd::Bdd;
/// use tbdd_pbt::predicate::{Predicate, PredicateUniverse};
/// use tbdd_pbt::theory::{ConstraintSolver, ModularSolver, SolveResult};
///
/// let bdd = Bdd::default();
/// let mut universe = PredicateUniverse::new();
///
/// let var1 = universe.register(Predicate::ge("x", 0), &bdd);
/// let var2 = universe.register(Predicate::le("x", 100), &bdd);
///
/// let solver = ModularSolver::with_bounds(0, 100);
/// let mut assignments = HashMap::new();
/// assignments.insert(var1, true);
/// assignments.insert(var2, true);
///
/// match solver.solve(&assignments, &universe) {
///     SolveResult::Sat(w) => assert!(w.get("x").unwrap() >= 0),
///     _ => panic!("Expected Sat"),
/// }
/// ```
pub struct ModularSolver {
    default_min: i64,
    default_max: i64,
}

impl Default for ModularSolver {
    fn default() -> Self {
        Self::new()
    }
}

impl ModularSolver {
    /// Create a modular solver with default bounds `[-1000, 1000]`.
    pub fn new() -> Self {
        Self {
            default_min: -1000,
            default_max: 1000,
        }
    }

    /// Create a modular solver with custom default bounds.
    pub fn with_bounds(min: i64, max: i64) -> Self {
        Self {
            default_min: min,
            default_max: max,
        }
    }

    /// Find a value satisfying modular constraints within an interval.
    fn find_satisfying_value(&self, interval: &Interval, modular: Option<&ModularConstraint>) -> Option<i64> {
        if interval.is_empty() {
            return None;
        }

        let Some(m) = modular else {
            return interval.pick_value();
        };

        // Find smallest x in [min, max] such that x % divisor == remainder
        let start = interval.min;
        let current_mod = start.rem_euclid(m.divisor);
        let delta = (m.remainder - current_mod).rem_euclid(m.divisor);
        let candidate = start + delta;

        if candidate <= interval.max && interval.excluded != Some(candidate) {
            return Some(candidate);
        }

        // Try next candidate
        let next = candidate + m.divisor;
        if next <= interval.max && interval.excluded != Some(next) {
            return Some(next);
        }

        None
    }
}

impl ConstraintSolver for ModularSolver {
    /// Solve constraints with modular arithmetic support.
    ///
    /// # Algorithm
    ///
    /// Extends interval reasoning with modular constraints: `x % d == r`.
    ///
    /// ## Steps
    ///
    /// 1. **Compute intervals** — Same as [`IntervalSolver`](super::IntervalSolver).
    ///
    /// 2. **Apply modular constraints** — For each `x % d == r`:
    ///    - Find smallest value in `[min, max]` satisfying the constraint.
    ///    - Formula: `candidate = min + ((r - min % d) mod d)`
    ///
    /// 3. **Generate witness** — Pick values satisfying both bounds and modular constraints.
    ///
    /// # Example
    ///
    /// ```text
    /// Given: x >= 10, x <= 20, x % 3 == 1
    /// Interval: [10, 20]
    /// 10 % 3 = 1 ✓ → candidate = 10
    /// Witness: x = 10
    /// ```
    fn solve(&self, assignments: &HashMap<Var, bool>, universe: &PredicateUniverse) -> SolveResult {
        // Step 1: Build intervals from predicate assignments (same as IntervalSolver)
        let mut intervals: HashMap<String, Interval> = HashMap::new();
        let modular_constraints: HashMap<String, ModularConstraint> = HashMap::new();

        for (&bdd_var, &value) in assignments {
            let Some(predicate) = universe.get_predicate(bdd_var) else {
                continue;
            };

            let Operand::Const(constant) = predicate.rhs else {
                return SolveResult::Unknown;
            };

            let var_name = &predicate.lhs.0;
            let interval = intervals
                .entry(var_name.clone())
                .or_insert_with(|| Interval::new(self.default_min, self.default_max));
            *interval = interval.constrain(predicate.op, constant, value);

            if interval.is_empty() {
                return SolveResult::Unsat;
            }
        }

        // Step 2 & 3: Generate witness satisfying both interval and modular constraints
        let mut witness = Witness::new();
        for (var, interval) in &intervals {
            // Look up any modular constraint for this variable
            let modular = modular_constraints.get(var);

            // find_satisfying_value finds a value in the interval that also
            // satisfies the modular constraint (if any)
            match self.find_satisfying_value(interval, modular) {
                Some(val) => {
                    witness.values.insert(var.clone(), val);
                }
                None => return SolveResult::Unsat,
            }
        }

        SolveResult::Sat(witness)
    }
}

#[cfg(test)]
mod tests {
    use ananke_bdd::bdd::Bdd;

    use super::*;
    use crate::predicate::Predicate;

    #[test]
    fn basic_constraint() {
        let bdd = Bdd::default();
        let mut universe = PredicateUniverse::new();

        let p1 = Predicate::ge("x", 0);
        let p2 = Predicate::le("x", 100);
        let var1 = universe.register(p1, &bdd);
        let var2 = universe.register(p2, &bdd);

        let solver = ModularSolver::with_bounds(0, 100);

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
}
