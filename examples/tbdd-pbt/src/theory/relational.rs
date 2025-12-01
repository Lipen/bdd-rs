//! Relational constraint solver using difference bound matrices.
//!
//! Handles constraints involving variable-to-variable comparisons.

use std::collections::{HashMap, HashSet};

use bdd_rs::types::Var;

use super::core::{ConstraintSolver, SolveResult, Witness};
use super::interval::Interval;
use crate::predicate::{CompareOp, Operand, PredicateUniverse};

/// Constraint edge in the difference bound graph.
#[derive(Debug, Clone)]
struct DifferenceConstraint {
    from: String,
    to: String,
    /// Upper bound: to - from <= bound
    bound: i64,
}

/// Default offset for converting Bellman-Ford distances to witness values.
///
/// Bellman-Ford produces relative distances that may be negative or zero.
/// This offset shifts them into a positive range for more readable witnesses.
/// For example, distances `{x: 0, y: -1}` become witnesses `{x: 50, y: 49}`.
const WITNESS_OFFSET: i64 = 50;

/// Relational solver using difference bound matrix (DBM) approach.
///
/// Handles constraints involving comparisons between variables:
/// - `x < y`  → `y - x >= 1`
/// - `x <= y` → `y - x >= 0`
/// - `x == y` → `x - y = 0`
///
/// Uses Bellman-Ford algorithm to detect negative cycles (unsatisfiability).
///
/// # Example
///
/// ```rust
/// use std::collections::HashMap;
/// use bdd_rs::bdd::Bdd;
/// use tbdd_pbt::predicate::{Predicate, PredicateUniverse};
/// use tbdd_pbt::theory::{ConstraintSolver, RelationalSolver, SolveResult};
///
/// let bdd = Bdd::default();
/// let mut universe = PredicateUniverse::new();
///
/// // Register x < y
/// let var1 = universe.register(Predicate::lt("x", "y"), &bdd);
///
/// let solver = RelationalSolver::new();
/// let mut assignments = HashMap::new();
/// assignments.insert(var1, true);
///
/// match solver.solve(&assignments, &universe) {
///     SolveResult::Sat(w) => {
///         assert!(w.get("x").unwrap() < w.get("y").unwrap());
///     }
///     _ => panic!("Expected Sat"),
/// }
/// ```
pub struct RelationalSolver {
    default_min: i64,
    default_max: i64,
}

impl Default for RelationalSolver {
    fn default() -> Self {
        Self::new()
    }
}

impl RelationalSolver {
    /// Create a relational solver with default bounds `[-1000, 1000]`.
    pub fn new() -> Self {
        Self {
            default_min: -1000,
            default_max: 1000,
        }
    }

    /// Create a relational solver with custom default bounds.
    pub fn with_bounds(min: i64, max: i64) -> Self {
        Self {
            default_min: min,
            default_max: max,
        }
    }

    /// Collect all variables and constraints from assignments.
    fn collect_constraints(
        &self,
        assignments: &HashMap<Var, bool>,
        universe: &PredicateUniverse,
    ) -> (
        HashSet<String>,
        Vec<DifferenceConstraint>,
        HashMap<String, Interval>,
        Vec<(String, String)>,
    ) {
        let mut variables = HashSet::new();
        let mut constraints = Vec::new();
        let mut intervals: HashMap<String, Interval> = HashMap::new();
        let mut ne_constraints: Vec<(String, String)> = Vec::new();

        for (&bdd_var, &value) in assignments {
            let Some(predicate) = universe.get_predicate(bdd_var) else {
                continue;
            };

            let lhs = &predicate.lhs.0;
            variables.insert(lhs.clone());

            match &predicate.rhs {
                Operand::Const(constant) => {
                    // Single variable constraint: apply to interval
                    let interval = intervals
                        .entry(lhs.clone())
                        .or_insert_with(|| Interval::new(self.default_min, self.default_max));
                    *interval = interval.constrain(predicate.op, *constant, value);
                }
                Operand::Var(rhs_var) => {
                    let rhs = &rhs_var.0;
                    variables.insert(rhs.clone());

                    // Relational constraint: convert to difference constraints
                    let effective_op = if value { predicate.op } else { predicate.op.negate() };
                    match effective_op {
                        CompareOp::Lt => {
                            // x < y → y - x >= 1 → x - y <= -1
                            constraints.push(DifferenceConstraint {
                                from: rhs.clone(),
                                to: lhs.clone(),
                                bound: -1,
                            });
                        }
                        CompareOp::Le => {
                            // x <= y → y - x >= 0 → x - y <= 0
                            constraints.push(DifferenceConstraint {
                                from: rhs.clone(),
                                to: lhs.clone(),
                                bound: 0,
                            });
                        }
                        CompareOp::Gt => {
                            // x > y → x - y >= 1 → y - x <= -1
                            constraints.push(DifferenceConstraint {
                                from: lhs.clone(),
                                to: rhs.clone(),
                                bound: -1,
                            });
                        }
                        CompareOp::Ge => {
                            // x >= y → x - y >= 0 → y - x <= 0
                            constraints.push(DifferenceConstraint {
                                from: lhs.clone(),
                                to: rhs.clone(),
                                bound: 0,
                            });
                        }
                        CompareOp::Eq => {
                            // x == y → x - y = 0 (both directions)
                            constraints.push(DifferenceConstraint {
                                from: lhs.clone(),
                                to: rhs.clone(),
                                bound: 0,
                            });
                            constraints.push(DifferenceConstraint {
                                from: rhs.clone(),
                                to: lhs.clone(),
                                bound: 0,
                            });
                        }
                        CompareOp::Ne => {
                            // x != y - track separately for witness adjustment
                            ne_constraints.push((lhs.clone(), rhs.clone()));
                        }
                    }
                }
            }
        }

        (variables, constraints, intervals, ne_constraints)
    }

    /// Bellman-Ford algorithm to find shortest paths and detect negative cycles.
    fn bellman_ford(&self, variables: &HashSet<String>, constraints: &[DifferenceConstraint]) -> Option<HashMap<String, i64>> {
        let mut distances: HashMap<String, i64> = HashMap::new();

        // Initialize with source (virtual node at 0)
        for var in variables {
            distances.insert(var.clone(), 0);
        }

        // Relax edges |V| - 1 times
        for _ in 0..variables.len() {
            let mut changed = false;
            for c in constraints {
                if let Some(&from_dist) = distances.get(&c.from) {
                    let new_dist = from_dist.saturating_add(c.bound);
                    let to_dist = distances.entry(c.to.clone()).or_insert(i64::MAX);
                    if new_dist < *to_dist {
                        *to_dist = new_dist;
                        changed = true;
                    }
                }
            }
            if !changed {
                break;
            }
        }

        // Check for negative cycles
        for c in constraints {
            if let (Some(&from_dist), Some(&to_dist)) = (distances.get(&c.from), distances.get(&c.to)) {
                if from_dist.saturating_add(c.bound) < to_dist {
                    return None; // Negative cycle detected
                }
            }
        }

        Some(distances)
    }
}

impl ConstraintSolver for RelationalSolver {
    /// Solve constraints involving inter-variable comparisons.
    ///
    /// # Algorithm
    ///
    /// Uses a **Difference Bound Matrix (DBM)** approach with Bellman-Ford.
    /// Converts relational constraints to difference bounds:
    ///
    /// | Relation | Difference Bound           |
    /// |----------|----------------------------|
    /// | `x < y`  | `x - y <= -1`              |
    /// | `x <= y` | `x - y <= 0`               |
    /// | `x > y`  | `y - x <= -1`              |
    /// | `x >= y` | `y - x <= 0`               |
    /// | `x == y` | `x - y <= 0 ∧ y - x <= 0`  |
    ///
    /// ## Steps
    ///
    /// 1. **Collect constraints** — Parse predicates into difference, interval, and `!=` constraints.
    ///
    /// 2. **Build constraint graph** — Nodes are variables; edge `(u → v, w)` means `v - u <= w`.
    ///
    /// 3. **Run Bellman-Ford** — Find shortest paths from virtual source.
    ///    - Negative cycle → `Unsat` (contradictory constraints like `x < y < z < x`).
    ///    - Otherwise → distances encode a valid assignment.
    ///
    /// 4. **Generate witness** — Combine distances with interval bounds, offset by [`WITNESS_OFFSET`].
    ///
    /// 5. **Post-adjust** — Fix any `!=` violations.
    ///
    /// # Example
    ///
    /// ```text
    /// Given: x < y, y < z
    /// Edges: (y → x, -1), (z → y, -1)  [meaning x - y <= -1, y - z <= -1]
    /// Bellman-Ford: dist = {x: -2, y: -1, z: 0}
    /// After offset: x = 48, y = 49, z = 50
    /// Verify: 48 < 49 < 50 ✓
    /// ```
    fn solve(&self, assignments: &HashMap<Var, bool>, universe: &PredicateUniverse) -> SolveResult {
        // Step 1: Parse assignments into different constraint types
        let (variables, constraints, intervals, ne_constraints) = self.collect_constraints(assignments, universe);

        // Step 2: Check interval feasibility (quick rejection)
        for interval in intervals.values() {
            if interval.is_empty() {
                return SolveResult::Unsat;
            }
        }

        // Step 3: Run Bellman-Ford to check satisfiability and get relative distances
        // A negative cycle means the constraints are contradictory (e.g., x < y < z < x)
        let distances = if !constraints.is_empty() {
            match self.bellman_ford(&variables, &constraints) {
                Some(d) => d,
                None => return SolveResult::Unsat, // Negative cycle = contradiction
            }
        } else {
            HashMap::new()
        };

        // Step 4: Generate witness combining Bellman-Ford distances with intervals
        let mut witness = Witness::new();

        // Bellman-Ford distances give relative orderings (e.g., if x < y, dist[x] < dist[y])
        // We add an offset to get positive, meaningful values
        for var in &variables {
            let base_value = distances.get(var).copied().unwrap_or(0);

            let value = if let Some(interval) = intervals.get(var) {
                // If we have interval bounds, prefer values within them
                interval.pick_value().unwrap_or(base_value)
            } else {
                // For pure relational constraints, offset the Bellman-Ford distance
                // so that x < y results in positive distinct values like x=49, y=50
                base_value + WITNESS_OFFSET
            };
            witness.values.insert(var.clone(), value);
        }

        // Step 5a: Adjust values to ensure all difference constraints are satisfied
        // This handles cases where interval picking might have violated ordering
        for c in &constraints {
            let from_val = witness.values.get(&c.from).copied().unwrap_or(0);
            let to_val = witness.values.get(&c.to).copied().unwrap_or(0);

            // Constraint: to - from <= bound
            // Example: for x < y, we have from=y, to=x, bound=-1
            // This means x - y <= -1, i.e., x < y
            if to_val - from_val > c.bound {
                // Violation! Adjust to_val to satisfy the constraint
                let new_to = from_val + c.bound;
                witness.values.insert(c.to.clone(), new_to);
            }
        }

        // Handle != constraints by adjusting witness if needed
        for (var1, var2) in &ne_constraints {
            let v1 = witness.values.get(var1).copied().unwrap_or(0);
            let v2 = witness.values.get(var2).copied().unwrap_or(0);
            if v1 == v2 {
                // They're equal but shouldn't be - adjust one of them
                witness.values.insert(var1.clone(), v1 + 1);
            }
        }

        SolveResult::Sat(witness)
    }
}

#[cfg(test)]
mod tests {
    use bdd_rs::bdd::Bdd;

    use super::*;
    use crate::predicate::Predicate;

    #[test]
    fn x_less_than_y() {
        let bdd = Bdd::default();
        let mut universe = PredicateUniverse::new();

        let p1 = Predicate::lt("x", "y");
        let var1 = universe.register(p1, &bdd);

        let solver = RelationalSolver::with_bounds(0, 100);

        let mut assignments = HashMap::new();
        assignments.insert(var1, true);

        match solver.solve(&assignments, &universe) {
            SolveResult::Sat(witness) => {
                let x = witness.get("x").unwrap();
                let y = witness.get("y").unwrap();
                assert!(x < y, "x={} should be < y={}", x, y);
            }
            other => panic!("Expected Sat, got {:?}", other),
        }
    }

    #[test]
    fn x_equals_y() {
        let bdd = Bdd::default();
        let mut universe = PredicateUniverse::new();

        let p1 = Predicate::eq("x", "y");
        let var1 = universe.register(p1, &bdd);

        let solver = RelationalSolver::with_bounds(0, 100);

        let mut assignments = HashMap::new();
        assignments.insert(var1, true);

        match solver.solve(&assignments, &universe) {
            SolveResult::Sat(witness) => {
                let x = witness.get("x").unwrap();
                let y = witness.get("y").unwrap();
                assert_eq!(x, y, "x={} should equal y={}", x, y);
            }
            other => panic!("Expected Sat, got {:?}", other),
        }
    }

    #[test]
    fn x_greater_than_y() {
        let bdd = Bdd::default();
        let mut universe = PredicateUniverse::new();

        // x < y = false, x == y = false => x > y
        let p1 = Predicate::lt("x", "y");
        let p2 = Predicate::eq("x", "y");
        let var1 = universe.register(p1, &bdd);
        let var2 = universe.register(p2, &bdd);

        let solver = RelationalSolver::with_bounds(0, 100);

        let mut assignments = HashMap::new();
        assignments.insert(var1, false); // NOT(x < y) => x >= y
        assignments.insert(var2, false); // NOT(x == y) => x != y
                                         // Combined: x > y

        match solver.solve(&assignments, &universe) {
            SolveResult::Sat(witness) => {
                let x = witness.get("x").unwrap();
                let y = witness.get("y").unwrap();
                assert!(x > y, "x={} should be > y={}", x, y);
            }
            other => panic!("Expected Sat, got {:?}", other),
        }
    }

    #[test]
    fn chain_constraints() {
        let bdd = Bdd::default();
        let mut universe = PredicateUniverse::new();

        // x < y and y < z => x < z
        let p1 = Predicate::lt("x", "y");
        let p2 = Predicate::lt("y", "z");
        let var1 = universe.register(p1, &bdd);
        let var2 = universe.register(p2, &bdd);

        let solver = RelationalSolver::with_bounds(0, 100);

        let mut assignments = HashMap::new();
        assignments.insert(var1, true);
        assignments.insert(var2, true);

        match solver.solve(&assignments, &universe) {
            SolveResult::Sat(witness) => {
                let x = witness.get("x").unwrap();
                let y = witness.get("y").unwrap();
                let z = witness.get("z").unwrap();
                assert!(x < y, "x={} should be < y={}", x, y);
                assert!(y < z, "y={} should be < z={}", y, z);
                assert!(x < z, "transitivity: x={} should be < z={}", x, z);
            }
            other => panic!("Expected Sat, got {:?}", other),
        }
    }

    #[test]
    fn unsat_cycle() {
        let bdd = Bdd::default();
        let mut universe = PredicateUniverse::new();

        // x < y, y < z, z < x => cycle => UNSAT
        let p1 = Predicate::lt("x", "y");
        let p2 = Predicate::lt("y", "z");
        let p3 = Predicate::lt("z", "x");
        let var1 = universe.register(p1, &bdd);
        let var2 = universe.register(p2, &bdd);
        let var3 = universe.register(p3, &bdd);

        let solver = RelationalSolver::with_bounds(0, 100);

        let mut assignments = HashMap::new();
        assignments.insert(var1, true);
        assignments.insert(var2, true);
        assignments.insert(var3, true);

        assert!(matches!(solver.solve(&assignments, &universe), SolveResult::Unsat));
    }
}
