//! Interval-based constraint solver.
//!
//! Handles constraints of the form `x op constant` using interval arithmetic.

use std::collections::HashMap;

use ananke_bdd::types::Var;

use super::core::{ConstraintSolver, SolveResult, Witness};
use crate::predicate::{CompareOp, Operand, PredicateUniverse};

/// Internal interval representation for the theory solver.
///
/// Note: This is different from [`domain::Interval`](crate::domain::Interval).
/// This struct is optimized for constraint solving and includes an `excluded`
/// field for handling `!=` constraints.
#[derive(Debug, Clone, Copy)]
pub struct Interval {
    pub min: i64,
    pub max: i64,
    /// Value excluded from the interval (for `!=` constraints).
    pub excluded: Option<i64>,
}

impl Interval {
    pub fn new(min: i64, max: i64) -> Self {
        Self { min, max, excluded: None }
    }

    pub fn is_empty(&self) -> bool {
        self.min > self.max
    }

    pub fn intersect(&self, other: &Interval) -> Interval {
        Interval {
            min: self.min.max(other.min),
            max: self.max.min(other.max),
            excluded: self.excluded.or(other.excluded),
        }
    }

    pub fn pick_value(&self) -> Option<i64> {
        if self.is_empty() {
            return None;
        }
        let mid = self.min.saturating_add(self.max) / 2;
        if self.excluded != Some(mid) {
            return Some(mid);
        }
        if self.excluded != Some(self.min) {
            return Some(self.min);
        }
        if self.excluded != Some(self.max) {
            return Some(self.max);
        }
        None
    }

    pub fn constrain(&self, op: CompareOp, constant: i64, positive: bool) -> Interval {
        let effective_op = if positive { op } else { op.negate() };

        match effective_op {
            CompareOp::Lt => self.intersect(&Interval::new(i64::MIN / 2, constant - 1)),
            CompareOp::Le => self.intersect(&Interval::new(i64::MIN / 2, constant)),
            CompareOp::Gt => self.intersect(&Interval::new(constant + 1, i64::MAX / 2)),
            CompareOp::Ge => self.intersect(&Interval::new(constant, i64::MAX / 2)),
            CompareOp::Eq => self.intersect(&Interval::new(constant, constant)),
            CompareOp::Ne => {
                let mut result = *self;
                result.excluded = Some(constant);
                result
            }
        }
    }
}

/// Interval-based constraint solver for linear integer arithmetic.
///
/// Handles constraints of the form `x op constant` where `op` is a comparison
/// operator. Uses interval arithmetic to track bounds on each variable.
///
/// # Supported Constraints
///
/// - `x < c`, `x <= c`, `x > c`, `x >= c`
/// - `x == c`, `x != c`
///
/// # Limitations
///
/// - Cannot handle variable-to-variable constraints (`x < y`)
/// - Returns [`SolveResult::Unknown`] for unsupported constraint forms
///
/// # Example
///
/// ```rust
/// use std::collections::HashMap;
/// use ananke_bdd::bdd::Bdd;
/// use tbdd_pbt::predicate::{Predicate, PredicateUniverse};
/// use tbdd_pbt::theory::{ConstraintSolver, IntervalSolver, SolveResult};
///
/// let bdd = Bdd::default();
/// let mut universe = PredicateUniverse::new();
///
/// let var1 = universe.register(Predicate::ge("x", 0), &bdd);
/// let var2 = universe.register(Predicate::lt("x", 10), &bdd);
///
/// let solver = IntervalSolver::with_bounds(-100, 100);
/// let mut assignments = HashMap::new();
/// assignments.insert(var1, true);
/// assignments.insert(var2, true);
///
/// match solver.solve(&assignments, &universe) {
///     SolveResult::Sat(w) => assert!(w.get("x").unwrap() >= 0),
///     _ => panic!("Expected Sat"),
/// }
/// ```
pub struct IntervalSolver {
    pub(crate) default_min: i64,
    pub(crate) default_max: i64,
}

impl Default for IntervalSolver {
    fn default() -> Self {
        Self::new()
    }
}

impl IntervalSolver {
    /// Create an interval solver with default bounds `[-1000, 1000]`.
    pub fn new() -> Self {
        Self {
            default_min: -1000,
            default_max: 1000,
        }
    }

    /// Create an interval solver with custom default bounds.
    ///
    /// Variables start with interval `[min, max]` before any constraints.
    pub fn with_bounds(min: i64, max: i64) -> Self {
        Self {
            default_min: min,
            default_max: max,
        }
    }
}

impl ConstraintSolver for IntervalSolver {
    /// Solve constraints using interval abstract interpretation.
    ///
    /// # Algorithm
    ///
    /// Uses interval arithmetic to track bounds on integer variables.
    /// Each variable `x` is abstracted as an interval `[min, max]`.
    ///
    /// ## Steps
    ///
    /// 1. **Initialize** — Start each variable with `[default_min, default_max]`.
    ///
    /// 2. **Propagate constraints** — For each predicate `(var op const = value)`:
    ///    - If `value = false`, negate the operator (`<` becomes `>=`).
    ///    - Intersect the interval:
    ///      | Constraint | Intersection       |
    ///      |------------|--------------------|
    ///      | `x < c`    | `(-∞, c-1]`        |
    ///      | `x <= c`   | `(-∞, c]`          |
    ///      | `x > c`    | `[c+1, +∞)`        |
    ///      | `x >= c`   | `[c, +∞)`          |
    ///      | `x == c`   | `[c, c]`           |
    ///      | `x != c`   | mark `c` excluded  |
    ///
    /// 3. **Check feasibility** — If any interval is empty (`min > max`), return `Unsat`.
    ///
    /// 4. **Generate witness** — Pick a concrete value from each interval (midpoint).
    ///
    /// # Properties
    ///
    /// - **Sound** — Never returns `Sat` for unsatisfiable constraints.
    /// - **Incomplete** — May return `Unknown` for variable RHS (use [`RelationalSolver`](super::RelationalSolver)).
    /// - **Efficient** — O(n) where n = number of assignments.
    fn solve(&self, assignments: &HashMap<Var, bool>, universe: &PredicateUniverse) -> SolveResult {
        // Step 1: Initialize interval map for each variable
        let mut intervals: HashMap<String, Interval> = HashMap::new();

        // Step 2: Process each predicate assignment and refine intervals
        for (&bdd_var, &value) in assignments {
            // Look up the predicate corresponding to this BDD variable
            let Some(predicate) = universe.get_predicate(bdd_var) else {
                continue;
            };

            // We only handle constant RHS; variable RHS requires RelationalSolver
            let Operand::Const(constant) = predicate.rhs else {
                return SolveResult::Unknown;
            };

            // Get or create interval for this variable
            let var_name = &predicate.lhs.0;
            let interval = intervals
                .entry(var_name.clone())
                .or_insert_with(|| Interval::new(self.default_min, self.default_max));

            // Apply constraint: if value=false, the predicate is negated
            // e.g., if predicate is "x < 10" and value=false, then x >= 10
            *interval = interval.constrain(predicate.op, constant, value);

            // Step 3: Early termination if interval becomes empty
            if interval.is_empty() {
                return SolveResult::Unsat;
            }
        }

        // Step 4: Generate witness by picking concrete values from each interval
        let mut witness = Witness::new();
        for (var, interval) in &intervals {
            match interval.pick_value() {
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
    fn simple_bounds() {
        let bdd = Bdd::default();
        let mut universe = PredicateUniverse::new();

        let p1 = Predicate::lt("x", 10);
        let var1 = universe.register(p1, &bdd);

        let p2 = Predicate::ge("x", 0);
        let var2 = universe.register(p2, &bdd);

        let solver = IntervalSolver::new();

        let mut assignments = HashMap::new();
        assignments.insert(var1, true);
        assignments.insert(var2, true);

        match solver.solve(&assignments, &universe) {
            SolveResult::Sat(witness) => {
                let x = witness.get("x").unwrap();
                assert!(x >= 0 && x < 10, "x = {} should be in [0, 10)", x);
            }
            other => panic!("Expected Sat, got {:?}", other),
        }
    }

    #[test]
    fn unsat_contradiction() {
        let bdd = Bdd::default();
        let mut universe = PredicateUniverse::new();

        let p1 = Predicate::lt("x", 5);
        let var1 = universe.register(p1, &bdd);

        let p2 = Predicate::ge("x", 11);
        let var2 = universe.register(p2, &bdd);

        let solver = IntervalSolver::new();

        let mut assignments = HashMap::new();
        assignments.insert(var1, true);
        assignments.insert(var2, true);

        assert!(matches!(solver.solve(&assignments, &universe), SolveResult::Unsat));
    }

    #[test]
    fn negation() {
        let bdd = Bdd::default();
        let mut universe = PredicateUniverse::new();

        let p1 = Predicate::lt("x", 10);
        let var1 = universe.register(p1, &bdd);

        let solver = IntervalSolver::new();

        let mut assignments = HashMap::new();
        assignments.insert(var1, false); // NOT(x < 10) => x >= 10

        match solver.solve(&assignments, &universe) {
            SolveResult::Sat(witness) => {
                let x = witness.get("x").unwrap();
                assert!(x >= 10, "x = {} should be >= 10", x);
            }
            other => panic!("Expected Sat, got {:?}", other),
        }
    }

    #[test]
    fn equality_constraint() {
        let bdd = Bdd::default();
        let mut universe = PredicateUniverse::new();

        let p1 = Predicate::eq("x", 42);
        let var1 = universe.register(p1, &bdd);

        let solver = IntervalSolver::new();

        let mut assignments = HashMap::new();
        assignments.insert(var1, true);

        match solver.solve(&assignments, &universe) {
            SolveResult::Sat(witness) => {
                let x = witness.get("x").unwrap();
                assert_eq!(x, 42, "x should equal 42");
            }
            other => panic!("Expected Sat, got {:?}", other),
        }
    }

    #[test]
    fn not_equal_constraint() {
        let bdd = Bdd::default();
        let mut universe = PredicateUniverse::new();

        let p1 = Predicate::ne("x", 0);
        let var1 = universe.register(p1, &bdd);

        let solver = IntervalSolver::with_bounds(-10, 10);

        let mut assignments = HashMap::new();
        assignments.insert(var1, true);

        match solver.solve(&assignments, &universe) {
            SolveResult::Sat(witness) => {
                let x = witness.get("x").unwrap();
                assert_ne!(x, 0, "x should not equal 0");
            }
            other => panic!("Expected Sat, got {:?}", other),
        }
    }

    #[test]
    fn multiple_variables() {
        let bdd = Bdd::default();
        let mut universe = PredicateUniverse::new();

        let var1 = universe.register(Predicate::gt("x", 0), &bdd);
        let var2 = universe.register(Predicate::lt("y", 100), &bdd);
        let var3 = universe.register(Predicate::ge("z", -50), &bdd);

        let solver = IntervalSolver::with_bounds(-100, 200);

        let mut assignments = HashMap::new();
        assignments.insert(var1, true);
        assignments.insert(var2, true);
        assignments.insert(var3, true);

        match solver.solve(&assignments, &universe) {
            SolveResult::Sat(witness) => {
                let x = witness.get("x").unwrap();
                let y = witness.get("y").unwrap();
                let z = witness.get("z").unwrap();
                assert!(x > 0, "x = {} should be > 0", x);
                assert!(y < 100, "y = {} should be < 100", y);
                assert!(z >= -50, "z = {} should be >= -50", z);
            }
            other => panic!("Expected Sat, got {:?}", other),
        }
    }

    #[test]
    fn custom_bounds() {
        let solver = IntervalSolver::with_bounds(0, 100);
        let _bdd = Bdd::default();
        let universe = PredicateUniverse::new();

        // No constraints - should use default bounds
        let assignments = HashMap::new();

        // This should work since we have no constraints
        assert!(matches!(solver.solve(&assignments, &universe), SolveResult::Sat(_)));
    }

    #[test]
    fn interval_is_empty() {
        assert!(Interval::new(10, 5).is_empty());
        assert!(!Interval::new(5, 10).is_empty());
        assert!(!Interval::new(5, 5).is_empty());
    }

    #[test]
    fn interval_intersect() {
        let a = Interval::new(0, 10);
        let b = Interval::new(5, 15);
        let c = a.intersect(&b);
        assert_eq!(c.min, 5);
        assert_eq!(c.max, 10);
    }

    #[test]
    fn interval_intersect_empty() {
        let a = Interval::new(0, 5);
        let b = Interval::new(10, 15);
        let c = a.intersect(&b);
        assert!(c.is_empty());
    }

    #[test]
    fn interval_pick_value_simple() {
        let interval = Interval::new(0, 100);
        let val = interval.pick_value().unwrap();
        assert!(val >= 0 && val <= 100);
    }

    #[test]
    fn interval_pick_value_single() {
        let interval = Interval::new(42, 42);
        assert_eq!(interval.pick_value(), Some(42));
    }

    #[test]
    fn interval_pick_value_with_excluded() {
        let mut interval = Interval::new(0, 2);
        interval.excluded = Some(1); // Exclude midpoint
        let val = interval.pick_value().unwrap();
        assert!(val == 0 || val == 2);
    }

    #[test]
    fn interval_constrain_lt() {
        let interval = Interval::new(-100, 100);
        let constrained = interval.constrain(CompareOp::Lt, 50, true);
        assert!(constrained.max < 50);
    }

    #[test]
    fn interval_constrain_ge_negated() {
        let interval = Interval::new(-100, 100);
        // NOT(x >= 50) => x < 50
        let constrained = interval.constrain(CompareOp::Ge, 50, false);
        assert!(constrained.max < 50);
    }
}
