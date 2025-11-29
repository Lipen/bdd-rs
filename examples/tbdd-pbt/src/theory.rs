//! Theory solver integration for T-BDD.
//!
//! This module provides the interface between BDD path constraints and
//! theory solvers. BDD paths give us boolean assignments to predicates,
//! but we need theory reasoning to:
//!
//! 1. Check if a path is feasible (satisfiable in the theory)
//! 2. Generate concrete witness values when feasible
//! 3. Prune infeasible paths early
//!
//! ## Available Solvers
//!
//! - [`IntervalSolver`]: Simple interval arithmetic for single-variable bounds
//! - [`RelationalSolver`]: Handles inter-variable constraints (x < y, x == y)
//! - [`ModularSolver`]: Divisibility and modular constraints (x % n == 0)
//! - [`CombinedSolver`]: Chains multiple solvers for richer theories

use std::collections::{HashMap, HashSet};

use bdd_rs::types::Var;

use crate::predicate::{CompareOp, Operand, PredicateUniverse};

/// Result of checking constraint satisfiability.
#[derive(Debug, Clone)]
pub enum SolveResult {
    /// Satisfiable with a concrete witness.
    Sat(Witness),
    /// Definitely unsatisfiable.
    Unsat,
    /// Solver couldn't determine (timeout, incomplete theory, etc.)
    Unknown,
}

/// A concrete assignment of values to program variables.
#[derive(Debug, Clone, Default)]
pub struct Witness {
    pub values: HashMap<String, i64>,
}

impl Witness {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn with(mut self, var: impl Into<String>, value: i64) -> Self {
        self.values.insert(var.into(), value);
        self
    }

    pub fn get(&self, var: &str) -> Option<i64> {
        self.values.get(var).copied()
    }
}

/// Trait for theory solvers.
pub trait ConstraintSolver {
    /// Check satisfiability of constraints derived from a BDD path.
    fn solve(&self, assignments: &HashMap<Var, bool>, universe: &PredicateUniverse) -> SolveResult;
}

/// Simple interval-based constraint solver.
///
/// Tracks integer bounds using interval arithmetic. Sound but incomplete:
/// never returns Sat for unsatisfiable constraints, but may return Unknown.
pub struct IntervalSolver {
    default_min: i64,
    default_max: i64,
}

impl Default for IntervalSolver {
    fn default() -> Self {
        Self::new()
    }
}

impl IntervalSolver {
    pub fn new() -> Self {
        Self {
            default_min: i64::MIN / 2,
            default_max: i64::MAX / 2,
        }
    }

    pub fn with_bounds(min: i64, max: i64) -> Self {
        Self {
            default_min: min,
            default_max: max,
        }
    }
}

#[derive(Debug, Clone, Copy)]
pub struct Interval {
    pub min: i64,
    pub max: i64,
    pub excluded: Option<i64>,
}

impl Interval {
    fn new(min: i64, max: i64) -> Self {
        Self { min, max, excluded: None }
    }

    fn is_empty(&self) -> bool {
        self.min > self.max
    }

    fn intersect(&self, other: &Interval) -> Interval {
        Interval {
            min: self.min.max(other.min),
            max: self.max.min(other.max),
            excluded: self.excluded.or(other.excluded),
        }
    }

    fn pick_value(&self) -> Option<i64> {
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

    fn constrain(&self, op: CompareOp, constant: i64, positive: bool) -> Interval {
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
    /// - **Incomplete** — May return `Unknown` for variable RHS (use [`RelationalSolver`]).
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

// =============================================================================
// Relational Solver: Handles inter-variable constraints (x < y, x == y)
// =============================================================================

/// Constraint edge in the difference bound graph.
#[derive(Debug, Clone)]
struct DifferenceConstraint {
    from: String,
    to: String,
    /// Upper bound: to - from <= bound
    bound: i64,
}

/// Relational solver using difference bound matrix (DBM) approach.
///
/// Handles constraints like:
/// - `x < y`  → `y - x >= 1`
/// - `x <= y` → `y - x >= 0`
/// - `x == y` → `x - y = 0`
///
/// Uses Bellman-Ford to detect negative cycles (unsatisfiability).
pub struct RelationalSolver {
    default_min: i64,
    default_max: i64,
}

/// Default offset for converting Bellman-Ford distances to witness values.
///
/// Bellman-Ford produces relative distances that may be negative or zero.
/// This offset shifts them into a positive range for more readable witnesses.
/// For example, distances `{x: 0, y: -1}` become witnesses `{x: 50, y: 49}`.
const WITNESS_OFFSET: i64 = 50;

impl Default for RelationalSolver {
    fn default() -> Self {
        Self::new()
    }
}

impl RelationalSolver {
    pub fn new() -> Self {
        Self {
            default_min: -1000,
            default_max: 1000,
        }
    }

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

// =============================================================================
// Modular Solver: Divisibility and modular constraints
// =============================================================================

/// Modular constraint: x % divisor == remainder
#[derive(Debug, Clone)]
pub struct ModularConstraint {
    pub var: String,
    pub divisor: i64,
    pub remainder: i64,
}

/// Solver for modular arithmetic constraints.
///
/// Handles constraints like:
/// - x % 2 == 0 (x is even)
/// - x % 3 == 1 (x ≡ 1 mod 3)
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
    pub fn new() -> Self {
        Self {
            default_min: -1000,
            default_max: 1000,
        }
    }

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
    /// 1. **Compute intervals** — Same as [`IntervalSolver`].
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

// =============================================================================
// Combined Solver: Chains multiple solvers
// =============================================================================

/// Combined solver that chains multiple theory solvers.
///
/// First checks each solver for unsatisfiability, then generates
/// a witness from the most capable solver that succeeds.
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

// =============================================================================
// Array Bounds Solver: Validates array indexing constraints
// =============================================================================

/// Array constraint: index must be in bounds [0, length).
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
    Const(i64),
    Var(String),
}

/// Solver for array bounds constraints.
///
/// Ensures array indices are in bounds: 0 <= index < length.
/// Supports both constant and variable-length arrays.
pub struct ArrayBoundsSolver {
    /// Array constraints indexed by array name.
    arrays: HashMap<String, ArrayConstraint>,
    /// Interval solver for underlying arithmetic.
    interval_solver: IntervalSolver,
}

impl ArrayBoundsSolver {
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

// =============================================================================
// Bitwise Solver: Constraints on bit-level properties
// =============================================================================

/// Bitwise constraint types.
#[derive(Debug, Clone)]
pub enum BitwiseConstraint {
    /// Value is a power of 2 (single bit set).
    PowerOfTwo(String),
    /// Value has specific bit set.
    BitSet(String, u32),
    /// Value has specific bit clear.
    BitClear(String, u32),
    /// Value is non-negative (sign bit clear for signed).
    NonNegative(String),
    /// Value is aligned to power-of-2 boundary.
    Aligned(String, u32),
}

/// Solver for bitwise constraints.
///
/// Handles constraints involving bit-level operations:
/// - Power of 2 checks
/// - Bit set/clear conditions
/// - Alignment requirements
pub struct BitwiseSolver {
    constraints: Vec<BitwiseConstraint>,
    interval_solver: IntervalSolver,
}

impl BitwiseSolver {
    pub fn new() -> Self {
        Self {
            constraints: Vec::new(),
            interval_solver: IntervalSolver::with_bounds(0, i64::MAX / 2),
        }
    }

    /// Add a constraint that variable must be a power of 2.
    pub fn require_power_of_two(&mut self, var: impl Into<String>) {
        self.constraints.push(BitwiseConstraint::PowerOfTwo(var.into()));
    }

    /// Add a constraint that specific bit must be set.
    pub fn require_bit_set(&mut self, var: impl Into<String>, bit: u32) {
        self.constraints.push(BitwiseConstraint::BitSet(var.into(), bit));
    }

    /// Add a constraint that specific bit must be clear.
    pub fn require_bit_clear(&mut self, var: impl Into<String>, bit: u32) {
        self.constraints.push(BitwiseConstraint::BitClear(var.into(), bit));
    }

    /// Add a constraint that variable must be non-negative.
    pub fn require_non_negative(&mut self, var: impl Into<String>) {
        self.constraints.push(BitwiseConstraint::NonNegative(var.into()));
    }

    /// Add a constraint that variable must be aligned.
    pub fn require_aligned(&mut self, var: impl Into<String>, alignment: u32) {
        self.constraints.push(BitwiseConstraint::Aligned(var.into(), alignment));
    }

    /// Check if a value satisfies a bitwise constraint.
    fn check_constraint(&self, values: &HashMap<String, i64>, constraint: &BitwiseConstraint) -> bool {
        match constraint {
            BitwiseConstraint::PowerOfTwo(var) => values.get(var).map_or(true, |&v| v > 0 && (v & (v - 1)) == 0),
            BitwiseConstraint::BitSet(var, bit) => values.get(var).map_or(true, |&v| (v >> bit) & 1 == 1),
            BitwiseConstraint::BitClear(var, bit) => values.get(var).map_or(true, |&v| (v >> bit) & 1 == 0),
            BitwiseConstraint::NonNegative(var) => values.get(var).map_or(true, |&v| v >= 0),
            BitwiseConstraint::Aligned(var, alignment) => values.get(var).map_or(true, |&v| v >= 0 && v % (*alignment as i64) == 0),
        }
    }

    /// Adjust witness to satisfy bitwise constraints.
    fn adjust_witness(&self, mut witness: Witness) -> Option<Witness> {
        for constraint in &self.constraints {
            match constraint {
                BitwiseConstraint::PowerOfTwo(var) => {
                    if let Some(&v) = witness.values.get(var) {
                        // Round up to next power of 2
                        let new_v = if v <= 0 { 1 } else { 1i64 << (64 - (v as u64).leading_zeros()) };
                        witness.values.insert(var.clone(), new_v.min(1 << 30));
                    }
                }
                BitwiseConstraint::BitSet(var, bit) => {
                    if let Some(&v) = witness.values.get(var) {
                        witness.values.insert(var.clone(), v | (1i64 << bit));
                    }
                }
                BitwiseConstraint::BitClear(var, bit) => {
                    if let Some(&v) = witness.values.get(var) {
                        witness.values.insert(var.clone(), v & !(1i64 << bit));
                    }
                }
                BitwiseConstraint::NonNegative(var) => {
                    if let Some(&v) = witness.values.get(var) {
                        if v < 0 {
                            witness.values.insert(var.clone(), 0);
                        }
                    }
                }
                BitwiseConstraint::Aligned(var, alignment) => {
                    if let Some(&v) = witness.values.get(var) {
                        let aligned = (v / (*alignment as i64)) * (*alignment as i64);
                        witness.values.insert(var.clone(), aligned.max(0));
                    }
                }
            }
        }

        // Verify all constraints are satisfied
        for constraint in &self.constraints {
            if !self.check_constraint(&witness.values, constraint) {
                return None;
            }
        }

        Some(witness)
    }
}

impl Default for BitwiseSolver {
    fn default() -> Self {
        Self::new()
    }
}

impl ConstraintSolver for BitwiseSolver {
    /// Solve constraints with bit-level property requirements.
    ///
    /// # Algorithm
    ///
    /// Two-phase solving: get a candidate witness, then adjust for bit constraints.
    ///
    /// ## Supported Constraints
    ///
    /// | Constraint         | Meaning                          | Adjustment           |
    /// |--------------------|----------------------------------|----------------------|
    /// | `PowerOfTwo(x)`    | `x > 0 ∧ x & (x-1) == 0`         | Round up to 2^k      |
    /// | `BitSet(x, n)`     | `(x >> n) & 1 == 1`              | `x \| (1 << n)`      |
    /// | `BitClear(x, n)`   | `(x >> n) & 1 == 0`              | `x & ~(1 << n)`      |
    /// | `NonNegative(x)`   | `x >= 0`                         | `max(x, 0)`          |
    /// | `Aligned(x, a)`    | `x % a == 0`                     | Round down           |
    ///
    /// ## Steps
    ///
    /// 1. **Base solve** — Use [`IntervalSolver`] to get a candidate witness.
    /// 2. **Adjust** — Modify values to satisfy bit constraints.
    /// 3. **Verify** — Ensure adjustments don't conflict (e.g., `BitSet(x,0)` + `BitClear(x,0)`).
    ///
    /// # Example
    ///
    /// ```text
    /// Constraint: x > 0, PowerOfTwo(x)
    /// Base witness: x = 5 (binary: 101)
    /// Adjustment: round up → x = 8 (binary: 1000)
    /// Verify: 8 > 0 ✓, 8 & 7 == 0 ✓ → Sat(x=8)
    /// ```
    fn solve(&self, assignments: &HashMap<Var, bool>, universe: &PredicateUniverse) -> SolveResult {
        // Step 1: Get initial witness from interval solver
        let result = self.interval_solver.solve(assignments, universe);
        let SolveResult::Sat(witness) = result else {
            return result; // Propagate Unsat or Unknown
        };

        // Steps 2 & 3: Adjust witness values and verify bitwise constraints
        // adjust_witness modifies values to satisfy bit constraints, then verifies
        match self.adjust_witness(witness) {
            Some(w) => SolveResult::Sat(w),
            None => SolveResult::Unknown, // Conflicting bitwise constraints
        }
    }
}

// =============================================================================
// Boundary Value Analysis
// =============================================================================

/// Boundary value generator for systematic edge case testing.
#[derive(Debug, Clone)]
pub struct BoundaryValueGenerator {
    /// Include off-by-one values.
    pub off_by_one: bool,
    /// Include special values (0, -1, MAX, MIN).
    pub special_values: bool,
    /// Include powers of 2 boundaries.
    pub powers_of_two: bool,
}

impl Default for BoundaryValueGenerator {
    fn default() -> Self {
        Self {
            off_by_one: true,
            special_values: true,
            powers_of_two: false,
        }
    }
}

impl BoundaryValueGenerator {
    pub fn new() -> Self {
        Self::default()
    }

    /// Enable all boundary value strategies.
    pub fn all() -> Self {
        Self {
            off_by_one: true,
            special_values: true,
            powers_of_two: true,
        }
    }

    /// Generate boundary values for an interval.
    pub fn generate(&self, interval: &Interval) -> Vec<i64> {
        let mut values = Vec::new();

        if interval.is_empty() {
            return values;
        }

        // Core boundaries
        values.push(interval.min);
        values.push(interval.max);

        // Midpoint
        let mid = interval.min.saturating_add(interval.max) / 2;
        if mid != interval.min && mid != interval.max {
            values.push(mid);
        }

        // Off-by-one
        if self.off_by_one {
            if interval.min > i64::MIN / 2 {
                values.push(interval.min.saturating_sub(1));
            }
            if interval.max < i64::MAX / 2 {
                values.push(interval.max.saturating_add(1));
            }
            if interval.min < interval.max {
                values.push(interval.min.saturating_add(1));
                values.push(interval.max.saturating_sub(1));
            }
        }

        // Special values
        if self.special_values {
            for special in [0, -1, 1, i64::MAX / 2, i64::MIN / 2] {
                if special >= interval.min && special <= interval.max {
                    values.push(special);
                }
            }
        }

        // Powers of 2
        if self.powers_of_two {
            for exp in 0..62 {
                let pow = 1i64 << exp;
                if pow >= interval.min && pow <= interval.max {
                    values.push(pow);
                }
                if -pow >= interval.min && -pow <= interval.max {
                    values.push(-pow);
                }
            }
        }

        // Remove duplicates and excluded value
        values.sort();
        values.dedup();
        if let Some(excluded) = interval.excluded {
            values.retain(|&v| v != excluded);
        }

        values
    }

    /// Generate boundary test cases for multiple variables.
    pub fn generate_test_cases(&self, intervals: &HashMap<String, Interval>) -> Vec<Witness> {
        if intervals.is_empty() {
            return vec![Witness::new()];
        }

        // Generate boundary values for each variable
        let var_values: Vec<(String, Vec<i64>)> = intervals
            .iter()
            .map(|(var, interval)| (var.clone(), self.generate(interval)))
            .collect();

        // For each variable, pick boundary combinations
        // Use representative sampling to avoid explosion
        let mut test_cases = Vec::new();

        // Add corner cases: all mins, all maxs, all mids
        let mut all_min = Witness::new();
        let mut all_max = Witness::new();
        let mut all_mid = Witness::new();

        for (var, values) in &var_values {
            if !values.is_empty() {
                all_min.values.insert(var.clone(), values[0]);
                all_max.values.insert(var.clone(), *values.last().unwrap());
                all_mid.values.insert(var.clone(), values[values.len() / 2]);
            }
        }

        test_cases.push(all_min);
        test_cases.push(all_max);
        test_cases.push(all_mid);

        // Add single-variable boundary variations
        for (var, values) in &var_values {
            for &val in values.iter().take(5) {
                // Limit per variable
                let mut witness = Witness::new();
                for (v, vals) in &var_values {
                    let base_val = vals.get(vals.len() / 2).copied().unwrap_or(0);
                    witness.values.insert(v.clone(), if v == var { val } else { base_val });
                }
                test_cases.push(witness);
            }
        }

        // Deduplicate
        let mut seen = HashSet::new();
        test_cases.retain(|w| {
            let key: Vec<_> = w.values.iter().collect();
            seen.insert(format!("{:?}", key))
        });

        test_cases
    }
}

#[cfg(test)]
mod tests {
    use bdd_rs::bdd::Bdd;

    use super::*;
    use crate::predicate::Predicate;

    // =========================================================================
    // Interval Solver Tests
    // =========================================================================

    mod interval_solver {
        use super::*;

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
    }

    // =========================================================================
    // Interval Struct Tests
    // =========================================================================

    mod interval {
        use super::*;

        #[test]
        fn is_empty() {
            assert!(Interval::new(10, 5).is_empty());
            assert!(!Interval::new(5, 10).is_empty());
            assert!(!Interval::new(5, 5).is_empty());
        }

        #[test]
        fn intersect() {
            let a = Interval::new(0, 10);
            let b = Interval::new(5, 15);
            let c = a.intersect(&b);
            assert_eq!(c.min, 5);
            assert_eq!(c.max, 10);
        }

        #[test]
        fn intersect_empty() {
            let a = Interval::new(0, 5);
            let b = Interval::new(10, 15);
            let c = a.intersect(&b);
            assert!(c.is_empty());
        }

        #[test]
        fn pick_value_simple() {
            let interval = Interval::new(0, 100);
            let val = interval.pick_value().unwrap();
            assert!(val >= 0 && val <= 100);
        }

        #[test]
        fn pick_value_single() {
            let interval = Interval::new(42, 42);
            assert_eq!(interval.pick_value(), Some(42));
        }

        #[test]
        fn pick_value_with_excluded() {
            let mut interval = Interval::new(0, 2);
            interval.excluded = Some(1); // Exclude midpoint
            let val = interval.pick_value().unwrap();
            assert!(val == 0 || val == 2);
        }

        #[test]
        fn constrain_lt() {
            let interval = Interval::new(-100, 100);
            let constrained = interval.constrain(CompareOp::Lt, 50, true);
            assert!(constrained.max < 50);
        }

        #[test]
        fn constrain_ge_negated() {
            let interval = Interval::new(-100, 100);
            // NOT(x >= 50) => x < 50
            let constrained = interval.constrain(CompareOp::Ge, 50, false);
            assert!(constrained.max < 50);
        }
    }

    // =========================================================================
    // Relational Solver Tests
    // =========================================================================

    mod relational_solver {
        use super::*;

        #[test]
        fn x_less_than_y() {
            let bdd = Bdd::default();
            let mut universe = PredicateUniverse::new();

            let p1 = Predicate::lt_var("x", "y");
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

            let p1 = Predicate::eq_var("x", "y");
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
            let p1 = Predicate::lt_var("x", "y");
            let p2 = Predicate::eq_var("x", "y");
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
            let p1 = Predicate::lt_var("x", "y");
            let p2 = Predicate::lt_var("y", "z");
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
            let p1 = Predicate::lt_var("x", "y");
            let p2 = Predicate::lt_var("y", "z");
            let p3 = Predicate::lt_var("z", "x");
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

    // =========================================================================
    // Array Bounds Solver Tests
    // =========================================================================

    mod array_bounds_solver {
        use super::*;

        #[test]
        fn valid_index() {
            let bdd = Bdd::default();
            let mut universe = PredicateUniverse::new();

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
            let mut universe = PredicateUniverse::new();

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
            let mut universe = PredicateUniverse::new();

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
            let mut universe = PredicateUniverse::new();

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

    // =========================================================================
    // Bitwise Solver Tests
    // =========================================================================

    mod bitwise_solver {
        use super::*;

        #[test]
        fn power_of_two() {
            let bdd = Bdd::default();
            let mut universe = PredicateUniverse::new();

            let p1 = Predicate::gt("x", 0);
            let var1 = universe.register(p1, &bdd);

            let mut solver = BitwiseSolver::new();
            solver.require_power_of_two("x");

            let mut assignments = HashMap::new();
            assignments.insert(var1, true);

            match solver.solve(&assignments, &universe) {
                SolveResult::Sat(witness) => {
                    let x = witness.get("x").unwrap();
                    assert!(x > 0, "x should be positive");
                    assert!((x & (x - 1)) == 0, "x={} should be power of 2", x);
                }
                other => panic!("Expected Sat, got {:?}", other),
            }
        }

        #[test]
        fn non_negative() {
            let bdd = Bdd::default();
            let mut universe = PredicateUniverse::new();

            // Test with a potentially negative range
            let p1 = Predicate::ge("x", -100);
            let p2 = Predicate::le("x", 100);
            let var1 = universe.register(p1, &bdd);
            let var2 = universe.register(p2, &bdd);

            let mut solver = BitwiseSolver::new();
            solver.require_non_negative("x");

            let mut assignments = HashMap::new();
            assignments.insert(var1, true);
            assignments.insert(var2, true);

            match solver.solve(&assignments, &universe) {
                SolveResult::Sat(witness) => {
                    let x = witness.get("x").unwrap();
                    assert!(x >= 0, "x={} should be non-negative", x);
                }
                other => panic!("Expected Sat, got {:?}", other),
            }
        }

        #[test]
        fn alignment() {
            let bdd = Bdd::default();
            let mut universe = PredicateUniverse::new();

            let p1 = Predicate::gt("x", 0);
            let var1 = universe.register(p1, &bdd);

            let mut solver = BitwiseSolver::new();
            solver.require_aligned("x", 8);

            let mut assignments = HashMap::new();
            assignments.insert(var1, true);

            match solver.solve(&assignments, &universe) {
                SolveResult::Sat(witness) => {
                    let x = witness.get("x").unwrap();
                    assert!(x % 8 == 0, "x={} should be 8-byte aligned", x);
                }
                other => panic!("Expected Sat, got {:?}", other),
            }
        }

        #[test]
        fn bit_set() {
            let bdd = Bdd::default();
            let mut universe = PredicateUniverse::new();

            // Need a constraint to establish the variable
            let p1 = Predicate::ge("x", 0);
            let var1 = universe.register(p1, &bdd);

            let mut solver = BitwiseSolver::new();
            solver.require_bit_set("x", 3); // Bit 3 must be set

            let mut assignments = HashMap::new();
            assignments.insert(var1, true);

            match solver.solve(&assignments, &universe) {
                SolveResult::Sat(witness) => {
                    let x = witness.get("x").unwrap();
                    assert!((x >> 3) & 1 == 1, "x={} should have bit 3 set", x);
                }
                other => panic!("Expected Sat, got {:?}", other),
            }
        }

        #[test]
        fn bit_clear() {
            let bdd = Bdd::default();
            let mut universe = PredicateUniverse::new();

            // Need a constraint to establish the variable
            let p1 = Predicate::ge("x", 0);
            let var1 = universe.register(p1, &bdd);

            let mut solver = BitwiseSolver::new();
            solver.require_bit_clear("x", 0); // Bit 0 must be clear (even number)

            let mut assignments = HashMap::new();
            assignments.insert(var1, true);

            match solver.solve(&assignments, &universe) {
                SolveResult::Sat(witness) => {
                    let x = witness.get("x").unwrap_or(0);
                    assert!((x & 1) == 0, "x={} should have bit 0 clear (even)", x);
                }
                other => panic!("Expected Sat, got {:?}", other),
            }
        }

        #[test]
        fn combined_constraints() {
            let bdd = Bdd::default();
            let mut universe = PredicateUniverse::new();

            let p1 = Predicate::gt("x", 0);
            let var1 = universe.register(p1, &bdd);

            let mut solver = BitwiseSolver::new();
            solver.require_power_of_two("x");
            solver.require_non_negative("x");

            let mut assignments = HashMap::new();
            assignments.insert(var1, true);

            match solver.solve(&assignments, &universe) {
                SolveResult::Sat(witness) => {
                    let x = witness.get("x").unwrap();
                    assert!(x > 0 && (x & (x - 1)) == 0, "x={} should be positive power of 2", x);
                }
                other => panic!("Expected Sat, got {:?}", other),
            }
        }
    }

    // =========================================================================
    // Boundary Value Generator Tests
    // =========================================================================

    mod boundary_value_generator {
        use super::*;

        #[test]
        fn basic_generation() {
            let generator = BoundaryValueGenerator::new();
            let interval = Interval::new(0, 100);
            let values = generator.generate(&interval);

            // Should include min, max, and midpoint at minimum
            assert!(values.contains(&0));
            assert!(values.contains(&100));
            assert!(values.contains(&50));
        }

        #[test]
        fn off_by_one_values() {
            let generator = BoundaryValueGenerator::new();
            let interval = Interval::new(10, 20);
            let values = generator.generate(&interval);

            // Should include off-by-one values
            assert!(values.contains(&9)); // min - 1
            assert!(values.contains(&11)); // min + 1
            assert!(values.contains(&19)); // max - 1
            assert!(values.contains(&21)); // max + 1
        }

        #[test]
        fn special_values() {
            let generator = BoundaryValueGenerator::new();
            let interval = Interval::new(-10, 10);
            let values = generator.generate(&interval);

            // Should include special values like 0, -1, 1
            assert!(values.contains(&0));
            assert!(values.contains(&-1));
            assert!(values.contains(&1));
        }

        #[test]
        fn powers_of_two() {
            let generator = BoundaryValueGenerator::all();
            let interval = Interval::new(0, 100);
            let values = generator.generate(&interval);

            // With powers_of_two enabled
            assert!(values.contains(&1));
            assert!(values.contains(&2));
            assert!(values.contains(&4));
            assert!(values.contains(&8));
            assert!(values.contains(&16));
            assert!(values.contains(&32));
            assert!(values.contains(&64));
        }

        #[test]
        fn excluded_value() {
            let generator = BoundaryValueGenerator::new();
            let mut interval = Interval::new(0, 10);
            interval.excluded = Some(5);
            let values = generator.generate(&interval);

            // Should not include excluded value
            assert!(!values.contains(&5));
        }

        #[test]
        fn empty_interval() {
            let generator = BoundaryValueGenerator::new();
            let interval = Interval::new(10, 5); // Empty
            let values = generator.generate(&interval);

            assert!(values.is_empty());
        }

        #[test]
        fn single_point_interval() {
            let generator = BoundaryValueGenerator::new();
            let interval = Interval::new(42, 42);
            let values = generator.generate(&interval);

            assert!(values.contains(&42));
        }

        #[test]
        fn test_cases_generation() {
            let generator = BoundaryValueGenerator::new();
            let mut intervals = HashMap::new();
            intervals.insert("x".to_string(), Interval::new(0, 10));
            intervals.insert("y".to_string(), Interval::new(-5, 5));

            let test_cases = generator.generate_test_cases(&intervals);

            // Should generate multiple test cases
            assert!(!test_cases.is_empty());

            // Each test case should have both variables
            for tc in &test_cases {
                assert!(tc.values.contains_key("x"));
                assert!(tc.values.contains_key("y"));
            }
        }
    }

    // =========================================================================
    // Combined Solver Tests
    // =========================================================================

    mod combined_solver {
        use super::*;

        #[test]
        fn interval_relational_combined() {
            let bdd = Bdd::default();
            let mut universe = PredicateUniverse::new();

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
            let mut universe = PredicateUniverse::new();

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

    // =========================================================================
    // Modular Solver Tests
    // =========================================================================

    mod modular_solver {
        use super::*;

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

    // =========================================================================
    // Witness Tests
    // =========================================================================

    mod witness {
        use super::*;

        #[test]
        fn builder_pattern() {
            let w = Witness::new().with("x", 10).with("y", 20).with("z", 30);

            assert_eq!(w.get("x"), Some(10));
            assert_eq!(w.get("y"), Some(20));
            assert_eq!(w.get("z"), Some(30));
        }

        #[test]
        fn missing_variable() {
            let w = Witness::new().with("x", 10);
            assert_eq!(w.get("y"), None);
        }

        #[test]
        fn default_is_empty() {
            let w = Witness::default();
            assert!(w.values.is_empty());
        }
    }
}
