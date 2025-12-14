//! Bitwise constraint solver.
//!
//! Handles constraints involving bit-level properties.

use std::collections::HashMap;

use ananke_bdd::types::Var;

use super::core::{ConstraintSolver, SolveResult, Witness};
use super::interval::IntervalSolver;
use crate::predicate::PredicateUniverse;

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
///
/// # Example
///
/// ```rust
/// use std::collections::HashMap;
/// use ananke_bdd::bdd::Bdd;
/// use tbdd_pbt::predicate::{Predicate, PredicateUniverse};
/// use tbdd_pbt::theory::{BitwiseSolver, ConstraintSolver, SolveResult};
///
/// let bdd = Bdd::default();
/// let mut universe = PredicateUniverse::new();
///
/// let var1 = universe.register(Predicate::gt("x", 0), &bdd);
///
/// let mut solver = BitwiseSolver::new();
/// solver.require_power_of_two("x");
///
/// let mut assignments = HashMap::new();
/// assignments.insert(var1, true);
///
/// match solver.solve(&assignments, &universe) {
///     SolveResult::Sat(w) => {
///         let x = w.get("x").unwrap();
///         assert!(x > 0 && (x & (x - 1)) == 0, "x should be power of 2");
///     }
///     _ => panic!("Expected Sat"),
/// }
/// ```
pub struct BitwiseSolver {
    constraints: Vec<BitwiseConstraint>,
    interval_solver: IntervalSolver,
}

impl BitwiseSolver {
    /// Create a new bitwise solver.
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

#[cfg(test)]
mod tests {
    use ananke_bdd::bdd::Bdd;

    use super::*;
    use crate::predicate::Predicate;

    #[test]
    fn power_of_two() {
        let bdd = Bdd::default();
        let mut universe = crate::predicate::PredicateUniverse::new();

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
        let mut universe = crate::predicate::PredicateUniverse::new();

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
        let mut universe = crate::predicate::PredicateUniverse::new();

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
        let mut universe = crate::predicate::PredicateUniverse::new();

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
        let mut universe = crate::predicate::PredicateUniverse::new();

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
        let mut universe = crate::predicate::PredicateUniverse::new();

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
