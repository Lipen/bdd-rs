//! Theory solver integration for T-BDD.
//!
//! This module provides the interface between BDD path constraints and
//! theory solvers. BDD paths give us boolean assignments to predicates,
//! but we need theory reasoning to:
//!
//! 1. Check if a path is feasible (satisfiable in the theory)
//! 2. Generate concrete witness values when feasible
//! 3. Prune infeasible paths early

use std::collections::HashMap;

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
struct Interval {
    min: i64,
    max: i64,
    excluded: Option<i64>,
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
    fn solve(&self, assignments: &HashMap<Var, bool>, universe: &PredicateUniverse) -> SolveResult {
        let mut intervals: HashMap<String, Interval> = HashMap::new();

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
    use bdd_rs::bdd::Bdd;

    use super::*;
    use crate::predicate::Predicate;

    #[test]
    fn test_interval_solver_simple() {
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
    fn test_interval_solver_unsat() {
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
    fn test_interval_negation() {
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
}
