//! Test input generation from BDD paths.
//!
//! This module generates concrete test inputs by:
//! 1. Enumerating paths through the BDD (each path = boolean assignment)
//! 2. Using theory solver to get concrete values
//! 3. Optionally using randomization for variety

use std::collections::HashMap;

use bdd_rs::bdd::Bdd;
use bdd_rs::reference::Ref;
use bdd_rs::types::Var;
use rand::Rng;

use crate::predicate::PredicateUniverse;
use crate::theory::{ConstraintSolver, SolveResult, Witness};

/// Configuration for test generation.
#[derive(Debug, Clone)]
pub struct GeneratorConfig {
    /// Maximum number of tests to generate.
    pub max_tests: usize,
    /// Whether to randomize path exploration order.
    pub randomize: bool,
}

impl Default for GeneratorConfig {
    fn default() -> Self {
        Self {
            max_tests: 100,
            randomize: false,
        }
    }
}

/// Test generator that explores BDD paths and generates witnesses.
pub struct TestGenerator<'a, S: ConstraintSolver> {
    bdd: &'a Bdd,
    universe: &'a PredicateUniverse,
    solver: &'a S,
    config: GeneratorConfig,
}

impl<'a, S: ConstraintSolver> TestGenerator<'a, S> {
    pub fn new(bdd: &'a Bdd, universe: &'a PredicateUniverse, solver: &'a S, config: GeneratorConfig) -> Self {
        Self {
            bdd,
            universe,
            solver,
            config,
        }
    }

    /// Generate test cases from all satisfying paths through a BDD.
    pub fn generate(&self, constraint: Ref) -> Vec<TestCase> {
        let mut tests = Vec::new();

        if self.bdd.is_zero(constraint) {
            return tests;
        }

        let paths = self.enumerate_paths(constraint);

        for (i, path) in paths.into_iter().enumerate() {
            if i >= self.config.max_tests {
                break;
            }

            match self.solver.solve(&path.assignments, self.universe) {
                SolveResult::Sat(witness) => {
                    tests.push(TestCase {
                        witness,
                        path_id: i,
                        path_assignments: path.assignments,
                    });
                }
                SolveResult::Unsat => continue,
                SolveResult::Unknown => {
                    tests.push(TestCase {
                        witness: Witness::new(),
                        path_id: i,
                        path_assignments: path.assignments,
                    });
                }
            }
        }

        tests
    }

    /// Generate test cases for uncovered paths.
    pub fn generate_for_coverage(&self, covered: Ref, target: Ref) -> Vec<TestCase> {
        let uncovered = self.bdd.apply_and(target, -covered);
        self.generate(uncovered)
    }

    fn enumerate_paths(&self, node: Ref) -> Vec<Path> {
        let mut paths = Vec::new();
        let mut assignment = HashMap::new();
        self.enumerate_paths_rec(node, &mut assignment, &mut paths);
        paths
    }

    fn enumerate_paths_rec(&self, node: Ref, assignment: &mut HashMap<Var, bool>, paths: &mut Vec<Path>) {
        if self.bdd.is_zero(node) {
            return;
        }
        if self.bdd.is_one(node) {
            paths.push(Path {
                assignments: assignment.clone(),
            });
            return;
        }

        let var = self.bdd.variable(node.id());
        let low = self.bdd.low_node(node);
        let high = self.bdd.high_node(node);

        assignment.insert(var, false);
        self.enumerate_paths_rec(low, assignment, paths);

        assignment.insert(var, true);
        self.enumerate_paths_rec(high, assignment, paths);

        assignment.remove(&var);
    }
}

#[derive(Debug, Clone)]
struct Path {
    assignments: HashMap<Var, bool>,
}

/// A generated test case.
#[derive(Debug, Clone)]
pub struct TestCase {
    /// Concrete values for program variables.
    pub witness: Witness,
    /// Identifier for the path that generated this test.
    pub path_id: usize,
    /// The boolean assignments that define this path.
    pub path_assignments: HashMap<Var, bool>,
}

/// Wrapper for generating tests with randomization.
pub struct RandomizedGenerator<'a, S: ConstraintSolver, R: Rng> {
    inner: TestGenerator<'a, S>,
    rng: R,
}

impl<'a, S: ConstraintSolver, R: Rng> RandomizedGenerator<'a, S, R> {
    pub fn new(inner: TestGenerator<'a, S>, rng: R) -> Self {
        Self { inner, rng }
    }

    /// Generate tests with randomized witness selection.
    pub fn generate_random(&mut self, constraint: Ref, count: usize) -> Vec<TestCase> {
        let mut tests = Vec::new();
        let paths = self.inner.enumerate_paths(constraint);

        if paths.is_empty() {
            return tests;
        }

        for _ in 0..count {
            let idx = self.rng.gen_range(0..paths.len());
            let path = &paths[idx];

            if let SolveResult::Sat(mut witness) = self.inner.solver.solve(&path.assignments, self.inner.universe) {
                self.randomize_witness(&mut witness);
                tests.push(TestCase {
                    witness,
                    path_id: idx,
                    path_assignments: path.assignments.clone(),
                });
            }
        }

        tests
    }

    fn randomize_witness(&mut self, witness: &mut Witness) {
        for value in witness.values.values_mut() {
            let delta: i64 = self.rng.gen_range(-10..=10);
            *value = value.saturating_add(delta);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::predicate::Predicate;
    use crate::theory::IntervalSolver;

    #[test]
    fn test_path_enumeration() {
        let bdd = Bdd::default();
        let mut universe = PredicateUniverse::new();

        let p1 = Predicate::lt("x", 10);
        let p2 = Predicate::ge("y", 0);

        let v1 = universe.register(p1, &bdd);
        let v2 = universe.register(p2, &bdd);

        let r1 = bdd.mk_var(v1);
        let r2 = bdd.mk_var(v2);
        let constraint = bdd.apply_and(r1, r2);

        let solver = IntervalSolver::new();
        let config = GeneratorConfig::default();
        let generator = TestGenerator::new(&bdd, &universe, &solver, config);

        let tests = generator.generate(constraint);

        assert_eq!(tests.len(), 1);

        let test = &tests[0];
        let x = test.witness.get("x").unwrap();
        let y = test.witness.get("y").unwrap();

        assert!(x < 10, "x should be < 10");
        assert!(y >= 0, "y should be >= 0");
    }
}
