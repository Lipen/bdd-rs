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

// =============================================================================
// Path Prioritization: Heuristic-based path ordering
// =============================================================================

/// Path priority heuristics for guided exploration.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PathPriority {
    /// Higher priority for shorter paths (fewer predicates).
    ShortestFirst,
    /// Higher priority for longer paths (more constraints).
    LongestFirst,
    /// Prioritize paths with more positive (true) assignments.
    MorePositive,
    /// Prioritize paths with more negative (false) assignments.
    MoreNegative,
    /// Prioritize boundary/edge case paths.
    BoundaryFirst,
    /// Random ordering.
    Random,
}

/// Path with associated priority score.
#[derive(Debug, Clone)]
pub struct PrioritizedPath {
    /// The boolean assignments defining this path.
    pub assignments: HashMap<Var, bool>,
    /// Priority score (higher = more priority).
    pub score: i64,
    /// Reason for this priority.
    pub reason: String,
}

impl PrioritizedPath {
    fn new(assignments: HashMap<Var, bool>) -> Self {
        Self {
            assignments,
            score: 0,
            reason: String::new(),
        }
    }
}

/// Prioritized test generator with heuristic-based path ordering.
pub struct PrioritizedGenerator<'a, S: ConstraintSolver> {
    bdd: &'a Bdd,
    universe: &'a PredicateUniverse,
    solver: &'a S,
    priorities: Vec<PathPriority>,
}

impl<'a, S: ConstraintSolver> PrioritizedGenerator<'a, S> {
    pub fn new(bdd: &'a Bdd, universe: &'a PredicateUniverse, solver: &'a S) -> Self {
        Self {
            bdd,
            universe,
            solver,
            priorities: vec![PathPriority::ShortestFirst],
        }
    }

    /// Set the prioritization strategy.
    pub fn with_priority(mut self, priority: PathPriority) -> Self {
        self.priorities = vec![priority];
        self
    }

    /// Add multiple prioritization strategies (combined).
    pub fn with_priorities(mut self, priorities: Vec<PathPriority>) -> Self {
        self.priorities = priorities;
        self
    }

    /// Generate tests in priority order.
    pub fn generate_prioritized(&self, constraint: Ref, max_tests: usize) -> Vec<TestCase> {
        let mut paths = self.enumerate_and_score(constraint);

        // Sort by score (descending)
        paths.sort_by(|a, b| b.score.cmp(&a.score));

        let mut tests = Vec::new();
        for (i, path) in paths.into_iter().enumerate() {
            if i >= max_tests {
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
                SolveResult::Unknown => continue,
            }
        }

        tests
    }

    fn enumerate_and_score(&self, node: Ref) -> Vec<PrioritizedPath> {
        let mut paths = Vec::new();
        let mut assignment = HashMap::new();
        self.enumerate_and_score_rec(node, &mut assignment, &mut paths);

        // Apply scoring
        for path in &mut paths {
            path.score = self.compute_score(path);
        }

        paths
    }

    fn enumerate_and_score_rec(&self, node: Ref, assignment: &mut HashMap<Var, bool>, paths: &mut Vec<PrioritizedPath>) {
        if self.bdd.is_zero(node) {
            return;
        }
        if self.bdd.is_one(node) {
            paths.push(PrioritizedPath::new(assignment.clone()));
            return;
        }

        let var = self.bdd.variable(node.id());
        let low = self.bdd.low_node(node);
        let high = self.bdd.high_node(node);

        assignment.insert(var, false);
        self.enumerate_and_score_rec(low, assignment, paths);

        assignment.insert(var, true);
        self.enumerate_and_score_rec(high, assignment, paths);

        assignment.remove(&var);
    }

    fn compute_score(&self, path: &PrioritizedPath) -> i64 {
        let mut score = 0i64;

        for priority in &self.priorities {
            score += match priority {
                PathPriority::ShortestFirst => -(path.assignments.len() as i64),
                PathPriority::LongestFirst => path.assignments.len() as i64,
                PathPriority::MorePositive => path.assignments.values().filter(|&&v| v).count() as i64,
                PathPriority::MoreNegative => path.assignments.values().filter(|&&v| !v).count() as i64,
                PathPriority::BoundaryFirst => {
                    // Score higher for paths with all-true or all-false assignments
                    let all_true = path.assignments.values().all(|&v| v);
                    let all_false = path.assignments.values().all(|&v| !v);
                    if all_true || all_false {
                        100
                    } else {
                        0
                    }
                }
                PathPriority::Random => 0, // Will shuffle later
            };
        }

        score
    }
}

// =============================================================================
// Symbolic Execution Pattern
// =============================================================================

/// State for symbolic execution trace.
#[derive(Debug, Clone)]
pub struct SymbolicState {
    /// Path condition as BDD.
    pub path_condition: Ref,
    /// Current variable assignments.
    pub assignments: HashMap<Var, bool>,
    /// Execution trace (sequence of branch decisions).
    pub trace: Vec<(Var, bool)>,
}

impl SymbolicState {
    pub fn new(path_condition: Ref) -> Self {
        Self {
            path_condition,
            assignments: HashMap::new(),
            trace: Vec::new(),
        }
    }

    /// Fork execution: create two states for a branch.
    pub fn fork(&self, bdd: &Bdd, var: Var) -> (SymbolicState, SymbolicState) {
        let var_node = bdd.mk_var(var);

        // True branch
        let mut true_state = self.clone();
        true_state.path_condition = bdd.apply_and(self.path_condition, var_node);
        true_state.assignments.insert(var, true);
        true_state.trace.push((var, true));

        // False branch
        let mut false_state = self.clone();
        false_state.path_condition = bdd.apply_and(self.path_condition, -var_node);
        false_state.assignments.insert(var, false);
        false_state.trace.push((var, false));

        (true_state, false_state)
    }

    /// Check if this state's path condition is satisfiable.
    pub fn is_feasible(&self, bdd: &Bdd) -> bool {
        !bdd.is_zero(self.path_condition)
    }
}

/// Symbolic executor for BDD-guided path exploration.
pub struct SymbolicExecutor<'a, S: ConstraintSolver> {
    bdd: &'a Bdd,
    universe: &'a PredicateUniverse,
    solver: &'a S,
    /// Maximum path depth before stopping.
    pub max_depth: usize,
    /// Maximum number of paths to explore.
    pub max_paths: usize,
}

impl<'a, S: ConstraintSolver> SymbolicExecutor<'a, S> {
    pub fn new(bdd: &'a Bdd, universe: &'a PredicateUniverse, solver: &'a S) -> Self {
        Self {
            bdd,
            universe,
            solver,
            max_depth: 20,
            max_paths: 100,
        }
    }

    /// Execute symbolically from the given constraint.
    pub fn execute(&self, constraint: Ref) -> Vec<ExecutionResult> {
        let mut results = Vec::new();
        let mut worklist = vec![SymbolicState::new(constraint)];
        let mut explored = 0;

        while let Some(state) = worklist.pop() {
            if explored >= self.max_paths {
                break;
            }

            if state.trace.len() >= self.max_depth {
                continue;
            }

            if !state.is_feasible(self.bdd) {
                continue;
            }

            // Try to solve the current path condition
            match self.solver.solve(&state.assignments, self.universe) {
                SolveResult::Sat(witness) => {
                    results.push(ExecutionResult {
                        witness,
                        trace: state.trace.clone(),
                        path_condition: state.path_condition,
                    });
                    explored += 1;
                }
                SolveResult::Unsat => continue,
                SolveResult::Unknown => continue,
            }
        }

        results
    }
}

/// Result of symbolic execution.
#[derive(Debug, Clone)]
pub struct ExecutionResult {
    /// Concrete witness values.
    pub witness: Witness,
    /// Execution trace.
    pub trace: Vec<(Var, bool)>,
    /// Path condition as BDD.
    pub path_condition: Ref,
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
