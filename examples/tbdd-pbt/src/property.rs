//! Property-based testing integration for T-BDD.
//!
//! This module provides the interface for defining properties and checking them
//! against BDD-guided test inputs. Properties are predicates that should hold
//! for all inputs; T-BDD systematically searches for counterexamples.
//!
//! ## Example
//!
//! ```ignore
//! let property = Property::new("abs is non-negative", |inputs| {
//!     let x = inputs.get("x").unwrap();
//!     x.abs() >= 0
//! });
//!
//! let checker = PropertyChecker::new(&bdd, &universe, &solver);
//! match checker.check(&property, constraint) {
//!     CheckResult::Pass(n) => println!("Passed {} tests", n),
//!     CheckResult::Fail(cex) => println!("Counterexample: {:?}", cex),
//! }
//! ```

use std::collections::HashMap;
use std::fmt;

use bdd_rs::bdd::Bdd;
use bdd_rs::reference::Ref;
use bdd_rs::types::Var;

use crate::coverage::CoverageTracker;
use crate::generator::{GeneratorConfig, TestCase, TestGenerator};
use crate::predicate::PredicateUniverse;
use crate::theory::{ConstraintSolver, SolveResult, Witness};

/// A property to check: a predicate that should hold for all inputs.
pub struct Property<F>
where
    F: Fn(&Witness) -> bool,
{
    /// Human-readable name for the property.
    pub name: String,
    /// The predicate to check.
    pub check: F,
}

impl<F> Property<F>
where
    F: Fn(&Witness) -> bool,
{
    pub fn new(name: impl Into<String>, check: F) -> Self {
        Self { name: name.into(), check }
    }
}

/// Result of property checking.
#[derive(Debug, Clone)]
pub enum CheckResult {
    /// Property passed for all tested inputs.
    Pass {
        /// Number of tests executed.
        test_count: usize,
        /// Number of paths explored.
        path_count: usize,
    },
    /// Found a counterexample.
    Fail {
        /// The failing input.
        counterexample: Witness,
        /// Which path led to the failure.
        path_id: usize,
        /// Boolean assignments for the failing path.
        path_assignments: HashMap<Var, bool>,
    },
    /// All paths were pruned as infeasible.
    Vacuous,
}

/// A counterexample with additional context.
#[derive(Debug, Clone)]
pub struct Counterexample {
    /// The failing input values.
    pub witness: Witness,
    /// Which path led to the failure.
    pub path_id: usize,
    /// Boolean assignments for the failing path.
    pub path_assignments: HashMap<Var, bool>,
    /// Human-readable description of the path.
    pub path_description: String,
}

impl fmt::Display for Counterexample {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "Counterexample found:")?;
        writeln!(f, "  Path ID: {}", self.path_id)?;
        writeln!(f, "  Path: {}", self.path_description)?;
        write!(f, "  Values:")?;
        for (var, val) in &self.witness.values {
            write!(f, " {} = {}", var, val)?;
        }
        Ok(())
    }
}

/// Property checker that explores BDD paths looking for counterexamples.
pub struct PropertyChecker<'a, S: ConstraintSolver> {
    bdd: &'a Bdd,
    universe: &'a PredicateUniverse,
    solver: &'a S,
    config: CheckerConfig,
}

/// Configuration for property checking.
#[derive(Debug, Clone)]
pub struct CheckerConfig {
    /// Maximum number of tests per property.
    pub max_tests: usize,
    /// Whether to continue after first failure.
    pub find_all: bool,
    /// Whether to track coverage.
    pub track_coverage: bool,
}

impl Default for CheckerConfig {
    fn default() -> Self {
        Self {
            max_tests: 1000,
            find_all: false,
            track_coverage: true,
        }
    }
}

impl<'a, S: ConstraintSolver> PropertyChecker<'a, S> {
    pub fn new(bdd: &'a Bdd, universe: &'a PredicateUniverse, solver: &'a S) -> Self {
        Self {
            bdd,
            universe,
            solver,
            config: CheckerConfig::default(),
        }
    }

    pub fn with_config(bdd: &'a Bdd, universe: &'a PredicateUniverse, solver: &'a S, config: CheckerConfig) -> Self {
        Self {
            bdd,
            universe,
            solver,
            config,
        }
    }

    /// Check a property against all paths in a constraint BDD.
    pub fn check<F>(&self, property: &Property<F>, constraint: Ref) -> CheckResult
    where
        F: Fn(&Witness) -> bool,
    {
        if self.bdd.is_zero(constraint) {
            return CheckResult::Vacuous;
        }

        let gen_config = GeneratorConfig {
            max_tests: self.config.max_tests,
            randomize: false,
        };
        let generator = TestGenerator::new(self.bdd, self.universe, self.solver, gen_config);
        let tests = generator.generate(constraint);

        if tests.is_empty() {
            return CheckResult::Vacuous;
        }

        let mut test_count = 0;
        let path_count = tests.len();

        for test in tests {
            if test.witness.values.is_empty() {
                continue;
            }

            test_count += 1;

            if !(property.check)(&test.witness) {
                return CheckResult::Fail {
                    counterexample: test.witness,
                    path_id: test.path_id,
                    path_assignments: test.path_assignments,
                };
            }
        }

        CheckResult::Pass { test_count, path_count }
    }

    /// Check multiple properties, returning results for each.
    pub fn check_all<'b, F>(&self, properties: &'b [Property<F>], constraint: Ref) -> Vec<(&'b str, CheckResult)>
    where
        F: Fn(&Witness) -> bool,
    {
        properties.iter().map(|p| (p.name.as_str(), self.check(p, constraint))).collect()
    }
}

/// Shrinking strategy for counterexamples.
pub trait Shrinker {
    /// Try to find a smaller counterexample.
    fn shrink(&self, witness: &Witness) -> Vec<Witness>;
}

/// Simple numeric shrinking: try values closer to zero.
pub struct NumericShrinker;

impl Shrinker for NumericShrinker {
    fn shrink(&self, witness: &Witness) -> Vec<Witness> {
        let mut results = Vec::new();

        for (var, &val) in &witness.values {
            // Try zero
            if val != 0 {
                let mut shrunk = witness.clone();
                shrunk.values.insert(var.clone(), 0);
                results.push(shrunk);
            }

            // Try halving
            if val.abs() > 1 {
                let mut shrunk = witness.clone();
                shrunk.values.insert(var.clone(), val / 2);
                results.push(shrunk);
            }

            // Try moving toward zero
            if val > 0 {
                let mut shrunk = witness.clone();
                shrunk.values.insert(var.clone(), val - 1);
                results.push(shrunk);
            } else if val < 0 {
                let mut shrunk = witness.clone();
                shrunk.values.insert(var.clone(), val + 1);
                results.push(shrunk);
            }
        }

        results
    }
}

/// Shrink a counterexample while it still fails the property.
pub fn shrink_counterexample<F, H>(witness: &Witness, property: &F, shrinker: &H, max_steps: usize) -> Witness
where
    F: Fn(&Witness) -> bool,
    H: Shrinker,
{
    let mut current = witness.clone();
    let mut steps = 0;

    while steps < max_steps {
        let candidates = shrinker.shrink(&current);
        let mut found_smaller = false;

        for candidate in candidates {
            if !property(&candidate) {
                current = candidate;
                found_smaller = true;
                break;
            }
        }

        if !found_smaller {
            break;
        }
        steps += 1;
    }

    current
}

/// Builder for constructing property-based tests.
pub struct TestBuilder<'a, S: ConstraintSolver> {
    bdd: &'a Bdd,
    universe: &'a PredicateUniverse,
    solver: &'a S,
    constraints: Vec<Ref>,
}

impl<'a, S: ConstraintSolver> TestBuilder<'a, S> {
    pub fn new(bdd: &'a Bdd, universe: &'a PredicateUniverse, solver: &'a S) -> Self {
        Self {
            bdd,
            universe,
            solver,
            constraints: Vec::new(),
        }
    }

    /// Add a constraint that inputs must satisfy.
    pub fn given(mut self, constraint: Ref) -> Self {
        self.constraints.push(constraint);
        self
    }

    /// Run a property check with all accumulated constraints.
    pub fn check<F>(self, property: Property<F>) -> CheckResult
    where
        F: Fn(&Witness) -> bool,
    {
        let mut combined = self.bdd.one();
        for c in &self.constraints {
            combined = self.bdd.apply_and(combined, *c);
        }

        let checker = PropertyChecker::new(self.bdd, self.universe, self.solver);
        checker.check(&property, combined)
    }
}

// =============================================================================
// Statistical property testing
// =============================================================================

/// Statistics from property checking run.
#[derive(Debug, Clone)]
pub struct TestStatistics {
    /// Total tests executed.
    pub total_tests: usize,
    /// Tests that passed.
    pub passed: usize,
    /// Tests that failed.
    pub failed: usize,
    /// Paths pruned by theory.
    pub pruned: usize,
    /// Coverage summary if tracking was enabled.
    pub coverage: Option<f64>,
}

/// Extended property checker with statistics.
pub struct StatisticalChecker<'a, S: ConstraintSolver> {
    bdd: &'a Bdd,
    universe: &'a PredicateUniverse,
    solver: &'a S,
    coverage: CoverageTracker<'a>,
}

impl<'a, S: ConstraintSolver> StatisticalChecker<'a, S> {
    pub fn new(bdd: &'a Bdd, universe: &'a PredicateUniverse, solver: &'a S, target: Ref) -> Self {
        Self {
            bdd,
            universe,
            solver,
            coverage: CoverageTracker::new(bdd, target),
        }
    }

    /// Check property and collect statistics.
    pub fn check_with_stats<F>(&mut self, property: &Property<F>, constraint: Ref) -> (CheckResult, TestStatistics)
    where
        F: Fn(&Witness) -> bool,
    {
        let gen_config = GeneratorConfig {
            max_tests: 10000,
            randomize: false,
        };
        let generator = TestGenerator::new(self.bdd, self.universe, self.solver, gen_config);

        let paths = self.enumerate_paths_with_stats(constraint, &generator);

        let mut stats = TestStatistics {
            total_tests: 0,
            passed: 0,
            failed: 0,
            pruned: paths.pruned,
            coverage: None,
        };

        let mut first_failure: Option<(Witness, usize, HashMap<Var, bool>)> = None;

        for test in paths.tests {
            if test.witness.values.is_empty() {
                continue;
            }

            stats.total_tests += 1;
            self.coverage.record_assignments(&test.path_assignments);

            if (property.check)(&test.witness) {
                stats.passed += 1;
            } else {
                stats.failed += 1;
                if first_failure.is_none() {
                    first_failure = Some((test.witness.clone(), test.path_id, test.path_assignments.clone()));
                }
            }
        }

        stats.coverage = Some(self.coverage.summary().predicate_coverage_ratio);

        let result = match first_failure {
            Some((witness, path_id, assignments)) => CheckResult::Fail {
                counterexample: witness,
                path_id,
                path_assignments: assignments,
            },
            None if stats.total_tests == 0 => CheckResult::Vacuous,
            None => CheckResult::Pass {
                test_count: stats.total_tests,
                path_count: stats.passed,
            },
        };

        (result, stats)
    }

    fn enumerate_paths_with_stats(&self, constraint: Ref, generator: &TestGenerator<'a, S>) -> PathEnumerationResult {
        let tests = generator.generate(constraint);
        let mut valid_tests = Vec::new();
        let mut pruned = 0;

        for test in tests {
            // Check if this path was actually satisfiable
            let result = self.solver.solve(&test.path_assignments, self.universe);
            match result {
                SolveResult::Sat(_) => valid_tests.push(test),
                SolveResult::Unsat => pruned += 1,
                SolveResult::Unknown => valid_tests.push(test),
            }
        }

        PathEnumerationResult {
            tests: valid_tests,
            pruned,
        }
    }

    /// Get current coverage tracker.
    pub fn coverage(&self) -> &CoverageTracker<'a> {
        &self.coverage
    }
}

struct PathEnumerationResult {
    tests: Vec<TestCase>,
    pruned: usize,
}

#[cfg(test)]
mod tests {
    use bdd_rs::bdd::Bdd;

    use super::*;
    use crate::predicate::Predicate;
    use crate::theory::IntervalSolver;

    #[test]
    fn test_property_pass() {
        let bdd = Bdd::default();
        let mut universe = PredicateUniverse::new();

        let p1 = Predicate::ge("x", 0);
        let v1 = universe.register(p1, &bdd);
        let constraint = bdd.mk_var(v1);

        let solver = IntervalSolver::with_bounds(0, 100);
        let checker = PropertyChecker::new(&bdd, &universe, &solver);

        let prop = Property::new("x is non-negative", |w| w.get("x").unwrap_or(0) >= 0);

        match checker.check(&prop, constraint) {
            CheckResult::Pass { test_count, .. } => {
                assert!(test_count > 0);
            }
            other => panic!("Expected Pass, got {:?}", other),
        }
    }

    #[test]
    fn test_property_fail() {
        let bdd = Bdd::default();
        let mut universe = PredicateUniverse::new();

        let p1 = Predicate::lt("x", 0);
        let v1 = universe.register(p1, &bdd);
        let constraint = bdd.mk_var(v1);

        let solver = IntervalSolver::with_bounds(-100, 100);
        let checker = PropertyChecker::new(&bdd, &universe, &solver);

        // Property that should fail: x >= 0
        let prop = Property::new("x is non-negative", |w| w.get("x").unwrap_or(0) >= 0);

        match checker.check(&prop, constraint) {
            CheckResult::Fail { counterexample, .. } => {
                let x = counterexample.get("x").unwrap();
                assert!(x < 0, "counterexample x={} should be negative", x);
            }
            other => panic!("Expected Fail, got {:?}", other),
        }
    }

    #[test]
    fn test_shrinking() {
        let witness = Witness::new().with("x", 100);
        let property = |w: &Witness| w.get("x").unwrap_or(0) < 50;

        let shrunk = shrink_counterexample(&witness, &property, &NumericShrinker, 100);
        let x = shrunk.get("x").unwrap();

        // Should have shrunk to something smaller but still >= 50
        assert!(x >= 50, "shrunk x={} should still fail property", x);
        assert!(x < 100, "shrunk x={} should be smaller than original", x);
    }

    #[test]
    fn test_builder_pattern() {
        let bdd = Bdd::default();
        let mut universe = PredicateUniverse::new();

        let p1 = Predicate::ge("x", 0);
        let p2 = Predicate::lt("x", 100);

        let v1 = universe.register(p1, &bdd);
        let v2 = universe.register(p2, &bdd);

        let solver = IntervalSolver::with_bounds(-1000, 1000);

        let result = TestBuilder::new(&bdd, &universe, &solver)
            .given(bdd.mk_var(v1))
            .given(bdd.mk_var(v2))
            .check(Property::new("x in range", |w| {
                let x = w.get("x").unwrap_or(0);
                x >= 0 && x < 100
            }));

        assert!(matches!(result, CheckResult::Pass { .. }));
    }
}
