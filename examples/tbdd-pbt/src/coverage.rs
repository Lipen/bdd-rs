//! Coverage tracking using BDD operations.
//!
//! BDDs naturally represent sets of paths, so:
//! - Coverage = BDD of covered paths
//! - Uncovered = NOT(Coverage) AND Target

use std::collections::HashMap;

use bdd_rs::bdd::Bdd;
use bdd_rs::reference::Ref;
use bdd_rs::types::Var;

/// Tracks coverage using BDD operations.
pub struct CoverageTracker<'a> {
    bdd: &'a Bdd,
    /// BDD representing covered paths.
    covered: Ref,
    /// BDD representing all paths we want to cover.
    target: Ref,
    /// Track which predicates we've seen in each polarity.
    predicate_coverage: HashMap<Var, PredicateCoverage>,
    /// Number of tests executed.
    test_count: usize,
}

/// Coverage status for a single predicate.
#[derive(Debug, Clone, Default)]
pub struct PredicateCoverage {
    pub seen_true: bool,
    pub seen_false: bool,
}

impl PredicateCoverage {
    pub fn is_fully_covered(&self) -> bool {
        self.seen_true && self.seen_false
    }
}

/// Summary of current coverage status.
#[derive(Debug, Clone)]
pub struct CoverageSummary {
    /// Fraction of predicates fully covered.
    pub predicate_coverage_ratio: f64,
    /// Number of tests executed.
    pub test_count: usize,
    /// Whether all target paths are covered.
    pub is_complete: bool,
}

impl<'a> CoverageTracker<'a> {
    /// Create a new coverage tracker.
    pub fn new(bdd: &'a Bdd, target: Ref) -> Self {
        Self {
            bdd,
            covered: bdd.zero(),
            target,
            predicate_coverage: HashMap::new(),
            test_count: 0,
        }
    }

    /// Create tracker targeting all paths (universe).
    pub fn new_universe(bdd: &'a Bdd) -> Self {
        Self::new(bdd, bdd.one())
    }

    /// Record that a path was covered.
    pub fn record_path(&mut self, path_constraint: Ref, assignments: &HashMap<Var, bool>) {
        self.covered = self.bdd.apply_or(self.covered, path_constraint);

        for (&var, &value) in assignments {
            let entry = self.predicate_coverage.entry(var).or_default();
            if value {
                entry.seen_true = true;
            } else {
                entry.seen_false = true;
            }
        }

        self.test_count += 1;
    }

    /// Record coverage from a set of variable assignments.
    pub fn record_assignments(&mut self, assignments: &HashMap<Var, bool>) {
        let mut constraint = self.bdd.one();
        for (&var, &value) in assignments {
            let var_ref = self.bdd.mk_var(var);
            let literal = if value { var_ref } else { -var_ref };
            constraint = self.bdd.apply_and(constraint, literal);
        }

        self.record_path(constraint, assignments);
    }

    /// Get BDD representing uncovered paths.
    pub fn uncovered(&self) -> Ref {
        self.bdd.apply_and(self.target, -self.covered)
    }

    /// Check if all target paths are covered.
    pub fn is_complete(&self) -> bool {
        self.bdd.is_zero(self.uncovered())
    }

    /// Get current coverage summary.
    pub fn summary(&self) -> CoverageSummary {
        let predicates_covered = self.predicate_coverage.values().filter(|p| p.is_fully_covered()).count();
        let predicates_total = self.predicate_coverage.len();

        let predicate_coverage_ratio = if predicates_total > 0 {
            predicates_covered as f64 / predicates_total as f64
        } else {
            1.0
        };

        CoverageSummary {
            predicate_coverage_ratio,
            test_count: self.test_count,
            is_complete: self.is_complete(),
        }
    }

    /// Get predicates that haven't been fully covered.
    pub fn uncovered_predicates(&self) -> Vec<Var> {
        self.predicate_coverage
            .iter()
            .filter(|(_, cov)| !cov.is_fully_covered())
            .map(|(&var, _)| var)
            .collect()
    }

    /// Get the covered BDD.
    pub fn covered(&self) -> Ref {
        self.covered
    }

    /// Get the target BDD.
    pub fn target(&self) -> Ref {
        self.target
    }

    /// Reset coverage tracking.
    pub fn reset(&mut self) {
        self.covered = self.bdd.zero();
        self.predicate_coverage.clear();
        self.test_count = 0;
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_coverage_tracking_basic() {
        let bdd = Bdd::default();
        let mut tracker = CoverageTracker::new_universe(&bdd);

        assert!(!tracker.is_complete());

        let assignments = HashMap::new();
        tracker.record_assignments(&assignments);

        assert!(tracker.is_complete());
    }

    #[test]
    fn test_coverage_with_variables() {
        let bdd = Bdd::default();
        let v1 = bdd.mk_var(Var::new(1));

        let mut tracker = CoverageTracker::new(&bdd, v1);

        let mut assignments = HashMap::new();
        assignments.insert(Var::new(1), true);
        tracker.record_assignments(&assignments);

        assert!(tracker.is_complete());

        let summary = tracker.summary();
        assert_eq!(summary.test_count, 1);
    }

    #[test]
    fn test_predicate_coverage() {
        let bdd = Bdd::default();
        let mut tracker = CoverageTracker::new_universe(&bdd);

        let mut assignments = HashMap::new();
        assignments.insert(Var::new(1), true);
        tracker.record_assignments(&assignments);

        assert!(!tracker.predicate_coverage[&Var::new(1)].is_fully_covered());

        assignments.insert(Var::new(1), false);
        tracker.record_assignments(&assignments);

        assert!(tracker.predicate_coverage[&Var::new(1)].is_fully_covered());
    }
}
