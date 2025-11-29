//! T-BDD Example: Testing a simple function with BDD-guided exploration.
//!
//! This example demonstrates how to use T-BDD to:
//! 1. Define program predicates
//! 2. Build BDD path constraints
//! 3. Generate test inputs using theory solving
//! 4. Track coverage

use bdd_rs::bdd::Bdd;
use tbdd_pbt::{CoverageTracker, GeneratorConfig, IntervalSolver, Predicate, PredicateUniverse, TestGenerator};

/// Example function under test: categorize a number.
fn categorize(x: i64) -> &'static str {
    if x < 0 {
        "negative"
    } else if x == 0 {
        "zero"
    } else if x < 100 {
        "small positive"
    } else {
        "large positive"
    }
}

/// Path description with constraint info
struct PathInfo {
    name: &'static str,
    branch_trace: &'static str,
    interval: &'static str,
    samples: &'static [i64],
}

const PATHS: &[PathInfo] = &[
    PathInfo {
        name: "negative",
        branch_trace: "x<0 → T",
        interval: "(-∞, -1]",
        samples: &[-1000, -1, -42],
    },
    PathInfo {
        name: "zero",
        branch_trace: "x<0 → F, x==0 → T",
        interval: "[0, 0]",
        samples: &[0],
    },
    PathInfo {
        name: "small positive",
        branch_trace: "x<0 → F, x==0 → F, x<100 → T",
        interval: "[1, 99]",
        samples: &[1, 50, 99],
    },
    PathInfo {
        name: "large positive",
        branch_trace: "x<0 → F, x==0 → F, x<100 → F",
        interval: "[100, +∞)",
        samples: &[100, 500, 1000],
    },
];

fn main() {
    println!("══════════════════════════════════════════════════════════════");
    println!("  T-BDD: Theory-Aware BDD-Guided Property-Based Testing");
    println!("══════════════════════════════════════════════════════════════\n");

    // ─────────────────────────────────────────────────────────────────────────
    // Show the program being analyzed
    // ─────────────────────────────────────────────────────────────────────────
    println!("── PROGRAM UNDER TEST ──────────────────────────────────────────");
    println!("  fn categorize(x: i64) -> &str {{");
    println!("      if x < 0 {{                        // P1");
    println!("          \"negative\"");
    println!("      }} else if x == 0 {{                // P2");
    println!("          \"zero\"");
    println!("      }} else if x < 100 {{               // P3");
    println!("          \"small positive\"");
    println!("      }} else {{");
    println!("          \"large positive\"");
    println!("      }}");
    println!("  }}\n");

    // ─────────────────────────────────────────────────────────────────────────
    // Setup BDD and predicates
    // ─────────────────────────────────────────────────────────────────────────
    let bdd = Bdd::default();
    let mut universe = PredicateUniverse::new();

    let v1 = universe.register(Predicate::lt("x", 0), &bdd);
    let v2 = universe.register(Predicate::eq("x", 0), &bdd);
    let v3 = universe.register(Predicate::lt("x", 100), &bdd);

    println!("── PREDICATES ──────────────────────────────────────────────────");
    println!("  P1: x < 0     (BDD var {})", v1.id());
    println!("  P2: x == 0    (BDD var {})", v2.id());
    println!("  P3: x < 100   (BDD var {})\n", v3.id());

    // ─────────────────────────────────────────────────────────────────────────
    // Build path BDDs
    // ─────────────────────────────────────────────────────────────────────────
    let bv1 = bdd.mk_var(v1);
    let bv2 = bdd.mk_var(v2);
    let bv3 = bdd.mk_var(v3);

    let path_bdds = [
        bv1,                                            // negative
        bdd.apply_and(-bv1, bv2),                       // zero
        bdd.apply_and(bdd.apply_and(-bv1, -bv2), bv3),  // small positive
        bdd.apply_and(bdd.apply_and(-bv1, -bv2), -bv3), // large positive
    ];

    let all_paths = path_bdds.iter().copied().reduce(|a, b| bdd.apply_or(a, b)).unwrap();

    println!("── PATH ANALYSIS ───────────────────────────────────────────────");
    for (i, (&path_bdd, info)) in path_bdds.iter().zip(PATHS.iter()).enumerate() {
        println!("  Path {}: \"{}\"", i + 1, info.name);
        println!("    Branches: {}", info.branch_trace);
        println!("    Interval: x ∈ {}", info.interval);
        println!("    Samples:  {:?}", info.samples);
        println!("    BDD size: {} node(s)", bdd.size(path_bdd));
        println!("    BDD: {}\n", bdd.to_bracket_string(path_bdd));
    }
    // println!("\n  Total: {} paths, combined BDD = {} node(s)\n", PATHS.len(), bdd.size(all_paths));
    println!();
    println!("  Total: {} paths", PATHS.len());
    println!("  Combined BDD size: {} node(s)", bdd.size(all_paths));
    println!("  Combined BDD: {}", bdd.to_bracket_string(all_paths));
    println!();

    // ─────────────────────────────────────────────────────────────────────────
    // Test generation and execution
    // ─────────────────────────────────────────────────────────────────────────
    let solver = IntervalSolver::with_bounds(-1000, 1000);
    let config = GeneratorConfig {
        max_tests: 100,
        randomize: false,
    };
    let generator = TestGenerator::new(&bdd, &universe, &solver, config);
    let mut coverage = CoverageTracker::new(&bdd, all_paths);

    println!("── TEST EXECUTION ──────────────────────────────────────────────");

    let mut total_tests = 0;
    for (path_bdd, info) in path_bdds.iter().zip(PATHS.iter()) {
        let tests = generator.generate(*path_bdd);

        for test in &tests {
            if let Some(x) = test.witness.get("x") {
                let actual = categorize(x);

                if actual != info.name {
                    println!("  ✗ FAIL: x={} → \"{}\" (expected \"{}\")", x, actual, info.name);
                }
                assert_eq!(actual, info.name, "Path '{}' failed for x={}", info.name, x);

                coverage.record_assignments(&test.path_assignments);
                total_tests += 1;
            }
        }
        println!("  ✓ Path \"{}\": {} test(s) passed", info.name, tests.len());
    }
    println!("\n  Total: {} tests executed, all passed ✓\n", total_tests);

    // ─────────────────────────────────────────────────────────────────────────
    // Coverage summary
    // ─────────────────────────────────────────────────────────────────────────
    let summary = coverage.summary();
    println!("── COVERAGE ────────────────────────────────────────────────────");
    println!("  Predicate coverage: {:.0}%", summary.predicate_coverage_ratio * 100.0);
    println!(
        "  Path coverage:      {}\n",
        if summary.is_complete { "complete ✓" } else { "incomplete" }
    );

    assert!(summary.is_complete, "Expected complete path coverage");

    // ─────────────────────────────────────────────────────────────────────────
    // Theory pruning demonstration
    // ─────────────────────────────────────────────────────────────────────────
    println!("── THEORY PRUNING ──────────────────────────────────────────────");

    let infeasible1 = bdd.apply_and(bv1, bv2); // x<0 ∧ x==0
    let tests1 = generator.generate(infeasible1);
    println!("  Constraint: (x < 0) ∧ (x == 0)");
    println!(
        "  Result:     {} (infeasible → pruned)",
        if tests1.is_empty() { "no tests ✓" } else { "UNEXPECTED" }
    );
    assert!(tests1.is_empty(), "Should prune infeasible path: x<0 ∧ x==0");

    let infeasible2 = bdd.apply_and(-bv3, bv1); // x>=100 ∧ x<0
    let tests2 = generator.generate(infeasible2);
    println!("  Constraint: (x ≥ 100) ∧ (x < 0)");
    println!(
        "  Result:     {} (infeasible → pruned)\n",
        if tests2.is_empty() { "no tests ✓" } else { "UNEXPECTED" }
    );
    assert!(tests2.is_empty(), "Should prune infeasible path: x>=100 ∧ x<0");

    println!("══════════════════════════════════════════════════════════════");
    println!("  All assertions passed. T-BDD demo complete!");
    println!("══════════════════════════════════════════════════════════════");
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_categorize_function() {
        assert_eq!(categorize(-5), "negative");
        assert_eq!(categorize(0), "zero");
        assert_eq!(categorize(50), "small positive");
        assert_eq!(categorize(100), "large positive");
        assert_eq!(categorize(1000), "large positive");
    }
}
