//! Path explosion and coverage-guided testing example.
//!
//! This example demonstrates:
//! 1. Handling programs with exponential path counts
//! 2. BDD compaction of path spaces
//! 3. Coverage-guided incremental test generation
//! 4. Statistics and coverage tracking
//!
//! Run with: `cargo run -p tbdd-pbt --example coverage`

use std::collections::HashMap;

use bdd_rs::bdd::Bdd;
use tbdd_pbt::{
    CheckResult, CoverageTracker, GeneratorConfig, IntervalSolver, Predicate, PredicateUniverse, Property, PropertyChecker, TestGenerator,
};

/// Function with multiple independent conditions (path explosion).
/// 3 independent conditions → 2³ = 8 paths
fn classify_3bits(a: i64, b: i64, c: i64) -> u8 {
    let mut result = 0u8;
    if a > 0 {
        result |= 1;
    }
    if b > 0 {
        result |= 2;
    }
    if c > 0 {
        result |= 4;
    }
    result
}

/// Function with 5 independent conditions → 2⁵ = 32 paths
fn classify_5bits(a: i64, b: i64, c: i64, d: i64, e: i64) -> u8 {
    let mut result = 0u8;
    if a > 0 {
        result |= 1;
    }
    if b > 0 {
        result |= 2;
    }
    if c > 0 {
        result |= 4;
    }
    if d > 0 {
        result |= 8;
    }
    if e > 0 {
        result |= 16;
    }
    result
}

/// Function with nested conditions (dependent paths).
fn nested_classify(x: i64) -> &'static str {
    if x < 0 {
        if x < -100 {
            "very negative"
        } else if x < -10 {
            "moderately negative"
        } else {
            "slightly negative"
        }
    } else if x == 0 {
        "zero"
    } else {
        if x > 100 {
            "very positive"
        } else if x > 10 {
            "moderately positive"
        } else {
            "slightly positive"
        }
    }
}

fn main() {
    println!("═══════════════════════════════════════════════════════════════");
    println!("  T-BDD: Path Explosion and Coverage-Guided Testing");
    println!("═══════════════════════════════════════════════════════════════\n");

    demo_path_explosion_3();
    demo_path_explosion_5();
    demo_nested_paths();
    demo_coverage_guided();

    println!("═══════════════════════════════════════════════════════════════");
    println!("  All coverage demos completed!");
    println!("═══════════════════════════════════════════════════════════════");
}

fn demo_path_explosion_3() {
    println!("── DEMO: 3-bit classifier (8 paths) ────────────────────────────");
    println!("  fn classify_3bits(a, b, c) → result |= 1*(a>0) | 2*(b>0) | 4*(c>0)\n");

    let bdd = Bdd::default();
    let mut universe = PredicateUniverse::new();

    universe.register(Predicate::gt("a", 0), &bdd);
    universe.register(Predicate::gt("b", 0), &bdd);
    universe.register(Predicate::gt("c", 0), &bdd);

    println!("  Path space analysis:");
    println!("    Variables: 3 (a>0, b>0, c>0)");
    println!("    Theoretical paths: 2³ = 8");

    let all_paths = bdd.one();
    println!("    BDD size: {} node(s)", bdd.size(all_paths));

    let solver = IntervalSolver::with_bounds(-100, 100);
    let config = GeneratorConfig {
        max_tests: 100,
        randomize: false,
    };
    let generator = TestGenerator::new(&bdd, &universe, &solver, config);

    let tests = generator.generate(all_paths);
    println!("    Tests generated: {}\n", tests.len());

    println!("  Path enumeration:");
    let mut seen_results = HashMap::new();
    for test in &tests {
        let a = test.witness.get("a").unwrap_or(0);
        let b = test.witness.get("b").unwrap_or(0);
        let c = test.witness.get("c").unwrap_or(0);
        let result = classify_3bits(a, b, c);
        *seen_results.entry(result).or_insert(0) += 1;
        println!("    a={:4}, b={:4}, c={:4} → result = {} (0b{:03b})", a, b, c, result, result);
    }

    println!("\n  Coverage: {} distinct results out of 8 possible\n", seen_results.len());

    // Property check
    let checker = PropertyChecker::new(&bdd, &universe, &solver);
    let prop = Property::new("result in [0, 7]", |w| {
        let a = w.get("a").unwrap_or(0);
        let b = w.get("b").unwrap_or(0);
        let c = w.get("c").unwrap_or(0);
        classify_3bits(a, b, c) <= 7
    });

    print!("  Property \"{}\": ", prop.name);
    match checker.check(&prop, all_paths) {
        CheckResult::Pass { test_count, .. } => println!("PASSED ({} tests) ✓\n", test_count),
        other => println!("{:?}\n", other),
    }
}

fn demo_path_explosion_5() {
    println!("── DEMO: 5-bit classifier (32 paths) ───────────────────────────");
    println!("  fn classify_5bits(a, b, c, d, e) → 5 independent conditions\n");

    let bdd = Bdd::default();
    let mut universe = PredicateUniverse::new();

    universe.register(Predicate::gt("a", 0), &bdd);
    universe.register(Predicate::gt("b", 0), &bdd);
    universe.register(Predicate::gt("c", 0), &bdd);
    universe.register(Predicate::gt("d", 0), &bdd);
    universe.register(Predicate::gt("e", 0), &bdd);

    println!("  Path space analysis:");
    println!("    Variables: 5");
    println!("    Theoretical paths: 2⁵ = 32");

    let all_paths = bdd.one();
    println!("    BDD size: {} node(s)", bdd.size(all_paths));

    let solver = IntervalSolver::with_bounds(-100, 100);
    let config = GeneratorConfig {
        max_tests: 100,
        randomize: false,
    };
    let generator = TestGenerator::new(&bdd, &universe, &solver, config);

    let tests = generator.generate(all_paths);
    println!("    Tests generated: {}", tests.len());

    // Count distinct results
    let mut seen_results = HashMap::new();
    for test in &tests {
        let a = test.witness.get("a").unwrap_or(0);
        let b = test.witness.get("b").unwrap_or(0);
        let c = test.witness.get("c").unwrap_or(0);
        let d = test.witness.get("d").unwrap_or(0);
        let e = test.witness.get("e").unwrap_or(0);
        let result = classify_5bits(a, b, c, d, e);
        *seen_results.entry(result).or_insert(0) += 1;
    }

    println!("    Distinct results: {} out of 32 possible\n", seen_results.len());
}

fn demo_nested_paths() {
    println!("── DEMO: Nested conditions (7 paths) ───────────────────────────");
    println!("  fn nested_classify(x) → hierarchical branching\n");

    let bdd = Bdd::default();
    let mut universe = PredicateUniverse::new();

    // Predicates for nested structure
    let v1 = universe.register(Predicate::lt("x", 0), &bdd);
    let v2 = universe.register(Predicate::lt("x", -100), &bdd);
    let v3 = universe.register(Predicate::lt("x", -10), &bdd);
    let v4 = universe.register(Predicate::eq("x", 0), &bdd);
    let v5 = universe.register(Predicate::gt("x", 100), &bdd);
    let v6 = universe.register(Predicate::gt("x", 10), &bdd);

    let bv1 = bdd.mk_var(v1);
    let bv2 = bdd.mk_var(v2);
    let bv3 = bdd.mk_var(v3);
    let bv4 = bdd.mk_var(v4);
    let bv5 = bdd.mk_var(v5);
    let bv6 = bdd.mk_var(v6);

    // Build path BDDs
    let paths = [
        ("very negative", bdd.apply_and(bv1, bv2)),
        ("moderately negative", bdd.apply_and(bdd.apply_and(bv1, -bv2), bv3)),
        ("slightly negative", bdd.apply_and(bdd.apply_and(bv1, -bv2), -bv3)),
        ("zero", bdd.apply_and(-bv1, bv4)),
        ("very positive", bdd.apply_and(bdd.apply_and(-bv1, -bv4), bv5)),
        (
            "moderately positive",
            bdd.apply_and(bdd.apply_and(bdd.apply_and(-bv1, -bv4), -bv5), bv6),
        ),
        (
            "slightly positive",
            bdd.apply_and(bdd.apply_and(bdd.apply_and(-bv1, -bv4), -bv5), -bv6),
        ),
    ];

    let all_paths = paths.iter().map(|(_, p)| *p).reduce(|a, b| bdd.apply_or(a, b)).unwrap();

    println!("  Path space analysis:");
    println!("    Predicates: 6");
    println!("    Actual paths: 7 (nested structure reduces combinations)");
    println!("    Combined BDD size: {} node(s)\n", bdd.size(all_paths));

    let solver = IntervalSolver::with_bounds(-200, 200);
    let config = GeneratorConfig::default();
    let generator = TestGenerator::new(&bdd, &universe, &solver, config);

    println!("  Path enumeration:");
    for (expected, path_bdd) in &paths {
        let tests = generator.generate(*path_bdd);
        if let Some(test) = tests.first() {
            let x = test.witness.get("x").unwrap_or(0);
            let actual = nested_classify(x);
            let status = if actual == *expected { "✓" } else { "✗" };
            println!("    x={:4} → \"{}\" {}", x, actual, status);
            assert_eq!(actual, *expected);
        }
    }
    println!();
}

fn demo_coverage_guided() {
    println!("── DEMO: Coverage-guided incremental testing ───────────────────");
    println!("  Simulating incremental test execution with coverage tracking\n");

    let bdd = Bdd::default();
    let mut universe = PredicateUniverse::new();

    let v1 = universe.register(Predicate::lt("x", 0), &bdd);
    let v2 = universe.register(Predicate::lt("x", -10), &bdd);
    let v3 = universe.register(Predicate::ge("x", 100), &bdd);

    let bv1 = bdd.mk_var(v1);
    let bv2 = bdd.mk_var(v2);
    let bv3 = bdd.mk_var(v3);

    // Target paths
    let targets = [
        bdd.apply_and(bv1, bv2),   // x < -10
        bdd.apply_and(bv1, -bv2),  // -10 <= x < 0
        bdd.apply_and(-bv1, -bv3), // 0 <= x < 100
        bv3,                       // x >= 100
    ];
    let target_bdd = targets.iter().copied().reduce(|a, b| bdd.apply_or(a, b)).unwrap();

    let mut coverage = CoverageTracker::new(&bdd, target_bdd);

    println!("  Target regions:");
    println!("    1. x < -10      (deep negative)");
    println!("    2. -10 <= x < 0 (shallow negative)");
    println!("    3. 0 <= x < 100 (normal)");
    println!("    4. x >= 100     (large)\n");

    // Simulate incremental test execution
    let test_sequence = [
        (HashMap::from([(v1, true), (v2, true)]), "x = -50", "deep negative"),
        (HashMap::from([(v1, true), (v2, false)]), "x = -5", "shallow negative"),
        (HashMap::from([(v1, false), (v3, false)]), "x = 50", "normal"),
        (HashMap::from([(v1, false), (v3, true)]), "x = 200", "large"),
    ];

    println!("  Incremental coverage:");
    for (i, (assignments, input, region)) in test_sequence.iter().enumerate() {
        coverage.record_assignments(assignments);
        let summary = coverage.summary();
        let status = if summary.is_complete { "complete" } else { "partial" };
        println!(
            "    Test {}: {} ({}) → {:.0}% coverage ({})",
            i + 1,
            input,
            region,
            summary.predicate_coverage_ratio * 100.0,
            status
        );
    }

    let final_summary = coverage.summary();
    println!("\n  Final coverage:");
    println!("    Predicate coverage: {:.0}%", final_summary.predicate_coverage_ratio * 100.0);
    println!("    Tests executed: {}", final_summary.test_count);
    println!(
        "    Status: {}\n",
        if final_summary.is_complete {
            "All target paths covered ✓"
        } else {
            "Incomplete"
        }
    );
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_classify_3bits() {
        assert_eq!(classify_3bits(-1, -1, -1), 0b000);
        assert_eq!(classify_3bits(1, -1, -1), 0b001);
        assert_eq!(classify_3bits(-1, 1, -1), 0b010);
        assert_eq!(classify_3bits(1, 1, -1), 0b011);
        assert_eq!(classify_3bits(-1, -1, 1), 0b100);
        assert_eq!(classify_3bits(1, 1, 1), 0b111);
    }

    #[test]
    fn test_nested_classify() {
        assert_eq!(nested_classify(-150), "very negative");
        assert_eq!(nested_classify(-50), "moderately negative");
        assert_eq!(nested_classify(-5), "slightly negative");
        assert_eq!(nested_classify(0), "zero");
        assert_eq!(nested_classify(5), "slightly positive");
        assert_eq!(nested_classify(50), "moderately positive");
        assert_eq!(nested_classify(150), "very positive");
    }
}
