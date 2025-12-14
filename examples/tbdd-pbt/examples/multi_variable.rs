//! Multi-variable and relational constraints example.
//!
//! This example demonstrates T-BDD with:
//! 1. Multi-variable predicates (x < y, x == y)
//! 2. Relational theory solver using difference bound matrices
//! 3. Complex function analysis with two parameters
//!
//! Run with: `cargo run -p tbdd-pbt --example multi_variable`

use ananke_bdd::bdd::Bdd;
use tbdd_pbt::{GeneratorConfig, Predicate, PredicateUniverse, RelationalSolver, TestGenerator};

/// Compare two values and return ordering description.
fn compare(x: i64, y: i64) -> &'static str {
    if x < y {
        "x less than y"
    } else if x == y {
        "x equals y"
    } else {
        "x greater than y"
    }
}

/// Min function with branching.
fn my_min(x: i64, y: i64) -> i64 {
    if x < y {
        x
    } else {
        y
    }
}

/// Max function with branching.
fn my_max(x: i64, y: i64) -> i64 {
    if x > y {
        x
    } else {
        y
    }
}

/// Absolute difference.
fn abs_diff(x: i64, y: i64) -> i64 {
    if x >= y {
        x - y
    } else {
        y - x
    }
}

/// Clamp value to range.
fn clamp(x: i64, lo: i64, hi: i64) -> i64 {
    if x < lo {
        lo
    } else if x > hi {
        hi
    } else {
        x
    }
}

fn main() {
    println!("═══════════════════════════════════════════════════════════════");
    println!("  T-BDD: Multi-Variable and Relational Constraints");
    println!("═══════════════════════════════════════════════════════════════\n");

    demo_compare();
    demo_min_max();
    demo_abs_diff();
    demo_clamp();

    println!("═══════════════════════════════════════════════════════════════");
    println!("  All multi-variable demos completed!");
    println!("═══════════════════════════════════════════════════════════════");
}

fn demo_compare() {
    println!("── DEMO: compare(x, y) ─────────────────────────────────────────");
    println!("  fn compare(x: i64, y: i64) -> &str {{");
    println!("      if x < y {{ \"x less than y\" }}");
    println!("      else if x == y {{ \"x equals y\" }}");
    println!("      else {{ \"x greater than y\" }}");
    println!("  }}\n");

    let bdd = Bdd::default();
    let mut universe = PredicateUniverse::new();

    // Register relational predicates
    let v1 = universe.register(Predicate::lt("x", "y"), &bdd); // x < y
    let v2 = universe.register(Predicate::eq("x", "y"), &bdd); // x == y

    println!("  Predicates:");
    println!("    P1: x < y   (BDD var {})", v1.id());
    println!("    P2: x == y  (BDD var {})\n", v2.id());

    let bv1 = bdd.mk_var(v1);
    let bv2 = bdd.mk_var(v2);

    // Path constraints
    let path_lt = bv1; // x < y
    let path_eq = bdd.apply_and(-bv1, bv2); // ¬(x<y) ∧ (x==y)
    let path_gt = bdd.apply_and(-bv1, -bv2); // ¬(x<y) ∧ ¬(x==y)

    // Use relational solver for multi-variable constraints
    let solver = RelationalSolver::with_bounds(-100, 100);
    let config = GeneratorConfig::default();
    let generator = TestGenerator::new(&bdd, &universe, &solver, config);

    let path_info = [
        ("x less than y", path_lt, "x < y"),
        ("x equals y", path_eq, "¬(x<y) ∧ (x==y)"),
        ("x greater than y", path_gt, "¬(x<y) ∧ ¬(x==y)"),
    ];

    println!("  Path Analysis:");
    for (name, constraint, _formula) in &path_info {
        let tests = generator.generate(*constraint);
        print!("    \"{}\": ", name);

        if let Some(test) = tests.first() {
            let x = test.witness.get("x").unwrap_or(0);
            let y = test.witness.get("y").unwrap_or(0);
            let actual = compare(x, y);
            let status = if actual == *name { "✓" } else { "✗" };
            println!("x={}, y={} → \"{}\" {}", x, y, actual, status);
            assert_eq!(actual, *name);
        } else {
            println!("⚠ No witness (relational solver returned Unknown)");
        }
    }

    // Theory pruning: x < y AND x == y should be UNSAT
    let infeasible = bdd.apply_and(bv1, bv2);
    let tests = generator.generate(infeasible);
    println!("\n  Theory Pruning:");
    println!(
        "    (x < y) ∧ (x == y) → {} ✓\n",
        if tests.is_empty() { "pruned" } else { "NOT pruned" }
    );
}

fn demo_min_max() {
    println!("── DEMO: my_min/my_max ─────────────────────────────────────────");

    let bdd = Bdd::default();
    let mut universe = PredicateUniverse::new();

    let v1 = universe.register(Predicate::lt("x", "y"), &bdd);
    let bv1 = bdd.mk_var(v1);

    let solver = RelationalSolver::with_bounds(-50, 50);
    let config = GeneratorConfig::default();
    let generator = TestGenerator::new(&bdd, &universe, &solver, config);

    // Test min when x < y
    let tests_lt = generator.generate(bv1);
    if let Some(test) = tests_lt.first() {
        let x = test.witness.get("x").unwrap_or(0);
        let y = test.witness.get("y").unwrap_or(0);
        let min_result = my_min(x, y);
        let max_result = my_max(x, y);
        println!("  When x < y (x={}, y={}):", x, y);
        println!(
            "    my_min → {} (expected x={}) {}",
            min_result,
            x,
            if min_result == x { "✓" } else { "✗" }
        );
        println!(
            "    my_max → {} (expected y={}) {}",
            max_result,
            y,
            if max_result == y { "✓" } else { "✗" }
        );
        assert_eq!(min_result, x);
        assert_eq!(max_result, y);
    }

    // Test min when x >= y
    let tests_ge = generator.generate(-bv1);
    if let Some(test) = tests_ge.first() {
        let x = test.witness.get("x").unwrap_or(0);
        let y = test.witness.get("y").unwrap_or(0);
        let min_result = my_min(x, y);
        let max_result = my_max(x, y);
        println!("  When x >= y (x={}, y={}):", x, y);
        println!(
            "    my_min → {} (expected y={}) {}",
            min_result,
            y,
            if min_result == y { "✓" } else { "✗" }
        );
        println!(
            "    my_max → {} (expected x={}) {}",
            max_result,
            x,
            if max_result == x { "✓" } else { "✗" }
        );
        assert_eq!(min_result, y);
        assert_eq!(max_result, x);
    }
    println!();
}

fn demo_abs_diff() {
    println!("── DEMO: abs_diff ──────────────────────────────────────────────");
    println!("  fn abs_diff(x, y) = if x >= y {{ x - y }} else {{ y - x }}\n");

    let bdd = Bdd::default();
    let mut universe = PredicateUniverse::new();

    let v1 = universe.register(Predicate::ge("x", 0), &bdd);
    let v2 = universe.register(Predicate::ge("y", 0), &bdd);
    let v3 = universe.register(Predicate::gt("x", "y"), &bdd);

    let bv1 = bdd.mk_var(v1);
    let bv2 = bdd.mk_var(v2);
    let bv3 = bdd.mk_var(v3);

    let solver = RelationalSolver::with_bounds(-100, 100);
    let config = GeneratorConfig::default();
    let generator = TestGenerator::new(&bdd, &universe, &solver, config);

    // Test with x > y (both positive)
    let constraint = bdd.apply_and(bdd.apply_and(bv1, bv2), bv3);
    let tests = generator.generate(constraint);
    if let Some(test) = tests.first() {
        let x = test.witness.get("x").unwrap_or(0);
        let y = test.witness.get("y").unwrap_or(0);
        let result = abs_diff(x, y);
        let expected = (x - y).abs();
        println!("  x={}, y={} (x > y, both positive):", x, y);
        println!(
            "    abs_diff → {} (expected {}) {}",
            result,
            expected,
            if result == expected { "✓" } else { "✗" }
        );
        assert_eq!(result, expected);
    }

    // Test with x < y
    let constraint2 = bdd.apply_and(bdd.apply_and(bv1, bv2), -bv3);
    let tests2 = generator.generate(constraint2);
    if let Some(test) = tests2.first() {
        let x = test.witness.get("x").unwrap_or(0);
        let y = test.witness.get("y").unwrap_or(0);
        let result = abs_diff(x, y);
        let expected = (x - y).abs();
        println!("  x={}, y={} (x <= y):", x, y);
        println!(
            "    abs_diff → {} (expected {}) {}",
            result,
            expected,
            if result == expected { "✓" } else { "✗" }
        );
        assert_eq!(result, expected);
    }
    println!();
}

fn demo_clamp() {
    println!("── DEMO: clamp ─────────────────────────────────────────────────");
    println!("  fn clamp(x, lo, hi) = if x < lo {{ lo }} else if x > hi {{ hi }} else {{ x }}\n");

    let bdd = Bdd::default();
    let mut universe = PredicateUniverse::new();

    // Predicates for clamp(x, 0, 100)
    let v1 = universe.register(Predicate::lt("x", 0), &bdd); // x < lo
    let v2 = universe.register(Predicate::gt("x", 100), &bdd); // x > hi

    let bv1 = bdd.mk_var(v1);
    let bv2 = bdd.mk_var(v2);

    let solver = tbdd_pbt::IntervalSolver::with_bounds(-200, 200);
    let config = GeneratorConfig::default();
    let generator = TestGenerator::new(&bdd, &universe, &solver, config);

    let lo = 0;
    let hi = 100;

    // Path 1: x < lo → returns lo
    let tests1 = generator.generate(bv1);
    if let Some(test) = tests1.first() {
        let x = test.witness.get("x").unwrap_or(0);
        let result = clamp(x, lo, hi);
        println!(
            "  x={} (x < lo={}): clamp → {} {}",
            x,
            lo,
            result,
            if result == lo { "✓" } else { "✗" }
        );
        assert_eq!(result, lo);
    }

    // Path 2: x > hi → returns hi
    let tests2 = generator.generate(bv2);
    if let Some(test) = tests2.first() {
        let x = test.witness.get("x").unwrap_or(0);
        let result = clamp(x, lo, hi);
        println!(
            "  x={} (x > hi={}): clamp → {} {}",
            x,
            hi,
            result,
            if result == hi { "✓" } else { "✗" }
        );
        assert_eq!(result, hi);
    }

    // Path 3: lo <= x <= hi → returns x
    let in_range = bdd.apply_and(-bv1, -bv2);
    let tests3 = generator.generate(in_range);
    if let Some(test) = tests3.first() {
        let x = test.witness.get("x").unwrap_or(0);
        let result = clamp(x, lo, hi);
        println!("  x={} (in range): clamp → {} {}", x, result, if result == x { "✓" } else { "✗" });
        assert_eq!(result, x);
    }
    println!();
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_compare() {
        assert_eq!(compare(1, 5), "x less than y");
        assert_eq!(compare(5, 5), "x equals y");
        assert_eq!(compare(5, 1), "x greater than y");
    }

    #[test]
    fn test_my_min() {
        assert_eq!(my_min(3, 5), 3);
        assert_eq!(my_min(5, 3), 3);
        assert_eq!(my_min(4, 4), 4);
    }

    #[test]
    fn test_my_max() {
        assert_eq!(my_max(3, 5), 5);
        assert_eq!(my_max(5, 3), 5);
        assert_eq!(my_max(4, 4), 4);
    }

    #[test]
    fn test_abs_diff() {
        assert_eq!(abs_diff(10, 3), 7);
        assert_eq!(abs_diff(3, 10), 7);
        assert_eq!(abs_diff(5, 5), 0);
    }

    #[test]
    fn test_clamp() {
        assert_eq!(clamp(-10, 0, 100), 0);
        assert_eq!(clamp(50, 0, 100), 50);
        assert_eq!(clamp(200, 0, 100), 100);
    }
}
