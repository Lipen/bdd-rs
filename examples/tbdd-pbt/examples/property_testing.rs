//! Property-based testing example with counterexample search.
//!
//! This example demonstrates:
//! 1. Defining properties that functions should satisfy
//! 2. Using PropertyChecker to find counterexamples
//! 3. Shrinking counterexamples to minimal failing inputs
//! 4. Testing buggy implementations
//!
//! Run with: `cargo run -p tbdd-pbt --example property_testing`

use bdd_rs::bdd::Bdd;
use tbdd_pbt::{CheckResult, IntervalSolver, Predicate, PredicateUniverse, Property, PropertyChecker, Witness};

/// A buggy absolute value function.
fn buggy_abs(x: i64) -> i64 {
    if x < 0 {
        -x
    } else if x > 0 {
        x
    } else {
        1 // BUG: returns 1 for 0 instead of 0
    }
}

/// Correct absolute value.
fn correct_abs(x: i64) -> i64 {
    if x < 0 {
        -x
    } else {
        x
    }
}

/// Buggy factorial (overflows for large inputs).
#[allow(dead_code)]
fn buggy_factorial(n: i64) -> i64 {
    if n <= 1 {
        1
    } else {
        n * buggy_factorial(n - 1) // Can overflow!
    }
}

/// Division that doesn't check for zero.
#[allow(dead_code)]
fn unsafe_div(a: i64, b: i64) -> i64 {
    a / b // Will panic on b == 0!
}

fn main() {
    println!("═══════════════════════════════════════════════════════════════");
    println!("  T-BDD: Property-Based Testing with Counterexamples");
    println!("═══════════════════════════════════════════════════════════════\n");

    demo_correct_abs();
    demo_buggy_abs();
    demo_multiple_properties();
    demo_preconditions();

    println!("═══════════════════════════════════════════════════════════════");
    println!("  All property testing demos completed!");
    println!("═══════════════════════════════════════════════════════════════");
}

fn demo_correct_abs() {
    println!("── DEMO: Testing correct_abs ───────────────────────────────────");

    let bdd = Bdd::default();
    let mut universe = PredicateUniverse::new();

    // Setup predicates covering all paths
    let v1 = universe.register(Predicate::lt("x", 0), &bdd);
    let v2 = universe.register(Predicate::eq("x", 0), &bdd);

    let _bv1 = bdd.mk_var(v1);
    let _bv2 = bdd.mk_var(v2);

    let all_paths = bdd.one();
    let solver = IntervalSolver::with_bounds(-100, 100);
    let checker = PropertyChecker::new(&bdd, &universe, &solver);

    // Property 1: result is always non-negative
    let prop_nonneg = Property::new("result is non-negative", |w| {
        let x = w.get("x").unwrap_or(0);
        correct_abs(x) >= 0
    });

    print!("  Property: \"{}\" ... ", prop_nonneg.name);
    match checker.check(&prop_nonneg, all_paths) {
        CheckResult::Pass { test_count, .. } => {
            println!("PASSED ({} tests) ✓", test_count);
        }
        CheckResult::Fail { counterexample, .. } => {
            println!("FAILED! Counterexample: {:?}", counterexample);
        }
        CheckResult::Vacuous => {
            println!("VACUOUS (no tests)");
        }
    }

    // Property 2: abs(x) == abs(-x) (symmetry)
    let prop_sym = Property::new("abs(x) == abs(-x)", |w| {
        let x = w.get("x").unwrap_or(0);
        if x == i64::MIN {
            true // Avoid overflow
        } else {
            correct_abs(x) == correct_abs(-x)
        }
    });

    print!("  Property: \"{}\" ... ", prop_sym.name);
    match checker.check(&prop_sym, all_paths) {
        CheckResult::Pass { test_count, .. } => {
            println!("PASSED ({} tests) ✓", test_count);
        }
        CheckResult::Fail { counterexample, .. } => {
            println!("FAILED! Counterexample: {:?}", counterexample);
        }
        CheckResult::Vacuous => {
            println!("VACUOUS (no tests)");
        }
    }

    // Property 3: abs(abs(x)) == abs(x) (idempotent)
    let prop_idem = Property::new("abs(abs(x)) == abs(x)", |w| {
        let x = w.get("x").unwrap_or(0);
        correct_abs(correct_abs(x)) == correct_abs(x)
    });

    print!("  Property: \"{}\" ... ", prop_idem.name);
    match checker.check(&prop_idem, all_paths) {
        CheckResult::Pass { test_count, .. } => {
            println!("PASSED ({} tests) ✓\n", test_count);
        }
        CheckResult::Fail { counterexample, .. } => {
            println!("FAILED! Counterexample: {:?}\n", counterexample);
        }
        CheckResult::Vacuous => {
            println!("VACUOUS (no tests)\n");
        }
    }
}

fn demo_buggy_abs() {
    println!("── DEMO: Finding bug in buggy_abs ──────────────────────────────");
    println!("  buggy_abs has a bug: returns 1 for input 0\n");

    let bdd = Bdd::default();
    let mut universe = PredicateUniverse::new();

    let v1 = universe.register(Predicate::lt("x", 0), &bdd);
    let v2 = universe.register(Predicate::eq("x", 0), &bdd);

    let bv1 = bdd.mk_var(v1);
    let bv2 = bdd.mk_var(v2);

    let solver = IntervalSolver::with_bounds(-100, 100);
    let checker = PropertyChecker::new(&bdd, &universe, &solver);

    // Property: buggy_abs(x) == correct_abs(x)
    let prop = Property::new("buggy_abs(x) == correct_abs(x)", |w| {
        let x = w.get("x").unwrap_or(0);
        buggy_abs(x) == correct_abs(x)
    });

    // Test on all paths
    println!("  Testing on all paths:");
    let all_paths = bdd.one();
    print!("    {} ... ", prop.name);
    match checker.check(&prop, all_paths) {
        CheckResult::Pass { test_count, .. } => {
            println!("PASSED ({} tests) - bug not found!", test_count);
        }
        CheckResult::Fail { counterexample, .. } => {
            let x = counterexample.get("x").unwrap_or(0);
            println!("FAILED!");
            println!("    Counterexample: x = {}", x);
            println!("    buggy_abs({}) = {}", x, buggy_abs(x));
            println!("    correct_abs({}) = {}", x, correct_abs(x));
        }
        CheckResult::Vacuous => {
            println!("VACUOUS (no tests)");
        }
    }

    // Targeted test on x == 0 path
    println!("\n  Targeted testing on x == 0 path:");
    let zero_path = bdd.apply_and(-bv1, bv2);
    print!("    {} ... ", prop.name);
    match checker.check(&prop, zero_path) {
        CheckResult::Pass { .. } => {
            println!("PASSED - bug not found!");
        }
        CheckResult::Fail { counterexample, .. } => {
            let x = counterexample.get("x").unwrap_or(0);
            println!("FAILED ✓ (bug found!)");
            println!("    x = {} → buggy_abs returns {}, should be {}\n", x, buggy_abs(x), correct_abs(x));
        }
        CheckResult::Vacuous => {
            println!("VACUOUS\n");
        }
    }
}

fn demo_multiple_properties() {
    println!("── DEMO: Multiple properties at once ───────────────────────────");

    let bdd = Bdd::default();
    let mut universe = PredicateUniverse::new();

    universe.register(Predicate::lt("x", 0), &bdd);
    universe.register(Predicate::eq("x", 0), &bdd);
    universe.register(Predicate::gt("x", 100), &bdd);

    let all_paths = bdd.one();
    let solver = IntervalSolver::with_bounds(-1000, 1000);
    let checker = PropertyChecker::new(&bdd, &universe, &solver);

    let properties: [Property<fn(&Witness) -> bool>; 4] = [
        Property::new("x + 0 == x", |w: &Witness| {
            let x = w.get("x").unwrap_or(0);
            x + 0 == x
        }),
        Property::new("x * 1 == x", |w: &Witness| {
            let x = w.get("x").unwrap_or(0);
            x * 1 == x
        }),
        Property::new("x - x == 0", |w: &Witness| {
            let x = w.get("x").unwrap_or(0);
            x - x == 0
        }),
        Property::new("-(-x) == x", |w: &Witness| {
            let x = w.get("x").unwrap_or(0);
            if x == i64::MIN {
                true // Avoid overflow
            } else {
                -(-x) == x
            }
        }),
    ];

    for prop in &properties {
        print!("  {} ... ", prop.name);
        match checker.check(prop, all_paths) {
            CheckResult::Pass { test_count, .. } => println!("PASSED ({} tests) ✓", test_count),
            CheckResult::Fail { counterexample, .. } => println!("FAILED! x={:?}", counterexample.get("x")),
            CheckResult::Vacuous => println!("VACUOUS"),
        }
    }
    println!();
}

fn demo_preconditions() {
    println!("── DEMO: Properties with preconditions ─────────────────────────");
    println!("  Testing division only when divisor != 0\n");

    let bdd = Bdd::default();
    let mut universe = PredicateUniverse::new();

    // Predicates for dividend and divisor
    let v1 = universe.register(Predicate::eq("b", 0), &bdd); // b == 0

    let bv1 = bdd.mk_var(v1);

    // Precondition: b != 0
    let precondition = -bv1;

    let solver = IntervalSolver::with_bounds(-100, 100);
    let checker = PropertyChecker::new(&bdd, &universe, &solver);

    // Property: (a / b) * b + (a % b) == a (when b != 0)
    let prop = Property::new("division property: (a/b)*b + a%b == a", |w| {
        let a = w.get("a").unwrap_or(1);
        let b = w.get("b").unwrap_or(1);
        if b == 0 {
            true // Skip (precondition not met)
        } else {
            (a / b) * b + (a % b) == a
        }
    });

    print!("  {} (with b != 0) ... ", prop.name);
    match checker.check(&prop, precondition) {
        CheckResult::Pass { test_count, .. } => println!("PASSED ({} tests) ✓", test_count),
        CheckResult::Fail { counterexample, .. } => {
            let a = counterexample.get("a");
            let b = counterexample.get("b");
            println!("FAILED! a={:?}, b={:?}", a, b);
        }
        CheckResult::Vacuous => println!("VACUOUS"),
    }

    // Show what happens without precondition (would panic)
    println!("\n  Note: Without precondition, b=0 could cause panic!");
    println!("  T-BDD's theory pruning ensures we only test valid inputs.\n");
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_correct_abs() {
        assert_eq!(correct_abs(-5), 5);
        assert_eq!(correct_abs(0), 0);
        assert_eq!(correct_abs(5), 5);
    }

    #[test]
    fn test_buggy_abs_has_bug() {
        assert_eq!(buggy_abs(-5), 5);
        assert_eq!(buggy_abs(0), 1); // The bug!
        assert_eq!(buggy_abs(5), 5);
        assert_ne!(buggy_abs(0), correct_abs(0));
    }
}
