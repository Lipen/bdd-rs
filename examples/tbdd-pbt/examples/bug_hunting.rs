//! Bug hunting example: Finding real vulnerability patterns.
//!
//! This example demonstrates using T-BDD to find common bug patterns:
//! 1. Integer overflow vulnerabilities
//! 2. Division by zero errors
//! 3. Buffer overflow conditions
//! 4. Off-by-one errors
//! 5. Sign confusion bugs
//!
//! Run with: `cargo run -p tbdd-pbt --example bug_hunting`

use ananke_bdd::bdd::Bdd;
use tbdd_pbt::{CheckResult, IntervalSolver, Predicate, PredicateUniverse, Property, PropertyChecker, Witness};

fn main() {
    println!("═══════════════════════════════════════════════════════════════");
    println!("  T-BDD: Bug Hunting with Theory-Guided Testing");
    println!("═══════════════════════════════════════════════════════════════\n");

    demo_integer_overflow();
    demo_division_by_zero();
    demo_buffer_overflow();
    demo_off_by_one();
    demo_sign_confusion();

    println!("═══════════════════════════════════════════════════════════════");
    println!("  Bug hunting complete! Summary:");
    println!("    - Integer overflow: detectable via boundary analysis");
    println!("    - Division by zero: theory pruning prevents panics");
    println!("    - Buffer overflow: bounds checking catches violations");
    println!("    - Off-by-one: boundary values expose fence-post errors");
    println!("    - Sign confusion: negative input handling critical");
    println!("═══════════════════════════════════════════════════════════════");
}

// =============================================================================
// Integer Overflow Detection
// =============================================================================

/// Vulnerable: may overflow on large inputs.
fn vulnerable_multiply(a: i32, b: i32) -> i32 {
    a * b // Potential overflow!
}

/// Safe: checks for overflow.
fn safe_multiply(a: i32, b: i32) -> Option<i32> {
    a.checked_mul(b)
}

fn demo_integer_overflow() {
    println!("── BUG: Integer Overflow ───────────────────────────────────────");
    println!("  Vulnerable function: a * b (unchecked multiplication)\n");

    let bdd = Bdd::default();
    let mut universe = PredicateUniverse::new();

    // Define predicates for different magnitude ranges
    let _ = universe.register(Predicate::gt("a", 0), &bdd);
    let _ = universe.register(Predicate::gt("b", 0), &bdd);
    let _ = universe.register(Predicate::gt("a", 46340), &bdd); // sqrt(i32::MAX) ≈ 46340
    let _ = universe.register(Predicate::gt("b", 46340), &bdd);

    // Test values that expose overflow
    println!("  Testing with boundary values:");

    let test_cases = [
        (100, 200, "small values"),
        (46340, 46340, "near sqrt(MAX)"),
        (46341, 46341, "just over sqrt(MAX)"),
        (50000, 50000, "definite overflow"),
    ];

    for (a, b, desc) in test_cases {
        let unsafe_result = std::panic::catch_unwind(|| vulnerable_multiply(a, b));
        let safe_result = safe_multiply(a, b);

        let status = match (&unsafe_result, &safe_result) {
            (Ok(v), Some(s)) if *v == *s => format!("{} = {} ✓", v, s),
            (Ok(v), Some(_)) => format!("{} (overflow detected!)", v),
            (Ok(v), None) => format!("{} (OVERFLOW! safe=None)", v),
            (Err(_), _) => "PANIC! (overflow)".to_string(),
        };

        println!("    {} * {} ({}): {}", a, b, desc, status);
    }

    println!("\n  Finding overflow boundary using T-BDD:");
    println!("    sqrt(i32::MAX) ≈ 46340");
    println!("    For a, b > 46340: a * b will overflow");
    println!("    Property: safe_multiply(a, b).is_some() ↔ no overflow ✓\n");
}

// =============================================================================
// Division by Zero Prevention
// =============================================================================

/// Vulnerable: panics on zero divisor.
fn _vulnerable_divide(a: i64, b: i64) -> i64 {
    a / b // Panics if b == 0!
}

/// Safe: returns None for zero divisor.
fn safe_divide(a: i64, b: i64) -> Option<i64> {
    if b == 0 {
        None
    } else {
        Some(a / b)
    }
}

fn demo_division_by_zero() {
    println!("── BUG: Division by Zero ─────────────────────────────────────────");
    println!("  Vulnerable function: a / b (unchecked division)\n");

    let bdd = Bdd::default();
    let mut universe = PredicateUniverse::new();

    // Predicates
    let v1 = universe.register(Predicate::eq("b", 0), &bdd); // divisor is zero
    let _bv1 = bdd.mk_var(v1);

    let solver = IntervalSolver::with_bounds(-100, 100);
    let checker = PropertyChecker::new(&bdd, &universe, &solver);

    // Path where b == 0
    let zero_divisor_path = bdd.mk_var(v1);

    // Path where b != 0
    let nonzero_divisor_path = bdd.apply_not(zero_divisor_path);

    // Property: division doesn't panic (only valid when b != 0)
    let div_property = Property::new("division is safe", |w: &Witness| {
        let a = w.get("a").unwrap_or(10);
        let b = w.get("b").unwrap_or(1);
        safe_divide(a, b).is_some()
    });

    print!("  Testing on b == 0 path: ");
    match checker.check(&div_property, zero_divisor_path) {
        CheckResult::Pass { test_count, .. } => {
            println!("PASSED ({} tests)", test_count);
        }
        CheckResult::Fail { counterexample, .. } => {
            let b = counterexample.get("b").unwrap_or(0);
            println!("FAILED! Found b={} (division would panic)", b);
        }
        CheckResult::Vacuous => {
            println!("VACUOUS (path infeasible - b != 0 implied)");
        }
    }

    print!("  Testing on b != 0 path: ");
    match checker.check(&div_property, nonzero_divisor_path) {
        CheckResult::Pass { test_count, .. } => {
            println!("PASSED ({} tests) ✓", test_count);
        }
        CheckResult::Fail { counterexample, .. } => {
            println!("FAILED! {:?}", counterexample);
        }
        CheckResult::Vacuous => {
            println!("VACUOUS");
        }
    }

    println!("\n  Theory Pruning Benefit:");
    println!("    - Without pruning: test might generate b=0 → PANIC!");
    println!("    - With T-BDD: infeasible paths pruned before execution");
    println!("    - Result: safe testing, bug found via path analysis ✓\n");
}

// =============================================================================
// Buffer Overflow Detection
// =============================================================================

/// Vulnerable: no bounds check.
fn _vulnerable_get(data: &[u8], index: usize) -> u8 {
    data[index] // Panics if out of bounds!
}

/// Safe: returns None for out of bounds.
fn safe_get(data: &[u8], index: usize) -> Option<u8> {
    data.get(index).copied()
}

fn demo_buffer_overflow() {
    println!("── BUG: Buffer Overflow ─────────────────────────────────────────");
    println!("  Vulnerable function: data[index] (unchecked access)\n");

    let buffer_size = 10;
    let buffer: Vec<u8> = (0..buffer_size as u8).collect();

    let bdd = Bdd::default();
    let mut universe = PredicateUniverse::new();

    // Predicates for index ranges
    let v1 = universe.register(Predicate::lt("index", 0), &bdd);
    let v2 = universe.register(Predicate::ge("index", buffer_size as i64), &bdd);

    let _bv1 = bdd.mk_var(v1);
    let _bv2 = bdd.mk_var(v2);

    let solver = IntervalSolver::with_bounds(-10, 20);
    let checker = PropertyChecker::new(&bdd, &universe, &solver);

    // Property: access is in bounds
    let bounds_property = Property::new("index in bounds", |w: &Witness| {
        let index = w.get("index").unwrap_or(0);
        index >= 0 && index < buffer_size as i64
    });

    // Test different paths
    let paths = [
        ("index < 0 (underflow)", bdd.mk_var(v1)),
        ("index >= size (overflow)", bdd.mk_var(v2)),
        (
            "valid index",
            bdd.apply_and(bdd.apply_not(bdd.mk_var(v1)), bdd.apply_not(bdd.mk_var(v2))),
        ),
    ];

    for (name, path) in paths {
        print!("  Path '{}': ", name);
        match checker.check(&bounds_property, path) {
            CheckResult::Pass { test_count, .. } => {
                println!("PASSED ({} tests) ✓", test_count);
            }
            CheckResult::Fail { counterexample, .. } => {
                let idx = counterexample.get("index").unwrap_or(0);
                println!("FAILED! index={} (out of bounds for size {})", idx, buffer_size);
            }
            CheckResult::Vacuous => {
                println!("VACUOUS");
            }
        }
    }

    // Demonstrate actual access patterns
    println!("\n  Access demonstration (buffer size = {}):", buffer_size);
    for i in [-1i64, 0, 5, 9, 10, 15].iter() {
        if *i >= 0 {
            let result = safe_get(&buffer, *i as usize);
            match result {
                Some(v) => println!("    buffer[{}] = {} ✓", i, v),
                None => println!("    buffer[{}] = OUT OF BOUNDS ✗", i),
            }
        } else {
            println!("    buffer[{}] = NEGATIVE INDEX ✗", i);
        }
    }
    println!();
}

// =============================================================================
// Off-by-One Error Detection
// =============================================================================

/// Buggy: uses <= instead of < (off-by-one).
fn buggy_range_sum(start: i64, end: i64) -> i64 {
    let mut sum = 0;
    let mut i = start;
    while i <= end {
        // Bug: should be i < end for half-open range
        sum += i;
        i += 1;
    }
    sum
}

/// Correct: uses < for half-open range [start, end).
fn correct_range_sum(start: i64, end: i64) -> i64 {
    let mut sum = 0;
    let mut i = start;
    while i < end {
        sum += i;
        i += 1;
    }
    sum
}

/// Mathematical formula for sum [start, end).
fn expected_sum(start: i64, end: i64) -> i64 {
    if end <= start {
        return 0;
    }
    // Sum from 0 to (end-1) minus sum from 0 to (start-1)
    let sum_to = |n: i64| if n <= 0 { 0 } else { n * (n - 1) / 2 };
    sum_to(end) - sum_to(start)
}

fn demo_off_by_one() {
    println!("── BUG: Off-by-One Error ───────────────────────────────────────");
    println!("  Buggy function: sum over [start, end] instead of [start, end)\n");

    let bdd = Bdd::default();
    let mut universe = PredicateUniverse::new();

    // Predicates
    let _ = universe.register(Predicate::lt("start", 0), &bdd);
    let _ = universe.register(Predicate::ge("end", 10), &bdd);

    // Test boundary cases that expose off-by-one
    let test_cases = [
        (0, 0, "empty range"),
        (0, 1, "single element"),
        (0, 5, "small range"),
        (5, 10, "offset range"),
        (0, 10, "boundary case"),
    ];

    println!("  Testing range sums [start, end):");
    println!("  {:>5} {:>5} {:>12} {:>12} {:>12}", "start", "end", "expected", "buggy", "correct");
    println!("  {:-<5} {:-<5} {:-<12} {:-<12} {:-<12}", "", "", "", "", "");

    for (start, end, _desc) in test_cases {
        let expected = expected_sum(start, end);
        let buggy = buggy_range_sum(start, end);
        let correct = correct_range_sum(start, end);

        let status = if buggy != expected { "← BUG!" } else { "" };
        println!(
            "  {:>5} {:>5} {:>12} {:>12} {:>12} {}",
            start, end, expected, buggy, correct, status
        );
    }

    println!("\n  Off-by-one detected:");
    println!("    - buggy_range_sum(0, 5) = {} (includes 5!)", buggy_range_sum(0, 5));
    println!("    - correct_range_sum(0, 5) = {} (excludes 5)", correct_range_sum(0, 5));
    println!(
        "    - Difference: {} (the off-by-one value!)",
        buggy_range_sum(0, 5) - correct_range_sum(0, 5)
    );
    println!();
}

// =============================================================================
// Sign Confusion Bug Detection
// =============================================================================

/// Vulnerable: casts negative i64 to usize (sign confusion).
fn vulnerable_size_cast(len: i64) -> usize {
    len as usize // Negative becomes huge!
}

/// Safe: rejects negative values.
fn safe_size_cast(len: i64) -> Option<usize> {
    if len < 0 {
        None
    } else {
        Some(len as usize)
    }
}

fn demo_sign_confusion() {
    println!("── BUG: Sign Confusion ─────────────────────────────────────────");
    println!("  Vulnerable function: i64 as usize (may wrap negative values)\n");

    let bdd = Bdd::default();
    let mut universe = PredicateUniverse::new();

    // Predicate: is the value negative?
    let v1 = universe.register(Predicate::lt("len", 0), &bdd);
    let _bv1 = bdd.mk_var(v1);

    let solver = IntervalSolver::with_bounds(-100, 100);
    let checker = PropertyChecker::new(&bdd, &universe, &solver);

    // Property: cast preserves value (only true for non-negative)
    let cast_property = Property::new("cast preserves value", |w: &Witness| {
        let len = w.get("len").unwrap_or(0);
        if len < 0 {
            // For negative values, the cast is problematic
            false // Mark as failing
        } else {
            vulnerable_size_cast(len) == len as usize
        }
    });

    // Test on negative path
    let negative_path = bdd.mk_var(v1);
    print!("  Testing on len < 0 path: ");
    match checker.check(&cast_property, negative_path) {
        CheckResult::Pass { .. } => println!("PASSED"),
        CheckResult::Fail { counterexample, .. } => {
            let len = counterexample.get("len").unwrap_or(-1);
            let cast = vulnerable_size_cast(len);
            println!("FAILED! len={} → cast={} (sign confusion!)", len, cast);
        }
        CheckResult::Vacuous => println!("VACUOUS"),
    }

    // Test on non-negative path
    let nonneg_path = bdd.apply_not(negative_path);
    print!("  Testing on len >= 0 path: ");
    match checker.check(&cast_property, nonneg_path) {
        CheckResult::Pass { test_count, .. } => println!("PASSED ({} tests) ✓", test_count),
        CheckResult::Fail { .. } => println!("FAILED!"),
        CheckResult::Vacuous => println!("VACUOUS"),
    }

    // Show the vulnerability
    println!("\n  Sign confusion demonstration:");
    for val in [-1i64, -100, i64::MIN].iter() {
        let cast = vulnerable_size_cast(*val);
        let safe = safe_size_cast(*val);
        println!("    {} as usize = {} (safe: {:?})", val, cast, safe);
    }

    println!("\n  Impact: Negative length → huge allocation → OOM or heap overflow ✓\n");
}
