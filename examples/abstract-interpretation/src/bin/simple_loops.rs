//! Simple loop analysis example.
//!
//! Demonstrates basic fixpoint computation with the interval domain.

use abstract_interpretation::*;
use simplelog::*;

fn main() {
    // Initialize logging
    TermLogger::init(
        LevelFilter::Debug,
        Config::default(),
        TerminalMode::Mixed,
        ColorChoice::Auto,
    )
    .unwrap();

    println!("=== Simple Loop Analysis ===\n");

    // Create interval domain
    let domain = IntervalDomain;

    // Create fixpoint engine
    let engine = FixpointEngine {
        domain: domain.clone(),
        widening_threshold: 3,
        narrowing_iterations: 2,
        max_iterations: 100,
    };

    // Example 1: Counter loop
    // let x = 0;
    // while (x < 10) { x = x + 1; }
    println!("Example 1: Counter loop (x := 0; while x < 10 do x := x + 1)");

    let init1 = {
        let mut elem = IntervalElement::new();
        elem.set("x".to_string(), Interval::constant(0));
        elem
    };

    let f1 = |elem: &IntervalElement| {
        // Simulate: x := x + 1, then check x < 10
        let x_int = elem.get("x");
        let incremented = Interval::new(
            x_int.low.add(&Bound::Finite(1)),
            x_int.high.add(&Bound::Finite(1)),
        );

        let mut result = elem.clone();
        result.set("x".to_string(), incremented);

        // Assume x < 10
        let refined = domain.assume(&result, &NumPred::Lt(NumExpr::Var("x".to_string()), NumExpr::Const(10)));
        refined
    };

    let result1 = engine.lfp(init1, f1);
    println!("  Initial: x ∈ [0, 0]");
    println!("  Result:  x ∈ {}", result1.get("x"));
    println!("  (After loop exit: x should be ≥ 10)\n");

    // Example 2: Countdown
    // let x = 100;
    // while (x > 0) { x = x - 1; }
    println!("Example 2: Countdown (x := 100; while x > 0 do x := x - 1)");

    let init2 = {
        let mut elem = IntervalElement::new();
        elem.set("x".to_string(), Interval::constant(100));
        elem
    };

    let f2 = |elem: &IntervalElement| {
        let x_int = elem.get("x");
        let decremented = Interval::new(
            x_int.low.sub(&Bound::Finite(1)),
            x_int.high.sub(&Bound::Finite(1)),
        );

        let mut result = elem.clone();
        result.set("x".to_string(), decremented);

        // Assume x > 0
        let refined = domain.assume(&result, &NumPred::Gt(NumExpr::Var("x".to_string()), NumExpr::Const(0)));
        refined
    };

    let result2 = engine.lfp(init2, f2);
    println!("  Initial: x ∈ [100, 100]");
    println!("  Result:  x ∈ {}", result2.get("x"));
    println!("  (After loop exit: x should be ≤ 0)\n");

    // Example 3: Unbounded loop
    // let x = 0;
    // while (true) { x = x + 1; }
    println!("Example 3: Unbounded loop (x := 0; while true do x := x + 1)");

    let init3 = {
        let mut elem = IntervalElement::new();
        elem.set("x".to_string(), Interval::constant(0));
        elem
    };

    let f3 = |elem: &IntervalElement| {
        let x_int = elem.get("x");
        let incremented = Interval::new(
            x_int.low.add(&Bound::Finite(1)),
            x_int.high.add(&Bound::Finite(1)),
        );

        let mut result = elem.clone();
        result.set("x".to_string(), incremented);
        result
    };

    let result3 = engine.lfp(init3, f3);
    println!("  Initial: x ∈ [0, 0]");
    println!("  Result:  x ∈ {}", result3.get("x"));
    println!("  (Widening extrapolates to [0, +∞])\n");

    println!("=== Analysis Complete ===");
}
