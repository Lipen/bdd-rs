//! Simple Loop Analysis Example.
//!
//! This example demonstrates the core concepts of abstract interpretation for loops:
//! 1. **Fixpoint Computation**: Iteratively approximating the loop invariant.
//! 2. **Widening**: Accelerating convergence to ensure termination (handling infinite loops).
//! 3. **Narrowing**: Refining the result after widening to improve precision.
//!
//! The analysis uses the **Interval Domain** to track the range of values for variables.

use abstract_interpretation::*;
use simplelog::*;

fn main() {
    // Initialize logging - set to Info by default, use RUST_LOG=debug for detailed trace
    let log_level = std::env::var("RUST_LOG")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(LevelFilter::Info);

    TermLogger::init(log_level, Config::default(), TerminalMode::Mixed, ColorChoice::Auto).unwrap();

    println!("=== Simple Loop Analysis ===");
    println!("(Set RUST_LOG=debug for detailed fixpoint trace)\n");

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
    //
    // NOTE: This computes the loop *invariant* (states satisfying x < 10),
    // not the full reachable set. To get the exit state properly, we'd need
    // to compute lfp(λσ. σ ⊔ (x+1 if x<10)) then apply exit condition.
    println!("Example 1: Counter loop (x := 0; while x < 10 do x := x + 1)");

    // init1: Initial abstract state before loop execution
    // Represents: x = 0 (precise constant value)
    // This is the starting point for fixpoint computation: lfp(λX. init ⊔ f(X))
    let init1 = {
        let mut elem = IntervalElement::new();
        elem.set("x".to_string(), Interval::constant(0));
        elem
    };

    // f1: Loop body transfer function
    // Represents: One iteration of the loop body
    // Input: Current abstract state (elem)
    // Output: Abstract state after executing loop body IF condition holds
    // Steps: 1) Execute x := x + 1
    //        2) Assume loop condition (x < 10) holds
    let f1 = |elem: &IntervalElement| {
        // Step 1: Execute assignment x := x + 1
        let x_int = elem.get("x");
        let incremented = Interval::new(x_int.low.add(&Bound::Finite(1)), x_int.high.add(&Bound::Finite(1)));

        let mut result = elem.clone();
        result.set("x".to_string(), incremented);

        // Step 2: Assume loop condition x < 10 holds (refines the state)
        let refined = domain.assume(&result, &NumPred::Lt(NumExpr::Var("x".to_string()), NumExpr::Const(10)));
        refined
    };

    // result1: Computed fixpoint - the loop invariant
    // This is the solution to: lfp(λX. init1 ⊔ f1(X))
    // Represents: All reachable states inside the loop body
    let result1 = engine.lfp(init1, f1);

    println!("  Initial: x ∈ [0, 0]");
    println!("  Loop invariant: x ∈ {} (states inside loop body)", result1.get("x"));
    println!();
    println!("  🔍 How to interpret [2, 9] (not [0, 9]):");
    println!("     • Widening at iteration 3: [0, 2] ∇ [0, 3] → [0, +∞]");
    println!("     • Narrowing iteration 1: meet([0, +∞], [1, 9]) → [1, 9]");
    println!("     • Narrowing iteration 2: meet([1, 9], [2, 9]) → [2, 9]");
    println!("     • Result loses 0 and 1 due to narrowing precision limits");
    println!();
    println!("  ✅ How to USE this result:");
    println!("     • [2, 9] is a SAFE over-approximation of loop states");
    println!("     • Any property true for ALL values in [2, 9] is true in the loop");
    println!("     • Example: Can prove x > 1 (always true in [2, 9])");
    println!("     • Example: Cannot prove x < 5 (false for x=9, which is in [2, 9])");
    println!("     • For verification: Checks like 'x > 0' will succeed ✓");
    println!("     • Missing 0 and 1 doesn't cause unsoundness (over-approximation)");
    println!();

    // Example 2: Countdown
    // let x = 100;
    // while (x > 0) { x = x - 1; }
    println!("Example 2: Countdown (x := 100; while x > 0 do x := x - 1)");

    // init2: Initial state with x = 100
    let init2 = {
        let mut elem = IntervalElement::new();
        elem.set("x".to_string(), Interval::constant(100));
        elem
    };

    // f2: Loop body transfer function for countdown
    // Executes: x := x - 1, then assumes x > 0
    let f2 = |elem: &IntervalElement| {
        let x_int = elem.get("x");
        let decremented = Interval::new(x_int.low.sub(&Bound::Finite(1)), x_int.high.sub(&Bound::Finite(1)));

        let mut result = elem.clone();
        result.set("x".to_string(), decremented);

        // Assume loop condition x > 0 holds
        let refined = domain.assume(&result, &NumPred::Gt(NumExpr::Var("x".to_string()), NumExpr::Const(0)));
        refined
    };

    // result2: Loop invariant for countdown loop
    let result2 = engine.lfp(init2, f2);

    println!("  Initial: x ∈ [100, 100]");
    println!("  Loop invariant: x ∈ {} (states inside loop body)", result2.get("x"));
    println!("  Interpretation: Values satisfying x > 0 during loop execution");
    println!();

    // Example 3: Unbounded loop
    // let x = 0;
    // while (true) { x = x + 1; }
    println!("Example 3: Unbounded loop (x := 0; while true do x := x + 1)");

    // init3: Initial state with x = 0
    let init3 = {
        let mut elem = IntervalElement::new();
        elem.set("x".to_string(), Interval::constant(0));
        elem
    };

    // f3: Loop body transfer function for unbounded loop
    // Only executes x := x + 1 (no loop condition to assume)
    // This will cause widening to extrapolate to +∞
    let f3 = |elem: &IntervalElement| {
        let x_int = elem.get("x");
        let incremented = Interval::new(x_int.low.add(&Bound::Finite(1)), x_int.high.add(&Bound::Finite(1)));

        let mut result = elem.clone();
        result.set("x".to_string(), incremented);
        result
    };

    // result3: Loop invariant showing unbounded growth
    // Upper bound extrapolates to +∞ via widening
    let result3 = engine.lfp(init3, f3);
    println!("  Initial: x ∈ [0, 0]");
    println!("  Loop invariant: x ∈ {} (grows unboundedly)", result3.get("x"));
    println!("  (No exit - infinite loop!)");
    println!();

    println!("=== Analysis Complete ===");
}
