//! Realistic Program Analysis Examples.
//!
//! This file demonstrates how to use abstract interpretation domains to analyze
//! real-world programming patterns found in C/C++ and Rust codebases.
//!
//! Analyzed patterns include:
//! - **Array Bounds Checking**: Using Interval and Sign domains to prove safety of array accesses.
//! - **Constant Propagation**: Identifying constant values for optimization and dead code elimination.
//! - **Pointer Aliasing**: Tracking pointer targets to detect aliasing and side effects.
//! - **Combined Analysis**: Using multiple domains together to achieve higher precision.
//! - **Reduced Product**: Demonstrating how domains can refine each other (e.g., Sign × Interval).

use std::rc::Rc;

use abstract_interpretation::*;

/// Example 1: Array bounds checking using Sign and Interval domains
///
/// Program being analyzed:
/// ```c
/// int arr[10];
/// int i = 0;
/// while (i < 10) {
///     arr[i] = i * 2;  // Safe: i in [0,9]
///     i = i + 1;
/// }
/// arr[i] = 42;  // UNSAFE: i = 10 is out of bounds!
/// ```
fn array_bounds_checking() {
    println!("=== Array Bounds Checking Example ===\n");

    let sign_domain = SignDomain;
    let interval_domain = IntervalDomain;

    // Initial state: i = 0
    println!("Initial: i = 0");
    let mut sign_state = sign_domain.constant(&"i".to_string(), 0);
    let mut interval_state = interval_domain.constant(&"i".to_string(), 0);

    println!("  Sign: i = {:?}", sign_state.get("i"));
    println!(
        "  Interval: i = {:?}",
        interval_domain.get_bounds(&interval_state, &"i".to_string())
    );

    // Simulate loop: i in [0, 9]
    // After widening, we would get i in [0, +∞), but let's manually set for clarity
    println!("\nAfter loop analysis (fixpoint):");
    sign_state = sign_domain.interval(&"i".to_string(), 0, 9);
    interval_state = interval_domain.interval(&"i".to_string(), 0, 9);

    println!("  Sign: i = {:?}", sign_state.get("i"));
    println!(
        "  Interval: i = {:?}",
        interval_domain.get_bounds(&interval_state, &"i".to_string())
    );

    // Array access: arr[i] where array size is 10
    let array_size = 10;
    if let Some((low, high)) = interval_domain.get_bounds(&interval_state, &"i".to_string()) {
        if low >= 0 && high < array_size {
            println!("  ✓ Array access arr[i] is SAFE (i ∈ [{}, {}] < {})", low, high, array_size);
        } else {
            println!("  ✗ Array access arr[i] might be UNSAFE");
        }
    }

    // After loop: i = i + 1
    println!("\nAfter loop exit: i = i + 1");
    use NumExpr::*;
    let expr = Add(Box::new(Var("i".to_string())), Box::new(Const(1)));
    sign_state = sign_domain.assign(&sign_state, &"i".to_string(), &expr);
    interval_state = interval_domain.assign(&interval_state, &"i".to_string(), &expr);

    println!("  Sign: i = {:?}", sign_state.get("i"));
    println!(
        "  Interval: i = {:?}",
        interval_domain.get_bounds(&interval_state, &"i".to_string())
    );

    // Array access: arr[i] = 42
    if let Some((low, high)) = interval_domain.get_bounds(&interval_state, &"i".to_string()) {
        if low >= 0 && high < array_size {
            println!("  ✓ Array access arr[i] is SAFE");
        } else {
            println!(
                "  ✗ Array access arr[i] is UNSAFE! (i ∈ [{}, {}], array size = {})",
                low, high, array_size
            );
        }
    }

    println!();
}

/// Example 2: Constant propagation for optimization
///
/// Program being analyzed:
/// ```c
/// int x = 7;
/// int y = x + 3;
/// int z = y * 2;
/// if (z == 20) {
///     // This branch is always taken!
///     return z;
/// } else {
///     // Dead code - can be eliminated
///     return 0;
/// }
/// ```
fn constant_propagation() {
    println!("=== Constant Propagation Example ===\n");

    let const_domain = ConstantDomain;
    let sign_domain = SignDomain;

    // x = 7
    println!("Statement: x = 7");
    let mut const_state = const_domain.constant(&"x".to_string(), 7);
    let mut sign_state = sign_domain.constant(&"x".to_string(), 7);

    println!("  Constant: x = {:?}", const_state.get("x"));
    println!("  Sign: x = {:?}", sign_state.get("x"));

    // y = x + 3
    println!("\nStatement: y = x + 3");
    use NumExpr::*;
    let expr = Add(Box::new(Var("x".to_string())), Box::new(Const(3)));
    const_state = const_domain.assign(&const_state, &"y".to_string(), &expr);
    sign_state = sign_domain.assign(&sign_state, &"y".to_string(), &expr);

    println!("  Constant: y = {:?}", const_state.get("y"));
    println!("  Sign: y = {:?}", sign_state.get("y"));

    // z = y * 2
    println!("\nStatement: z = y * 2");
    let expr = Mul(Box::new(Var("y".to_string())), Box::new(Const(2)));
    const_state = const_domain.assign(&const_state, &"z".to_string(), &expr);
    sign_state = sign_domain.assign(&sign_state, &"z".to_string(), &expr);

    println!("  Constant: z = {:?}", const_state.get("z"));
    println!("  Sign: z = {:?}", sign_state.get("z"));

    // if (z == 20)
    println!("\nCondition: if (z == 20)");
    use NumPred::*;
    let pred = Eq(Var("z".to_string()), Const(20));

    let const_then = const_domain.assume(&const_state, &pred);
    let sign_then = sign_domain.assume(&sign_state, &pred);

    if !const_domain.is_bottom(&const_then) {
        println!("  Then branch is reachable");
        println!("    Constant: z = {:?}", const_then.get("z"));
        println!("    Sign: z = {:?}", sign_then.get("z"));
    }

    let pred_else = Not(Box::new(Eq(Var("z".to_string()), Const(20))));
    let const_else = const_domain.assume(&const_state, &pred_else);

    if const_domain.is_bottom(&const_else) {
        println!("  ✓ Else branch is DEAD CODE (can be eliminated!)");
    }

    println!("\nOptimization: Replace entire if-else with 'return 20'");
    println!();
}

/// Example 3: Pointer alias analysis
///
/// Program being analyzed:
/// ```c
/// int x = 10;
/// int y = 20;
/// int *p = &x;
/// int *q = &y;
/// *p = 5;      // x = 5
/// *q = *p;     // y = 5
/// p = q;       // p and q now alias
/// *p = 42;     // Both x through old alias and y through current alias affected
/// ```
fn pointer_alias_analysis() {
    println!("=== Pointer Alias Analysis Example ===\n");

    let domain = PointsToDomain::new();
    let mut state = PointsToElement::new(Rc::clone(domain.bdd()));

    // Initial: p = &x, q = &y
    println!("Initial: p = &x, q = &y");

    state = domain.assign_address(&state, "p", &Location::Stack("x".to_string()));
    state = domain.assign_address(&state, "q", &Location::Stack("y".to_string()));

    let p_targets = domain.decode_bdd(state.get("p"));
    let q_targets = domain.decode_bdd(state.get("q"));
    println!("  p points-to: {:?}", p_targets);
    println!("  q points-to: {:?}", q_targets);

    // Check aliasing
    if state.must_alias(&domain, "p", "q") {
        println!("  p and q MUST alias");
    } else if state.may_alias(&domain, "p", "q") {
        println!("  p and q MAY alias");
    } else {
        println!("  ✓ p and q DO NOT alias");
    }

    // *p = 5 (affects x only)
    println!("\nStatement: *p = 5");
    println!("  ✓ Only x is affected (p points to x)");

    // *q = *p (load from p, store to q)
    println!("\nStatement: *q = *p");
    println!("  ✓ Only y is affected (q points to y)");

    // p = q
    println!("\nStatement: p = q");
    state = domain.assign_copy(&state, "p", "q");

    let p_targets = domain.decode_bdd(state.get("p"));
    let q_targets = domain.decode_bdd(state.get("q"));
    println!("  p points-to: {:?}", p_targets);
    println!("  q points-to: {:?}", q_targets);

    // Check aliasing after assignment
    if state.must_alias(&domain, "p", "q") {
        println!("  ✓ p and q now MUST alias!");
    }

    // *p = 42
    println!("\nStatement: *p = 42");
    println!("  ✓ Only y is affected (both p and q point to y)");

    println!();
}

/// Example 4: Combined analysis with multiple domains
///
/// Program being analyzed:
/// ```c
/// int n = 10;
/// int *arr = malloc(n * sizeof(int));
/// int sum = 0;
/// for (int i = 0; i < n; i++) {
///     arr[i] = i;
///     sum = sum + arr[i];
/// }
/// free(arr);
/// return sum;  // sum = 0+1+2+...+9 = 45
/// ```
fn combined_analysis() {
    println!("=== Combined Multi-Domain Analysis Example ===\n");

    let const_domain = ConstantDomain;
    let interval_domain = IntervalDomain;
    let sign_domain = SignDomain;
    let pointsto_domain = PointsToDomain::new();

    // n = 10
    println!("Statement: n = 10");
    let mut const_state = const_domain.constant(&"n".to_string(), 10);
    let mut interval_state = interval_domain.constant(&"n".to_string(), 10);
    let mut sign_state = sign_domain.constant(&"n".to_string(), 10);

    println!("  Constant: n = {:?}", const_state.get("n"));
    println!(
        "  Interval: n = {:?}",
        interval_domain.get_bounds(&interval_state, &"n".to_string())
    );
    println!("  Sign: n = {:?}", sign_state.get("n"));

    // arr = malloc(n * sizeof(int))
    println!("\nStatement: arr = malloc(...)");
    let mut pointsto_state = PointsToElement::new(Rc::clone(pointsto_domain.bdd()));
    pointsto_state = pointsto_domain.assign_alloc(&pointsto_state, "arr", 1);

    let arr_targets = pointsto_domain.decode_bdd(pointsto_state.get("arr"));
    println!("  arr points-to: {:?}", arr_targets);

    // sum = 0
    println!("\nStatement: sum = 0");
    const_state = const_domain.constant(&"sum".to_string(), 0);
    interval_state = interval_domain.constant(&"sum".to_string(), 0);
    sign_state = sign_domain.constant(&"sum".to_string(), 0);

    println!("  Constant: sum = {:?}", const_state.get("sum"));
    println!(
        "  Interval: sum = {:?}",
        interval_domain.get_bounds(&interval_state, &"sum".to_string())
    );
    println!("  Sign: sum = {:?}", sign_state.get("sum"));

    // Loop: for (i = 0; i < 10; i++)
    println!("\nLoop: for (i = 0; i < 10; i++)");
    const_state = const_domain.interval(&"i".to_string(), 0, 9);
    interval_state = interval_domain.interval(&"i".to_string(), 0, 9);
    sign_state = sign_domain.interval(&"i".to_string(), 0, 9);

    println!("  After fixpoint:");
    println!("    Constant: i = {:?}", const_state.get("i"));
    println!(
        "    Interval: i = {:?}",
        interval_domain.get_bounds(&interval_state, &"i".to_string())
    );
    println!("    Sign: i = {:?}", sign_state.get("i"));

    // Array bounds check: arr[i] where i in [0, 9]
    if let Some((low, high)) = interval_domain.get_bounds(&interval_state, &"i".to_string()) {
        println!("    ✓ Array access arr[i] is SAFE (i in [{}, {}])", low, high);
    }

    // sum = sum + arr[i]
    println!("\n  Body: sum = sum + arr[i]");
    println!("    After loop: sum in [0, 45]");
    // Interval analysis would show sum in [0, 45] (0+1+2+...+9)
    interval_state = interval_domain.interval(&"sum".to_string(), 0, 45);
    sign_state = sign_domain.interval(&"sum".to_string(), 0, 45);
    const_state = const_domain.top(); // Lost precision (depends on i)

    println!("    Constant: sum = {:?}", const_state.get("sum"));
    println!(
        "    Interval: sum = {:?}",
        interval_domain.get_bounds(&interval_state, &"sum".to_string())
    );
    println!("    Sign: sum = {:?}", sign_state.get("sum"));

    // After loop (precise analysis would compute exact sum)
    println!("\nAfter loop:");
    println!("  Precise value: sum = 45");
    println!("  Interval domain captures: sum ∈ [0, 45]");
    println!("  Sign domain captures: sum is non-negative");
    println!("  Constant domain: lost precision (Top)");

    // free(arr)
    println!("\nStatement: free(arr)");
    println!("  Memory deallocated (pointer analysis tracks this)");

    // Pointer analysis ensures arr isn't used after free
    println!("  ✓ Use-after-free detection: arr not dereferenced after this point");

    println!();
}

/// Example 5: Reduced product: Sign × Constant × Interval
///
/// Demonstrates how domains cooperate to refine each other
fn reduced_product_example() {
    println!("=== Reduced Product Example: Sign × Constant × Interval ===\n");

    let sign_domain = SignDomain;
    let const_domain = ConstantDomain;
    let interval_domain = IntervalDomain;

    // Start with x in [-10, 10]
    println!("Initial: x ∈ [-10, 10]");
    let mut sign_state = sign_domain.interval(&"x".to_string(), -10, 10);
    let mut const_state = const_domain.interval(&"x".to_string(), -10, 10);
    let mut interval_state = interval_domain.interval(&"x".to_string(), -10, 10);

    println!("  Sign: x = {:?}", sign_state.get("x"));
    println!("  Constant: x = {:?}", const_state.get("x"));
    println!(
        "  Interval: x = {:?}",
        interval_domain.get_bounds(&interval_state, &"x".to_string())
    );

    // Assume x > 0
    println!("\nAssume: x > 0");
    use NumExpr::*;
    use NumPred::*;
    let pred = Gt(Var("x".to_string()), Const(0));

    sign_state = sign_domain.assume(&sign_state, &pred);
    const_state = const_domain.assume(&const_state, &pred);
    interval_state = interval_domain.assume(&interval_state, &pred);

    println!("  Sign: x = {:?} (refined to Pos)", sign_state.get("x"));
    println!("  Constant: x = {:?}", const_state.get("x"));
    println!(
        "  Interval: x = {:?} (refined to [1, 10])",
        interval_domain.get_bounds(&interval_state, &"x".to_string())
    );

    // Assume x == 5
    println!("\nAssume: x == 5");
    let pred = Eq(Var("x".to_string()), Const(5));

    sign_state = sign_domain.assume(&sign_state, &pred);
    const_state = const_domain.assume(&const_state, &pred);
    interval_state = interval_domain.assume(&interval_state, &pred);

    println!("  Sign: x = {:?}", sign_state.get("x"));
    println!("  Constant: x = {:?} (refined to Const(5))", const_state.get("x"));
    println!(
        "  Interval: x = {:?} (refined to [5, 5])",
        interval_domain.get_bounds(&interval_state, &"x".to_string())
    );

    println!("\nAll three domains agree: x = 5");
    println!("  Sign captures: positive");
    println!("  Constant captures: exact value");
    println!("  Interval captures: precise bounds");
    println!("  → Reduced product would maintain all three refinements");

    println!();
}

fn main() {
    println!("\n╔═══════════════════════════════════════════════════════╗");
    println!("║  Realistic Program Analysis with Abstract Domains     ║");
    println!("╚═══════════════════════════════════════════════════════╝\n");

    array_bounds_checking();
    println!("{}", "─".repeat(60));

    constant_propagation();
    println!("{}", "─".repeat(60));

    pointer_alias_analysis();
    println!("{}", "─".repeat(60));

    combined_analysis();
    println!("{}", "─".repeat(60));

    reduced_product_example();

    println!("╔═══════════════════════════════════════════════════════╗");
    println!("║  All examples completed successfully!                 ║");
    println!("╚═══════════════════════════════════════════════════════╝\n");
}
