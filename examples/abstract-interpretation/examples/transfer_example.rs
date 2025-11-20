//! Transfer Function Analysis Example.
//!
//! This example demonstrates statement-by-statement abstract interpretation using
//! **Transfer Functions**.
//!
//! A transfer function `f` maps an abstract state `σ` before a statement to a new
//! abstract state `σ'` after the statement: `σ' = f(σ)`.
//!
//! Key concepts demonstrated:
//! - **Assignments**: Updating the abstract state with new values.
//! - **Conditionals**: Splitting the state (filtering) and joining paths.
//! - **Sequencing**: Chaining transfer functions.
//! - **Refinement**: Using `assume` and `assert` to narrow down possible values.

use abstract_interpretation::*;
use simplelog::*;

fn main() {
    // Initialize logging
    TermLogger::init(LevelFilter::Info, Config::default(), TerminalMode::Mixed, ColorChoice::Auto).unwrap();

    println!("=== Transfer Function Analysis ===\n");

    // domain: The abstract domain used for analysis (interval domain)
    // Provides lattice operations (⊔, ⊓, ∇, ∆) and numeric operations
    let domain = IntervalDomain;

    // transfer: Transfer function for applying abstract semantics to statements
    // Implements: ⟦stmt⟧♯: Element → Element
    let transfer = NumericTransferFunction;

    // Example 1: Sequential assignments
    println!("Example 1: Sequential assignments");
    println!("  let x = 5;");
    println!("  let y = x + 10;");
    println!("  let z = y * 2;\n");

    // init: Initial abstract state (empty - no variables defined yet)
    let init = IntervalElement::new();

    // prog1: Abstract syntax tree representing the program
    // Structure: Seq(x:=5, Seq(y:=x+10, z:=y*2))
    // Represents three sequential assignments in a nested structure
    let prog1 = Stmt::Seq(
        Box::new(Stmt::Assign("x".to_string(), NumExpr::Const(5))),
        Box::new(Stmt::Seq(
            Box::new(Stmt::Assign(
                "y".to_string(),
                NumExpr::Add(Box::new(NumExpr::Var("x".to_string())), Box::new(NumExpr::Const(10))),
            )),
            Box::new(Stmt::Assign(
                "z".to_string(),
                NumExpr::Mul(Box::new(NumExpr::Var("y".to_string())), Box::new(NumExpr::Const(2))),
            )),
        )),
    );

    // result1: Abstract state after applying transfer function
    // Computed via: ⟦prog1⟧♯(init) = abstract execution of the program
    let result1 = transfer.apply(&domain, &init, &prog1);
    println!("  Result:");
    println!("    x ∈ {}", result1.get("x"));
    println!("    y ∈ {}", result1.get("y"));
    println!("    z ∈ {}", result1.get("z"));
    println!();
    println!("  ✅ Interpretation:");
    println!("     • All values are PRECISE constants (singleton intervals)");
    println!("     • x=5 → y=5+10=15 → z=15*2=30");
    println!("     • Transfer functions propagate concrete values exactly");
    println!("     • No loss of precision for deterministic computations");
    println!();

    // Example 2: Conditional
    println!("Example 2: Conditional branch");
    println!("  let x = input (-10..10);");
    println!("  if (x >= 0) {{");
    println!("    y = x + 10;");
    println!("  }} else {{");
    println!("    y = -x;");
    println!("  }}\n");

    // init2: Initial state with x ∈ [-10, 10] (simulating input range)
    let init2 = {
        let mut elem = IntervalElement::new();
        elem.set("x".to_string(), Interval::new(Bound::Finite(-10), Bound::Finite(10)));
        elem
    };

    // prog2: Conditional statement (if-then-else)
    // Structure: If(x >= 0, y := x+10, y := -x)
    // Transfer function will:
    //   1. Split state by condition (x >= 0 vs x < 0)
    //   2. Apply assignments to each branch
    //   3. Join (⊔) results from both branches
    let prog2 = Stmt::If(
        NumPred::Ge(NumExpr::Var("x".to_string()), NumExpr::Const(0)),
        Box::new(Stmt::Assign(
            "y".to_string(),
            NumExpr::Add(Box::new(NumExpr::Var("x".to_string())), Box::new(NumExpr::Const(10))),
        )),
        Box::new(Stmt::Assign("y".to_string(), NumExpr::Neg(Box::new(NumExpr::Var("x".to_string()))))),
    );

    // result2: Abstract state after conditional
    // Contains join of both branches: then_result ⊔ else_result
    let result2 = transfer.apply(&domain, &init2, &prog2);
    println!("  Result:");
    println!("    x ∈ {}", result2.get("x"));
    println!("    y ∈ {}", result2.get("y"));
    println!();
    println!("  ✅ Interpretation:");
    println!("     • x unchanged: [-10, 10] (not modified by the conditional)");
    println!("     • y ∈ [1, 20]: Join of both branches");
    println!("       - THEN branch (x ≥ 0): x ∈ [0,10] → y = x+10 ∈ [10,20]");
    println!("       - ELSE branch (x < 0): x ∈ [-10,-1] → y = -x ∈ [1,10]");
    println!("       - Join: [10,20] ⊔ [1,10] = [1,20] ✓");
    println!("     • Note: Lower bound is 1 not 0 (negation of [-10,-1] starts at 1)");
    println!();

    // Example 3: Nested conditionals
    println!("Example 3: Nested conditionals");
    println!("  let x = input (0..100);");
    println!("  if (x < 50) {{");
    println!("    if (x < 25) {{");
    println!("      y = 0;");
    println!("    }} else {{");
    println!("      y = 1;");
    println!("    }}");
    println!("  }} else {{");
    println!("    y = 2;");
    println!("  }}\n");

    // init3: Initial state with x ∈ [0, 100]
    let init3 = {
        let mut elem = IntervalElement::new();
        elem.set("x".to_string(), Interval::new(Bound::Finite(0), Bound::Finite(100)));
        elem
    };

    // prog3: Nested conditional (if inside if)
    // Structure: If(x<50, If(x<25, y:=0, y:=1), y:=2)
    // Creates THREE execution paths that will be joined
    let prog3 = Stmt::If(
        NumPred::Lt(NumExpr::Var("x".to_string()), NumExpr::Const(50)),
        Box::new(Stmt::If(
            NumPred::Lt(NumExpr::Var("x".to_string()), NumExpr::Const(25)),
            Box::new(Stmt::Assign("y".to_string(), NumExpr::Const(0))),
            Box::new(Stmt::Assign("y".to_string(), NumExpr::Const(1))),
        )),
        Box::new(Stmt::Assign("y".to_string(), NumExpr::Const(2))),
    );

    // result3: Abstract state after nested conditional
    // Join of three paths: {0} ⊔ {1} ⊔ {2} = [0, 2]
    let result3 = transfer.apply(&domain, &init3, &prog3);
    println!("  Result:");
    println!("    x ∈ {}", result3.get("x"));
    println!("    y ∈ {}", result3.get("y"));
    println!();
    println!("  ✅ Interpretation:");
    println!("     • x unchanged: [0, 100]");
    println!("     • y ∈ [0, 2]: Join of THREE branches");
    println!("       - x < 25: y = 0");
    println!("       - 25 ≤ x < 50: y = 1");
    println!("       - x ≥ 50: y = 2");
    println!("       - Join: {{0}} ⊔ {{1}} ⊔ {{2}} = [0, 2] ✓");
    println!("     • Precise result captures all three possible outcomes");
    println!();

    // Example 4: Assert and assume
    println!("Example 4: Assertions and assumptions");
    println!("  let x = input (0..100);");
    println!("  assume(x >= 10);");
    println!("  assert(x <= 50);  // refines to [10, 50]\n");

    // init4: Initial state with x ∈ [0, 100]
    let init4 = {
        let mut elem = IntervalElement::new();
        elem.set("x".to_string(), Interval::new(Bound::Finite(0), Bound::Finite(100)));
        elem
    };

    // prog4: Sequence of assume and assert statements
    // Structure: Seq(assume(x>=10), assert(x<=50))
    // Both assume and assert use domain refinement (meet ⊓)
    let prog4 = Stmt::Seq(
        Box::new(Stmt::Assume(NumPred::Ge(NumExpr::Var("x".to_string()), NumExpr::Const(10)))),
        Box::new(Stmt::Assert(NumPred::Le(NumExpr::Var("x".to_string()), NumExpr::Const(50)))),
    );

    // result4: Abstract state after refinement
    // Sequential refinement: [0,100] ⊓ [10,∞] ⊓ [-∞,50] = [10,50]
    let result4 = transfer.apply(&domain, &init4, &prog4);
    println!("  Result:");
    println!("    x ∈ {}", result4.get("x"));
    println!();
    println!("  ✅ Interpretation:");
    println!("     • Initial: x ∈ [0, 100] (input range)");
    println!("     • After assume(x ≥ 10): x ∈ [10, 100] (refined by assumption)");
    println!("     • After assert(x ≤ 50): x ∈ [10, 50] (further refined)");
    println!("     • Both assume and assert REFINE the abstract state");
    println!("     • In abstract interpretation: assume = assert (both use meet)");
    println!("     • This demonstrates how contracts narrow the state space");
    println!();

    println!("=== Analysis Complete ===");
    println!();
    println!("📊 Key Takeaways:");
    println!("   1. Sequential code: Precise propagation of values");
    println!("   2. Conditionals: Join (⊔) merges branches, may lose precision");
    println!("   3. Nested branches: Multiple paths merged into single interval");
    println!("   4. Assumptions/assertions: Refine state via meet (⊓)");
    println!();
    println!("💡 Using these results:");
    println!("   • Results are SOUND over-approximations");
    println!("   • Can verify properties true for ALL values in intervals");
    println!("   • Cannot prove properties false for SOME values in intervals");
    println!("   • Precision loss at joins is inherent to interval domain");
}
