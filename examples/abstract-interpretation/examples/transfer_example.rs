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

fn main() {
    println!("=== Transfer Function Analysis ===");

    let domain = IntervalDomain;
    let transfer = NumericTransferFunction;

    example_sequential_assignments(&domain, &transfer);
    example_conditional_branch(&domain, &transfer);
    example_nested_conditionals(&domain, &transfer);
    example_assertions_and_assumptions(&domain, &transfer);
}

/// Example 1: Sequential assignments
fn example_sequential_assignments(domain: &IntervalDomain, transfer: &NumericTransferFunction) {
    println!("Example 1: Sequential Assignments");
    println!("----------------------------------");

    println!("Program:");
    println!("  let x = 5;");
    println!("  let y = x + 10;");
    println!("  let z = y * 2;");
    println!();

    let init = IntervalElement::new();

    let prog = Stmt::Seq(
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

    let result = transfer.apply(domain, &init, &prog);

    println!("Result:");
    println!("  x ∈ {}", result.get("x"));
    println!("  y ∈ {}", result.get("y"));
    println!("  z ∈ {}", result.get("z"));
    println!();
    println!("✓ All values are precise constants (singleton intervals)");
    println!("  x=5 → y=5+10=15 → z=15*2=30");
    println!("  Transfer functions propagate concrete values exactly");

    assert_eq!(result.get("x"), Interval::constant(5));
    assert_eq!(result.get("y"), Interval::constant(15));
    assert_eq!(result.get("z"), Interval::constant(30));

    println!("\n");
}

/// Example 2: Conditional branch
fn example_conditional_branch(domain: &IntervalDomain, transfer: &NumericTransferFunction) {
    println!("Example 2: Conditional Branch");
    println!("------------------------------");

    println!("Program:");
    println!("  let x = input (-10..10);");
    println!("  if (x >= 0) {{");
    println!("    y = x + 10;");
    println!("  }} else {{");
    println!("    y = -x;");
    println!("  }}");
    println!();

    let init = {
        let mut elem = IntervalElement::new();
        elem.set("x".to_string(), Interval::new(Bound::Finite(-10), Bound::Finite(10)));
        elem
    };

    let prog = Stmt::If(
        NumPred::Ge(NumExpr::Var("x".to_string()), NumExpr::Const(0)),
        Box::new(Stmt::Assign(
            "y".to_string(),
            NumExpr::Add(Box::new(NumExpr::Var("x".to_string())), Box::new(NumExpr::Const(10))),
        )),
        Box::new(Stmt::Assign("y".to_string(), NumExpr::Neg(Box::new(NumExpr::Var("x".to_string()))))),
    );

    let result = transfer.apply(domain, &init, &prog);

    println!("Result:");
    println!("  x ∈ {}", result.get("x"));
    println!("  y ∈ {}", result.get("y"));
    println!();
    println!("✓ Conditional analysis complete:");
    println!("  THEN branch (x ≥ 0): x ∈ [0,10] → y = x+10 ∈ [10,20]");
    println!("  ELSE branch (x < 0): x ∈ [-10,-1] → y = -x ∈ [1,10]");
    println!("  Join: [10,20] ⊔ [1,10] = [1,20]");

    assert_eq!(result.get("y"), Interval::new(Bound::Finite(1), Bound::Finite(20)));

    println!("\n");
}

/// Example 3: Nested conditionals
fn example_nested_conditionals(domain: &IntervalDomain, transfer: &NumericTransferFunction) {
    println!("Example 3: Nested Conditionals");
    println!("-------------------------------");

    println!("Program:");
    println!("  let x = input (0..100);");
    println!("  if (x < 50) {{");
    println!("    if (x < 25) {{");
    println!("      y = 0;");
    println!("    }} else {{");
    println!("      y = 1;");
    println!("    }}");
    println!("  }} else {{");
    println!("    y = 2;");
    println!("  }}");
    println!();

    let init = {
        let mut elem = IntervalElement::new();
        elem.set("x".to_string(), Interval::new(Bound::Finite(0), Bound::Finite(100)));
        elem
    };

    let prog = Stmt::If(
        NumPred::Lt(NumExpr::Var("x".to_string()), NumExpr::Const(50)),
        Box::new(Stmt::If(
            NumPred::Lt(NumExpr::Var("x".to_string()), NumExpr::Const(25)),
            Box::new(Stmt::Assign("y".to_string(), NumExpr::Const(0))),
            Box::new(Stmt::Assign("y".to_string(), NumExpr::Const(1))),
        )),
        Box::new(Stmt::Assign("y".to_string(), NumExpr::Const(2))),
    );

    let result = transfer.apply(domain, &init, &prog);

    println!("Result:");
    println!("  x ∈ {}", result.get("x"));
    println!("  y ∈ {}", result.get("y"));
    println!();
    println!("✓ Nested conditional analysis:");
    println!("  x < 25: y = 0");
    println!("  25 ≤ x < 50: y = 1");
    println!("  x ≥ 50: y = 2");
    println!("  Join: {{0}} ⊔ {{1}} ⊔ {{2}} = [0, 2]");

    assert_eq!(result.get("y"), Interval::new(Bound::Finite(0), Bound::Finite(2)));

    println!("\n");
}

/// Example 4: Assertions and assumptions
fn example_assertions_and_assumptions(domain: &IntervalDomain, transfer: &NumericTransferFunction) {
    println!("Example 4: Assertions and Assumptions");
    println!("-------------------------------------");

    println!("Program:");
    println!("  let x = input (0..100);");
    println!("  assume(x >= 10);");
    println!("  assert(x <= 50);");
    println!();

    let init = {
        let mut elem = IntervalElement::new();
        elem.set("x".to_string(), Interval::new(Bound::Finite(0), Bound::Finite(100)));
        elem
    };

    let prog = Stmt::Seq(
        Box::new(Stmt::Assume(NumPred::Ge(NumExpr::Var("x".to_string()), NumExpr::Const(10)))),
        Box::new(Stmt::Assert(NumPred::Le(NumExpr::Var("x".to_string()), NumExpr::Const(50)))),
    );

    let result = transfer.apply(domain, &init, &prog);

    println!("Result:");
    println!("  x ∈ {}", result.get("x"));
    println!();
    println!("✓ State refinement through constraints:");
    println!("  Initial: x ∈ [0, 100]");
    println!("  After assume(x ≥ 10): x ∈ [10, 100]");
    println!("  After assert(x ≤ 50): x ∈ [10, 50]");
    println!("  Both assume and assert refine the abstract state via meet (⊓)");

    assert_eq!(result.get("x"), Interval::new(Bound::Finite(10), Bound::Finite(50)));
}
