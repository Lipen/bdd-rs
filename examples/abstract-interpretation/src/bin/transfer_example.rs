//! Transfer function analysis example.
//!
//! Demonstrates statement-by-statement analysis using transfer functions.

use abstract_interpretation::*;
use simplelog::*;

fn main() {
    // Initialize logging
    TermLogger::init(LevelFilter::Info, Config::default(), TerminalMode::Mixed, ColorChoice::Auto).unwrap();

    println!("=== Transfer Function Analysis ===\n");

    let domain = IntervalDomain;
    let transfer = NumericTransferFunction;

    // Example 1: Sequential assignments
    println!("Example 1: Sequential assignments");
    println!("  let x = 5;");
    println!("  let y = x + 10;");
    println!("  let z = y * 2;\n");

    let init = IntervalElement::new();

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

    let result1 = transfer.apply(&domain, &init, &prog1);
    println!("  Result:");
    println!("    x ∈ {}", result1.get("x"));
    println!("    y ∈ {}", result1.get("y"));
    println!("    z ∈ {}\n", result1.get("z"));

    // Example 2: Conditional
    println!("Example 2: Conditional branch");
    println!("  let x = input (-10..10);");
    println!("  if (x >= 0) {{");
    println!("    y = x + 10;");
    println!("  }} else {{");
    println!("    y = -x;");
    println!("  }}\n");

    let init2 = {
        let mut elem = IntervalElement::new();
        elem.set("x".to_string(), Interval::new(Bound::Finite(-10), Bound::Finite(10)));
        elem
    };

    let prog2 = Stmt::If(
        NumPred::Ge(NumExpr::Var("x".to_string()), NumExpr::Const(0)),
        Box::new(Stmt::Assign(
            "y".to_string(),
            NumExpr::Add(Box::new(NumExpr::Var("x".to_string())), Box::new(NumExpr::Const(10))),
        )),
        Box::new(Stmt::Assign("y".to_string(), NumExpr::Neg(Box::new(NumExpr::Var("x".to_string()))))),
    );

    let result2 = transfer.apply(&domain, &init2, &prog2);
    println!("  Result:");
    println!("    x ∈ {}", result2.get("x"));
    println!("    y ∈ {}", result2.get("y"));
    println!("  (Expected: y ∈ [0, 20] - then branch [10,20], else branch [0,10])\n");

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

    let init3 = {
        let mut elem = IntervalElement::new();
        elem.set("x".to_string(), Interval::new(Bound::Finite(0), Bound::Finite(100)));
        elem
    };

    let prog3 = Stmt::If(
        NumPred::Lt(NumExpr::Var("x".to_string()), NumExpr::Const(50)),
        Box::new(Stmt::If(
            NumPred::Lt(NumExpr::Var("x".to_string()), NumExpr::Const(25)),
            Box::new(Stmt::Assign("y".to_string(), NumExpr::Const(0))),
            Box::new(Stmt::Assign("y".to_string(), NumExpr::Const(1))),
        )),
        Box::new(Stmt::Assign("y".to_string(), NumExpr::Const(2))),
    );

    let result3 = transfer.apply(&domain, &init3, &prog3);
    println!("  Result:");
    println!("    x ∈ {}", result3.get("x"));
    println!("    y ∈ {}", result3.get("y"));
    println!("  (Expected: y ∈ [0, 2])\n");

    // Example 4: Assert and assume
    println!("Example 4: Assertions and assumptions");
    println!("  let x = input (0..100);");
    println!("  assume(x >= 10);");
    println!("  assert(x <= 50);  // refines to [10, 50]\n");

    let init4 = {
        let mut elem = IntervalElement::new();
        elem.set("x".to_string(), Interval::new(Bound::Finite(0), Bound::Finite(100)));
        elem
    };

    let prog4 = Stmt::Seq(
        Box::new(Stmt::Assume(NumPred::Ge(NumExpr::Var("x".to_string()), NumExpr::Const(10)))),
        Box::new(Stmt::Assert(NumPred::Le(NumExpr::Var("x".to_string()), NumExpr::Const(50)))),
    );

    let result4 = transfer.apply(&domain, &init4, &prog4);
    println!("  Result:");
    println!("    x ∈ {}", result4.get("x"));
    println!("  (Expected: x ∈ [10, 50])\n");

    println!("=== Analysis Complete ===");
}
