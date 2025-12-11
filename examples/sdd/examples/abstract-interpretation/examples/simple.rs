//! Simple example demonstrating SDD-based abstract interpretation
//!
//! This example shows how to:
//! 1. Define a small program in the mini-language
//! 2. Create an abstract interpreter
//! 3. Analyze the program with different VTree strategies
//! 4. Compare results

use sdd_abstract_interpretation::*;

fn main() {
    println!("🎯 SDD Abstract Interpretation Example\n");

    // Example 1: Simple assignment and assertion
    println!("📝 Example 1: Simple counter increment");
    println!("━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━");

    // Program:
    //   x := 0
    //   x := x + 1
    //   assert x < 7
    let program1 = vec![
        Stmt::Assign(Var::new(1), Expr::Const(0)), // x := 0
        Stmt::Assign(
            Var::new(1),
            Expr::Add(
                // x := x + 1
                Box::new(Expr::Var(Var::new(1))),
                Box::new(Expr::Const(1)),
            ),
        ),
        Stmt::Assert(Predicate::Lt(
            // assert x < 7
            Expr::Var(Var::new(1)),
            Expr::Const(7),
        )),
    ];

    analyze_program(&program1);

    // Example 2: Conditional with both branches
    println!("\n📝 Example 2: Conditional branching");
    println!("━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━");

    let program2 = vec![
        Stmt::Assign(Var::new(1), Expr::Const(0)), // x := 0
        Stmt::Assign(Var::new(2), Expr::Const(5)), // y := 5
        Stmt::If(
            Predicate::Lt(Expr::Var(Var::new(1)), Expr::Var(Var::new(2))),
            vec![
                Stmt::Assign(Var::new(1), Expr::Const(1)), // x := 1
            ],
            vec![
                Stmt::Assign(Var::new(1), Expr::Const(0)), // x := 0
            ],
        ),
        Stmt::Assert(Predicate::Le(
            // assert x <= 1
            Expr::Var(Var::new(1)),
            Expr::Const(1),
        )),
    ];

    analyze_program(&program2);
}

fn analyze_program(program: &Program) {
    // Get program statistics
    let vars = program_vars(program);
    println!(
        "Variables: {}",
        vars.iter().map(|v| format!("{}", v)).collect::<Vec<_>>().join(", ")
    );
    println!("Statements: {}", program.len());

    // Analyze with different VTree strategies
    let strategies = vec![VtreeStrategy::Balanced, VtreeStrategy::RightLinear, VtreeStrategy::LeftLinear];

    println!("\nAnalysis Results by VTree Strategy:");
    println!("────────────────────────────────────");

    for strategy in strategies {
        println!("\n{}: {}", strategy, strategy.description());
        let mut interpreter = SddAbstractInterpreter::new(program, strategy);
        let result = interpreter.analyze();
        result.print_report();
    }
}
