//! Example programs for testing abstract interpretation
//!
//! Small programs demonstrating various patterns and interesting analyses

use sdd_abstract_interpretation::*;

fn main() {
    println!("🔬 Test Program Gallery\n");

    test_simple_loop();
    test_mutual_increment();
    test_branching_merge();
    test_assertion_chain();
}

fn test_simple_loop() {
    println!("📝 Test 1: Bounded Counter");
    println!("━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━");

    let program = vec![
        Stmt::Assign(Var::new(1), Expr::Const(0)), // x := 0
        Stmt::Assign(
            Var::new(1),
            Expr::Add(
                // x := x + 1
                Box::new(Expr::Var(Var::new(1))),
                Box::new(Expr::Const(1)),
            ),
        ),
        Stmt::Assign(
            Var::new(1),
            Expr::Add(
                // x := x + 1 (again)
                Box::new(Expr::Var(Var::new(1))),
                Box::new(Expr::Const(1)),
            ),
        ),
        Stmt::Assert(Predicate::Le(
            // assert x <= 7
            Expr::Var(Var::new(1)),
            Expr::Const(7),
        )),
    ];

    analyze_with_all_strategies(&program);
}

fn test_mutual_increment() {
    println!("\n📝 Test 2: Two-Variable Interaction");
    println!("━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━");

    let program = vec![
        Stmt::Assign(Var::new(1), Expr::Const(0)), // x := 0
        Stmt::Assign(Var::new(2), Expr::Const(0)), // y := 0
        Stmt::Assign(
            Var::new(1),
            Expr::Add(
                // x := x + 1
                Box::new(Expr::Var(Var::new(1))),
                Box::new(Expr::Const(1)),
            ),
        ),
        Stmt::Assign(
            Var::new(2),
            Expr::Add(
                // y := x + y
                Box::new(Expr::Var(Var::new(1))),
                Box::new(Expr::Var(Var::new(2))),
            ),
        ),
        Stmt::Assert(Predicate::Lt(
            // assert x < y
            Expr::Var(Var::new(1)),
            Expr::Var(Var::new(2)),
        )),
    ];

    analyze_with_all_strategies(&program);
}

fn test_branching_merge() {
    println!("\n📝 Test 3: Conditional with Multiple Branches");
    println!("━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━");

    let program = vec![
        Stmt::Assign(Var::new(1), Expr::Const(3)), // x := 3
        Stmt::Assign(Var::new(2), Expr::Const(2)), // y := 2
        Stmt::If(
            Predicate::Lt(Expr::Var(Var::new(1)), Expr::Var(Var::new(2))),
            vec![
                Stmt::Assign(Var::new(1), Expr::Const(0)), // x := 0
            ],
            vec![
                Stmt::Assign(Var::new(2), Expr::Const(5)), // y := 5
            ],
        ),
        Stmt::Assert(Predicate::Or(
            Box::new(Predicate::Eq(Expr::Var(Var::new(1)), Expr::Const(0))),
            Box::new(Predicate::Eq(Expr::Var(Var::new(2)), Expr::Const(5))),
        )),
    ];

    analyze_with_all_strategies(&program);
}

fn test_assertion_chain() {
    println!("\n📝 Test 4: Sequential Assertions");
    println!("━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━");

    let program = vec![
        Stmt::Assign(Var::new(1), Expr::Const(2)), // x := 2
        Stmt::Assert(Predicate::Eq(
            // assert x == 2
            Expr::Var(Var::new(1)),
            Expr::Const(2),
        )),
        Stmt::Assign(
            Var::new(1),
            Expr::Add(
                // x := x + 3
                Box::new(Expr::Var(Var::new(1))),
                Box::new(Expr::Const(3)),
            ),
        ),
        Stmt::Assert(Predicate::Eq(
            // assert x == 5
            Expr::Var(Var::new(1)),
            Expr::Const(5),
        )),
    ];

    analyze_with_all_strategies(&program);
}

fn analyze_with_all_strategies(program: &Program) {
    let vars = program_vars(program);
    println!(
        "Variables: {}",
        vars.iter().map(|v| format!("{}", v)).collect::<Vec<_>>().join(", ")
    );
    println!("Program size: {} statements\n", program.len());

    let strategies = vec![VtreeStrategy::Balanced, VtreeStrategy::RightLinear, VtreeStrategy::LeftLinear];

    for strategy in strategies {
        let mut interpreter = SddAbstractInterpreter::new(program, strategy);
        let result = interpreter.analyze();
        result.print_report();
    }
}
