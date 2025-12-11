//! VTree strategy comparison
//!
//! Shows how different vtree structures affect SDD size and analysis efficiency

use sdd_abstract_interpretation::*;

fn main() {
    println!("🌳 VTree Strategy Comparison\n");
    println!("This example demonstrates how different VTree structures");
    println!("affect SDD-based abstract interpretation.\n");

    // Create a program with interesting variable interactions
    let program = create_test_program();

    println!("📋 Program Structure:");
    println!("  - Variables: x, y, z (3 variables = 9 SDD variables)");
    println!("  - Statements: 6");
    println!("  - Predicates: Mix of individual and combined conditions\n");

    // Analyze with each strategy
    let strategies = vec![
        VtreeStrategy::Balanced,
        VtreeStrategy::RightLinear,
        VtreeStrategy::LeftLinear,
        VtreeStrategy::Syntactic,
        VtreeStrategy::Semantic,
    ];

    let mut results = Vec::new();

    for strategy in strategies {
        println!("┌─ Analyzing with {} VTree", strategy);
        println!("│  {}", strategy.description());
        println!("│");

        let mut interpreter = SddAbstractInterpreter::new(&program, strategy);
        let analysis_result = interpreter.analyze();

        // Compute efficiency metrics
        let efficiency = if analysis_result.max_state_size > 0 {
            analysis_result.total_states_computed as f64 / analysis_result.max_state_size as f64
        } else {
            0.0
        };

        println!("│  Initial: {}", analysis_result.initial_state_size);
        println!("│  Max size: {}", analysis_result.max_state_size);
        println!("│  States computed: {}", analysis_result.total_states_computed);
        println!("│  Efficiency ratio: {:.2}", efficiency);
        println!("│");

        if !analysis_result.assertions_violated.is_empty() {
            println!("│  ⚠️  Potential violations:");
            for v in &analysis_result.assertions_violated {
                println!("│    • {}", v);
            }
        } else {
            println!("│  ✓ All assertions safe");
        }
        println!("└─\n");

        results.push((strategy, analysis_result, efficiency));
    }

    // Summary comparison
    println!("📊 Summary Comparison");
    println!("━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━");

    let max_size = results.iter().map(|(_, r, _)| r.max_state_size).max().unwrap_or(1);
    let min_size = results.iter().map(|(_, r, _)| r.max_state_size).min().unwrap_or(1);
    let size_range = max_size as f64 / min_size.max(1) as f64;

    println!("\nMax State Size:");
    for (strategy, result, _) in &results {
        let bar = "█".repeat((result.max_state_size / 2).max(1).min(40));
        println!("  {:12} {:<40} {}", strategy, bar, result.max_state_size);
    }

    println!("\nTotal States Computed:");
    for (strategy, result, _) in &results {
        let bar = "█".repeat((result.total_states_computed / 2).max(1).min(40));
        println!("  {:12} {:<40} {}", strategy, bar, result.total_states_computed);
    }

    println!("\n🔍 Key Observations:");
    println!("  • Size range: {:.1}x (max/min)", size_range);

    let best = results.iter().min_by_key(|(_, r, _)| r.max_state_size).unwrap();
    let worst = results.iter().max_by_key(|(_, r, _)| r.max_state_size).unwrap();

    println!("  • Best (smallest): {} with size {}", best.0, best.1.max_state_size);
    println!("  • Worst (largest): {} with size {}", worst.0, worst.1.max_state_size);

    println!("\n💡 Insights:");
    println!("  Different VTree structures affect how the SDD decomposes variable");
    println!("  dependencies. A good VTree aligns with program structure to minimize");
    println!("  intermediate SDD size during analysis.");
}

fn create_test_program() -> Program {
    vec![
        Stmt::Assign(Var::new(1), Expr::Const(0)), // x := 0
        Stmt::Assign(Var::new(2), Expr::Const(1)), // y := 1
        Stmt::Assign(Var::new(3), Expr::Const(2)), // z := 2
        Stmt::Assume(Predicate::Lt(
            // assume x < y
            Expr::Var(Var::new(1)),
            Expr::Var(Var::new(2)),
        )),
        Stmt::If(
            Predicate::Lt(Expr::Var(Var::new(2)), Expr::Var(Var::new(3))),
            vec![Stmt::Assign(
                Var::new(1),
                Expr::Add(Box::new(Expr::Var(Var::new(1))), Box::new(Expr::Const(1))),
            )],
            vec![],
        ),
        Stmt::Assert(Predicate::Lt(
            // assert x < z
            Expr::Var(Var::new(1)),
            Expr::Var(Var::new(3)),
        )),
    ]
}
