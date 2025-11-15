use std::fs;
use std::process::Command;

use bdd_rs::bdd::Bdd;
use clap::{Parser, Subcommand, ValueEnum};
use color_eyre::Result;
use symbolic_execution::*;

#[derive(Debug, Clone, Copy, ValueEnum)]
enum VizType {
    /// Generate AST visualization only
    Ast,
    /// Generate CFG visualization only
    Cfg,
    /// Generate both AST and CFG visualizations
    Both,
}

#[derive(Parser)]
#[command(name = "symexec")]
#[command(about = "Symbolic execution engine using BDDs", long_about = None)]
struct Cli {
    #[command(subcommand)]
    command: Commands,
}

#[derive(Subcommand)]
enum Commands {
    /// Run example programs
    Example {
        /// Example name: simple, branch, xor, mutex, loop
        name: String,
    },
    /// Visualize program as AST or CFG
    Viz {
        /// Example name
        example: String,
        /// Visualization type
        #[arg(short, long, default_value = "both")]
        type_: VizType,
        /// Output file (without extension)
        #[arg(short, long)]
        output: Option<String>,
    },
}

fn main() -> Result<()> {
    color_eyre::install()?;
    let cli = Cli::parse();

    let bdd = Bdd::default();

    match cli.command {
        Commands::Example { name } => {
            run_example(&bdd, &name)?;
        }
        Commands::Viz { example, type_, output } => {
            visualize_example(&example, type_, output.as_deref())?;
        }
    }

    Ok(())
}

fn run_example(bdd: &Bdd, name: &str) -> Result<()> {
    let (prog_name, stmt) = match name {
        "simple" => example_simple(),
        "branch" => example_branch(),
        "xor" => example_xor(),
        "mutex" => example_mutex(),
        "loop" => example_loop(),
        _ => {
            eprintln!("Unknown example: {}", name);
            eprintln!("Available: simple, branch, xor, mutex, loop");
            return Ok(());
        }
    };

    println!("=== Example: {} ===\n", prog_name);
    println!("{}\n", Program::new(&prog_name, stmt.clone()));

    let executor = SymbolicExecutor::new(bdd);
    let result = executor.execute(&stmt);

    print_results(&result);

    Ok(())
}

fn visualize_example(name: &str, viz_type: VizType, output: Option<&str>) -> Result<()> {
    let (prog_name, stmt) = match name {
        "simple" => example_simple(),
        "branch" => example_branch(),
        "xor" => example_xor(),
        "mutex" => example_mutex(),
        "loop" => example_loop(),
        _ => {
            eprintln!("Unknown example: {}", name);
            return Ok(());
        }
    };

    // Print the program
    println!("=== Example: {} ===\n", prog_name);
    println!("{}\n", Program::new(&prog_name, stmt.clone()));

    // Create temp directory
    let temp_dir = std::env::temp_dir().join("symexec_viz");
    fs::create_dir_all(&temp_dir)?;

    let base_name = output.unwrap_or(name);

    // Determine which visualizations to generate
    let do_ast = matches!(viz_type, VizType::Ast | VizType::Both);
    let do_cfg = matches!(viz_type, VizType::Cfg | VizType::Both);

    // Generate AST visualization
    if do_ast {
        let dot = ast_to_dot(&stmt, &prog_name);
        let dot_file = temp_dir.join(format!("{}_ast.dot", base_name));
        let svg_file = temp_dir.join(format!("{}_ast.svg", base_name));
        let pdf_file = temp_dir.join(format!("{}_ast.pdf", base_name));

        fs::write(&dot_file, &dot)?;
        println!("Generated AST visualization:");
        println!("  DOT: file://{}", dot_file.display());

        if let Ok(output) = Command::new("dot")
            .args(&["-Tsvg", dot_file.to_str().unwrap(), "-o", svg_file.to_str().unwrap()])
            .output()
        {
            if output.status.success() {
                println!("  SVG: file://{}", svg_file.display());
            }
        }

        if let Ok(output) = Command::new("dot")
            .args(&["-Tpdf", dot_file.to_str().unwrap(), "-o", pdf_file.to_str().unwrap()])
            .output()
        {
            if output.status.success() {
                println!("  PDF: file://{}", pdf_file.display());
            }
        }

        println!();
    }

    // Generate CFG visualization
    if do_cfg {
        let cfg = ControlFlowGraph::from_stmt(&stmt);
        let dot = cfg_to_dot(&cfg, &prog_name);
        let dot_file = temp_dir.join(format!("{}_cfg.dot", base_name));
        let svg_file = temp_dir.join(format!("{}_cfg.svg", base_name));
        let pdf_file = temp_dir.join(format!("{}_cfg.pdf", base_name));

        fs::write(&dot_file, &dot)?;
        println!("Generated CFG visualization:");
        println!("  DOT: file://{}", dot_file.display());

        if let Ok(output) = Command::new("dot")
            .args(&["-Tsvg", dot_file.to_str().unwrap(), "-o", svg_file.to_str().unwrap()])
            .output()
        {
            if output.status.success() {
                println!("  SVG: file://{}", svg_file.display());
            }
        }

        if let Ok(output) = Command::new("dot")
            .args(&["-Tpdf", dot_file.to_str().unwrap(), "-o", pdf_file.to_str().unwrap()])
            .output()
        {
            if output.status.success() {
                println!("  PDF: file://{}", pdf_file.display());
            }
        }

        println!();
    }

    Ok(())
}

fn example_simple() -> (String, Stmt) {
    // x = true; y = x; assert y
    let stmt = Stmt::assign("x", Expr::Lit(true))
        .seq(Stmt::assign("y", Expr::var("x")))
        .seq(Stmt::assert(Expr::var("y")));

    ("simple".to_string(), stmt)
}

fn example_branch() -> (String, Stmt) {
    // if x { y = true } else { y = false }; assert (x == y)
    let stmt = Stmt::if_then_else(
        Expr::var("x"),
        Stmt::assign("y", Expr::Lit(true)),
        Stmt::assign("y", Expr::Lit(false)),
    )
    .seq(Stmt::assert(Expr::var("x").eq(Expr::var("y"))));

    ("branch".to_string(), stmt)
}

fn example_xor() -> (String, Stmt) {
    // z = x ^ y; assert (z == ((x || y) && !(x && y)))
    let stmt = Stmt::assign("z", Expr::var("x").xor(Expr::var("y"))).seq(Stmt::assert(
        Expr::var("z").eq(Expr::var("x").or(Expr::var("y")).and(Expr::var("x").and(Expr::var("y")).not())),
    ));

    ("xor".to_string(), stmt)
}

fn example_mutex() -> (String, Stmt) {
    // Mutual exclusion protocol
    // req1 = true; if req2 { wait } else { acquire1 = true };
    // req2 = true; if req1 { wait } else { acquire2 = true };
    // assert !(acquire1 && acquire2)

    let thread1 = Stmt::assign("req1", Expr::Lit(true)).seq(Stmt::if_then_else(
        Expr::var("req2"),
        Stmt::Skip,
        Stmt::assign("acquire1", Expr::Lit(true)),
    ));

    let thread2 = Stmt::assign("req2", Expr::Lit(true)).seq(Stmt::if_then_else(
        Expr::var("req1"),
        Stmt::Skip,
        Stmt::assign("acquire2", Expr::Lit(true)),
    ));

    let stmt = thread1
        .seq(thread2)
        .seq(Stmt::assert(Expr::var("acquire1").and(Expr::var("acquire2")).not()));

    ("mutex".to_string(), stmt)
}

fn example_loop() -> (String, Stmt) {
    // ```
    // x = false
    // i = 0
    // while i < 3 {
    //   x = !x
    //   i = i + 1
    // }
    // assert !x
    // ```
    // Simplified for boolean domain:
    // x = false; while sym_i { x = !x }; assert !x
    // (sym_i represents symbolic iteration count)

    let stmt = Stmt::assign("x", Expr::Lit(false))
        .seq(Stmt::while_do(Expr::var("sym_i"), Stmt::assign("x", Expr::var("x").not())))
        .seq(Stmt::assert(Expr::var("x").not()));

    ("loop".to_string(), stmt)
}

fn print_results(result: &ExecutionResult) {
    println!("=== Execution Results ===");
    println!("Total paths explored: {}", result.paths_explored);
    println!("Feasible paths: {}", result.feasible_paths);
    println!("Final states: {}", result.final_states.len());
    println!("Assertion failures: {}", result.num_failures());
    println!();

    if result.all_assertions_passed() {
        println!("✓ All assertions PASSED");
    } else {
        println!("✗ Found {} assertion failure(s):", result.num_failures());
        for (i, (state, expr)) in result.assertion_failures.iter().enumerate() {
            println!("\n  Failure #{}: assert {}", i + 1, expr);
            println!("  Path condition is satisfiable:");
            println!("    Feasible: {}", state.is_feasible());

            // Show symbolic values
            println!("  Variable values on failing path:");
            for var in state.vars() {
                if let Some(val) = state.get(var) {
                    let is_must_true = state.bdd().is_one(val);
                    let is_must_false = state.bdd().is_zero(val);

                    let value_str = if is_must_true {
                        "true"
                    } else if is_must_false {
                        "false"
                    } else {
                        "symbolic"
                    };

                    println!("    {} = {}", var, value_str);
                }
            }
        }
    }
    println!();
}
