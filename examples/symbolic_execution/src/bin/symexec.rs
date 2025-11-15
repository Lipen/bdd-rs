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

fn get_example(name: &str) -> Option<Program> {
    match name {
        "simple" => Some(example_simple()),
        "branch" => Some(example_branch()),
        "xor" => Some(example_xor()),
        "mutex" => Some(example_mutex()),
        "loop" => Some(example_loop()),
        "exception" => Some(example_exception()),
        "nested_exception" => Some(example_nested_exception()),
        "nested_finally" => Some(example_nested_finally()),
        "finally_in_catch" => Some(example_finally_in_catch()),
        "multiple_finally" => Some(example_multiple_finally()),
        _ => {
            eprintln!("Unknown example: {}", name);
            eprintln!("Available: simple, branch, xor, mutex, loop, exception, nested_exception, nested_finally, finally_in_catch, multiple_finally");
            None
        }
    }
}

fn run_example(bdd: &Bdd, name: &str) -> Result<()> {
    let program = match get_example(name) {
        Some(p) => p,
        None => return Ok(()),
    };

    println!("=== Example: {} ===\n", program.name);
    println!("{}", program);

    // Build CFG
    let cfg = ControlFlowGraph::from_stmts(&program.body);

    // Execute CFG
    let executor = SymbolicExecutor::new(bdd);
    let initial_state = SymbolicState::new(bdd);
    let result = executor.execute(&cfg, initial_state);

    print_results(&result);

    Ok(())
}

fn visualize_example(name: &str, viz_type: VizType, output: Option<&str>) -> Result<()> {
    let program = match get_example(name) {
        Some(p) => p,
        None => return Ok(()),
    };

    // Print the program
    println!("=== Example: {} ===\n", program.name);
    println!("{}", program);

    // Print CFG
    let cfg = ControlFlowGraph::from_stmts(&program.body);
    println!("{}", cfg);

    // Create temp directory
    let temp_dir = std::env::temp_dir().join("symexec_viz");
    fs::create_dir_all(&temp_dir)?;

    let base_name = output.unwrap_or(name);

    // Determine which visualizations to generate
    let do_ast = matches!(viz_type, VizType::Ast | VizType::Both);
    let do_cfg = matches!(viz_type, VizType::Cfg | VizType::Both);

    // Generate AST visualization
    if do_ast {
        let dot = ast_to_dot(&program.body, &program.name);
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
        let dot = cfg_to_dot(&cfg, &program.name);
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

fn example_simple() -> Program {
    // x = true; y = x; assert y
    Program::new(
        "simple",
        vec![
            Stmt::assign("x", Expr::Lit(true)),
            Stmt::assign("y", Expr::var("x")),
            Stmt::assert(Expr::var("y")),
        ],
    )
}

fn example_branch() -> Program {
    // if x { y = true } else { y = false }; assert (x == y)
    Program::new(
        "branch",
        vec![
            Stmt::if_then_else(
                Expr::var("x"),
                vec![Stmt::assign("y", Expr::Lit(true))],
                vec![Stmt::assign("y", Expr::Lit(false))],
            ),
            Stmt::assert(Expr::var("x").eq(Expr::var("y"))),
        ],
    )
}

fn example_xor() -> Program {
    // z = x ^ y; assert (z == ((x || y) && !(x && y)))
    Program::new(
        "xor",
        vec![
            Stmt::assign("z", Expr::var("x").xor(Expr::var("y"))),
            Stmt::assert(Expr::var("z").eq(Expr::var("x").or(Expr::var("y")).and(Expr::var("x").and(Expr::var("y")).not()))),
        ],
    )
}

fn example_mutex() -> Program {
    // Mutual exclusion protocol
    // req1 = true; if req2 { wait } else { acquire1 = true };
    // req2 = true; if req1 { wait } else { acquire2 = true };
    // assert !(acquire1 && acquire2)
    Program::new(
        "mutex",
        vec![
            Stmt::assign("req1", Expr::Lit(true)),
            Stmt::if_then_else(Expr::var("req2"), vec![Stmt::Skip], vec![Stmt::assign("acquire1", Expr::Lit(true))]),
            Stmt::assign("req2", Expr::Lit(true)),
            Stmt::if_then_else(Expr::var("req1"), vec![Stmt::Skip], vec![Stmt::assign("acquire2", Expr::Lit(true))]),
            Stmt::assert(Expr::var("acquire1").and(Expr::var("acquire2")).not()),
        ],
    )
}

fn example_loop() -> Program {
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
    Program::new(
        "loop",
        vec![
            Stmt::assign("x", Expr::Lit(false)),
            Stmt::while_do(Expr::var("sym_i"), vec![Stmt::assign("x", Expr::var("x").not())]),
            Stmt::assert(Expr::var("x").not()),
        ],
    )
}

fn example_exception() -> Program {
    // Example with try-catch-finally
    // try {
    //   x = true;
    //   if (error) { throw x; }
    //   y = false;
    // } catch (e) {
    //   y = e;
    // } finally {
    //   z = y;
    // }
    // assert (error => z);
    Program::new(
        "exception",
        vec![
            Stmt::try_catch_finally(
                vec![
                    Stmt::assign("x", Expr::Lit(true)),
                    Stmt::if_then(Expr::var("error"), vec![Stmt::throw(Expr::var("x"))]),
                    Stmt::assign("y", Expr::Lit(false)),
                ],
                Some("e".into()),
                vec![Stmt::assign("y", Expr::var("e"))],
                vec![Stmt::assign("z", Expr::var("y"))],
            ),
            Stmt::assert(Expr::var("error").implies(Expr::var("z"))),
        ],
    )
}

fn example_nested_exception() -> Program {
    // Nested try-catch example
    // try {
    //   x = true;
    //   try {
    //     y = true;
    //     if (inner_error) { throw y; }
    //   } catch (e1) {
    //     y = e1;
    //   }
    //   if (outer_error) { throw x; }
    // } catch (e2) {
    //   x = e2;
    // }
    // assert x;
    Program::new(
        "nested_exception",
        vec![
            Stmt::try_catch(
                vec![
                    Stmt::assign("x", Expr::Lit(true)),
                    Stmt::try_catch(
                        vec![
                            Stmt::assign("y", Expr::Lit(true)),
                            Stmt::if_then(Expr::var("inner_error"), vec![Stmt::throw(Expr::var("y"))]),
                        ],
                        Some("e1".into()),
                        vec![Stmt::assign("y", Expr::var("e1"))],
                    ),
                    Stmt::if_then(Expr::var("outer_error"), vec![Stmt::throw(Expr::var("x"))]),
                ],
                Some("e2".into()),
                vec![Stmt::assign("x", Expr::var("e2"))],
            ),
            Stmt::assert(Expr::var("x")),
        ],
    )
}

fn example_nested_finally() -> Program {
    // Nested try-catch-finally example
    // try {
    //   x = true;
    //   try {
    //     y = true;
    //     if (inner_error) { throw y; }
    //   } catch (e1) {
    //     z = e1;
    //   } finally {
    //     inner_finally = true;
    //   }
    //   after_inner = true;
    // } catch (e2) {
    //   outer_catch = true;
    // } finally {
    //   outer_finally = true;
    // }
    // assert inner_finally;
    // assert outer_finally;
    Program::new(
        "nested_finally",
        vec![
            Stmt::try_catch_finally(
                vec![
                    Stmt::assign("x", Expr::Lit(true)),
                    Stmt::try_catch_finally(
                        vec![
                            Stmt::assign("y", Expr::Lit(true)),
                            Stmt::if_then(Expr::var("inner_error"), vec![Stmt::throw(Expr::var("y"))]),
                        ],
                        Some("e1".into()),
                        vec![Stmt::assign("z", Expr::var("e1"))],
                        vec![Stmt::assign("inner_finally", Expr::Lit(true))],
                    ),
                    Stmt::assign("after_inner", Expr::Lit(true)),
                ],
                Some("e2".into()),
                vec![Stmt::assign("outer_catch", Expr::Lit(true))],
                vec![Stmt::assign("outer_finally", Expr::Lit(true))],
            ),
            Stmt::assert(Expr::var("inner_finally")),
            Stmt::assert(Expr::var("outer_finally")),
        ],
    )
}

fn example_finally_in_catch() -> Program {
    // Try-catch where catch block contains try-finally
    // try {
    //   x = true;
    //   if (error) { throw x; }
    // } catch (e) {
    //   in_catch = e;
    //   try {
    //     nested_in_catch = true;
    //     if (nested_error) { throw nested_in_catch; }
    //   } catch (e2) {
    //     nested_catch = e2;
    //   } finally {
    //     nested_finally = true;
    //   }
    // }
    // assert (error => nested_finally);
    Program::new(
        "finally_in_catch",
        vec![
            Stmt::try_catch(
                vec![
                    Stmt::assign("x", Expr::Lit(true)),
                    Stmt::if_then(Expr::var("error"), vec![Stmt::throw(Expr::var("x"))]),
                ],
                Some("e".into()),
                vec![
                    Stmt::assign("in_catch", Expr::var("e")),
                    Stmt::try_catch_finally(
                        vec![
                            Stmt::assign("nested_in_catch", Expr::Lit(true)),
                            Stmt::if_then(Expr::var("nested_error"), vec![Stmt::throw(Expr::var("nested_in_catch"))]),
                        ],
                        Some("e2".into()),
                        vec![Stmt::assign("nested_catch", Expr::var("e2"))],
                        vec![Stmt::assign("nested_finally", Expr::Lit(true))],
                    ),
                ],
            ),
            Stmt::assert(Expr::var("error").implies(Expr::var("nested_finally"))),
        ],
    )
}

fn example_multiple_finally() -> Program {
    // Multiple sequential try-finally blocks in an outer try-finally
    // try {
    //   try {
    //     x = true;
    //   } finally {
    //     finally1 = true;
    //   }
    //   try {
    //     y = true;
    //   } finally {
    //     finally2 = true;
    //   }
    // } finally {
    //   outer_finally = true;
    // }
    // assert (finally1 && finally2 && outer_finally);
    Program::new(
        "multiple_finally",
        vec![
            Stmt::try_catch_finally(
                vec![
                    Stmt::try_catch_finally(
                        vec![Stmt::assign("x", Expr::Lit(true))],
                        None,
                        vec![],
                        vec![Stmt::assign("finally1", Expr::Lit(true))],
                    ),
                    Stmt::try_catch_finally(
                        vec![Stmt::assign("y", Expr::Lit(true))],
                        None,
                        vec![],
                        vec![Stmt::assign("finally2", Expr::Lit(true))],
                    ),
                ],
                None,
                vec![],
                vec![Stmt::assign("outer_finally", Expr::Lit(true))],
            ),
            Stmt::assert(Expr::var("finally1").and(Expr::var("finally2")).and(Expr::var("outer_finally"))),
        ],
    )
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
