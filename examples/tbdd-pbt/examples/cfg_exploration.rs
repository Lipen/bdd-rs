//! CFG Exploration Example
//!
//! Demonstrates how to:
//! 1. Build a Control Flow Graph programmatically
//! 2. Extract predicates automatically
//! 3. Enumerate paths and generate tests
//! 4. Visualize the CFG in DOT format
//!
//! Run with: `cargo run -p tbdd-pbt --example cfg_exploration`

use ananke_bdd::bdd::Bdd;
use tbdd_pbt::cfg::CfgBuilder;
use tbdd_pbt::{GeneratorConfig, IntervalSolver, Predicate, TestGenerator};

/// The function being tested
fn classify(x: i64) -> &'static str {
    if x < 0 {
        "negative"
    } else if x == 0 {
        "zero"
    } else if x < 100 {
        "small"
    } else {
        "large"
    }
}

fn main() {
    println!("══════════════════════════════════════════════════════════════");
    println!("  T-BDD: Control Flow Graph Exploration");
    println!("══════════════════════════════════════════════════════════════\n");

    // ─────────────────────────────────────────────────────────────────────────
    // Build CFG for a simple classification function
    // ─────────────────────────────────────────────────────────────────────────

    println!("── BUILDING CFG ─────────────────────────────────────────────────");
    println!();
    println!("  Modeling function:");
    println!("    fn classify(x: i64) -> &str {{");
    println!("        if x < 0 {{");
    println!("            \"negative\"");
    println!("        }} else if x == 0 {{");
    println!("            \"zero\"");
    println!("        }} else if x < 100 {{");
    println!("            \"small\"");
    println!("        }} else {{");
    println!("            \"large\"");
    println!("        }}");
    println!("    }}");
    println!();

    let mut builder = CfgBuilder::new();

    // Create blocks
    let entry = builder.entry();
    let negative = builder.new_block("negative");
    let check_zero = builder.new_block("check_zero");
    let zero = builder.new_block("zero");
    let check_small = builder.new_block("check_small");
    let small = builder.new_block("small");
    let large = builder.new_block("large");

    // Define predicates
    let p_lt_zero = Predicate::lt("x", 0);
    let p_eq_zero = Predicate::eq("x", 0);
    let p_lt_100 = Predicate::lt("x", 100);

    // Wire up control flow
    builder.add_branch(entry, p_lt_zero.clone(), negative, check_zero);
    builder.add_return(negative);
    builder.add_branch(check_zero, p_eq_zero.clone(), zero, check_small);
    builder.add_return(zero);
    builder.add_branch(check_small, p_lt_100.clone(), small, large);
    builder.add_return(small);
    builder.add_return(large);

    let cfg = builder.build();

    println!("  CFG Statistics:");
    println!("    Blocks: {}", cfg.num_blocks());
    println!("    Edges:  {}", cfg.num_edges());
    println!("    Exits:  {}", cfg.exits().len());
    println!();

    // ─────────────────────────────────────────────────────────────────────────
    // Extract predicates
    // ─────────────────────────────────────────────────────────────────────────

    println!("── EXTRACTED PREDICATES ─────────────────────────────────────────");
    println!();

    let predicates = cfg.extract_predicates();
    for (i, pred) in predicates.iter().enumerate() {
        println!("    P{}: {}", i + 1, pred);
    }
    println!();

    // ─────────────────────────────────────────────────────────────────────────
    // Enumerate paths
    // ─────────────────────────────────────────────────────────────────────────

    println!("── PATH ENUMERATION ─────────────────────────────────────────────");
    println!();

    let paths = cfg.enumerate_paths(10);
    println!("  Found {} paths:\n", paths.len());

    for (i, path) in paths.iter().enumerate() {
        let path_desc: Vec<String> = path.condition.iter().map(|lit| lit.to_string()).collect();

        let outcome = match path_desc.len() {
            1 if path_desc[0].contains("x < 0") && !path_desc[0].starts_with('¬') => "negative",
            2 if path_desc[1].contains("x == 0") && !path_desc[1].starts_with('¬') => "zero",
            3 if path_desc[2].contains("x < 100") && !path_desc[2].starts_with('¬') => "small",
            3 => "large",
            _ => "unknown",
        };

        println!("    Path {}: [{}]", i + 1, path_desc.join(", "));
        println!("            → {}", outcome);
        println!();
    }

    // ─────────────────────────────────────────────────────────────────────────
    // Build BDD and generate tests
    // ─────────────────────────────────────────────────────────────────────────

    println!("── BDD CONSTRUCTION & TEST GENERATION ──────────────────────────");
    println!();

    let bdd = Bdd::default();
    let universe = cfg.build_universe(&bdd);

    println!("  Predicate Universe:");
    for pred in universe.predicates() {
        if let Some(var) = universe.get_var(pred) {
            println!("    {} → BDD Var({})", pred, var.id());
        }
    }
    println!();

    // Build path space BDD
    let path_space = cfg.paths_to_bdd(&universe, &bdd, 10);
    let node_count = bdd.count_nodes(&[path_space]);

    println!("  Path Space BDD:");
    println!("    Nodes: {}", node_count);
    println!("    Represents: {} distinct paths", paths.len());
    println!();

    // Generate test cases
    let solver = IntervalSolver::with_bounds(-1000, 1000);
    let config = GeneratorConfig {
        max_tests: 100,
        randomize: false,
    };
    let generator = TestGenerator::new(&bdd, &universe, &solver, config);
    let tests = generator.generate(path_space);

    println!("── GENERATED TEST CASES ─────────────────────────────────────────");
    println!();

    for test in &tests {
        let x = test.witness.get("x").unwrap_or(0);

        // Determine expected result
        let expected = if x < 0 {
            "negative"
        } else if x == 0 {
            "zero"
        } else if x < 100 {
            "small"
        } else {
            "large"
        };

        // Simulate running the function
        let actual = classify(x);
        let status = if expected == actual { "✓" } else { "✗" };

        println!("    {} x = {:>5} → {} (expected: {})", status, x, actual, expected);
    }
    println!();

    // ─────────────────────────────────────────────────────────────────────────
    // Generate DOT visualization
    // ─────────────────────────────────────────────────────────────────────────

    println!("── DOT VISUALIZATION ────────────────────────────────────────────");
    println!();
    println!("  Save the following to 'cfg.dot' and run:");
    println!("    dot -Tpng cfg.dot -o cfg.png");
    println!();
    println!("─────────────────────────────────────────────────────────────────");
    println!("{}", cfg.to_dot());
    println!("─────────────────────────────────────────────────────────────────");

    println!();
    println!("══════════════════════════════════════════════════════════════");
    println!("  CFG exploration complete!");
    println!("══════════════════════════════════════════════════════════════");
}
