//! Find canonical (minimal) expressions for all 16 Boolean functions.
//!
//! Run with: `cargo run -p expr-space --release --example canonical`

use std::collections::HashMap;

use ananke_bdd::bdd::Bdd;
use expr_space::{
    ast::{reconstruct_ast, Expr},
    builder::ExpressionSpaceBuilder,
    encoding::VariableMap,
    eval::truth_table_name,
    filters::Filters,
};

fn main() {
    println!("╔══════════════════════════════════════════════════════════════╗");
    println!("║        Canonical Boolean Expressions (2 variables)           ║");
    println!("╚══════════════════════════════════════════════════════════════╝");
    println!();

    let max_depth = 3;
    let bdd = Bdd::default();
    let vars = VariableMap::new(max_depth);

    // Build and filter expression space
    let mut builder = ExpressionSpaceBuilder::new(&bdd, &vars, max_depth);
    let space = builder.build();

    let filters = Filters::new(&bdd, &vars, max_depth);
    let filtered = filters.apply_all_simple(space);

    let total = bdd.sat_count(filtered, vars.num_vars());
    println!("Filtered expression space: {} trees\n", total);

    // Find ALL expressions for each truth table, collect top variants
    // This shows us what forms are actually available in the filtered space
    let mut variants: HashMap<u8, Vec<(Expr, usize, usize, bool)>> = HashMap::new();

    for path in bdd.paths(filtered) {
        if let Some(expr) = reconstruct_ast(&path, &vars) {
            let tt = expr.truth_table();
            let depth = expr.depth();
            let size = expr.size();
            let is_negated = matches!(expr, Expr::Not(_));

            variants.entry(tt).or_insert_with(Vec::new).push((expr, depth, size, is_negated));
        }
    }

    // Sort variants for each truth table by (depth, size, is_negated)
    for exprs in variants.values_mut() {
        exprs.sort_by_key(|(_, depth, size, is_neg)| (*depth, *size, *is_neg));
        exprs.dedup_by(|a, b| a.0 == b.0); // Remove duplicates
    }

    // For displaying, pick the best one as canonical
    let canonicals: HashMap<u8, Expr> = variants.iter().map(|(&tt, exprs)| (tt, exprs[0].0.clone())).collect();

    // Display results
    println!("┌────────────┬──────────────┬───────┬──────┬─────────────────────────┐");
    println!("│ Truth Table│ Function     │ Depth │ Size │ Canonical Expression    │");
    println!("├────────────┼──────────────┼───────┼──────┼─────────────────────────┤");

    for tt in 0u8..16 {
        if let Some(expr) = canonicals.get(&tt) {
            println!(
                "│ {:04b}       │ {:12} │ {:5} │ {:4} │ {:23} │",
                tt,
                truth_table_name(tt),
                expr.depth(),
                expr.size(),
                expr.to_string()
            );
        } else {
            println!(
                "│ {:04b}       │ {:12} │   -   │  -   │ (not found)             │",
                tt,
                truth_table_name(tt)
            );
        }
    }

    println!("└────────────┴──────────────┴───────┴──────┴─────────────────────────┘");
    println!();

    // Show top variants for selected functions to illustrate alternative forms
    println!("Alternative forms (top 8 minimal variants):\n");

    let show_variants_for = vec![0x01, 0x07, 0x06, 0x0E, 0x02, 0x04]; // AND, OR, XOR, NAND, x∧¬y, ¬x∧y

    for &tt in &show_variants_for {
        if let Some(exprs) = variants.get(&tt) {
            println!("  {} ({}):", truth_table_name(tt), format!("{:04b}", tt));
            for (idx, (expr, depth, size, is_neg)) in exprs.iter().take(8).enumerate() {
                let marker = if idx == 0 { "→ " } else { "  " };
                let negation_note = if *is_neg { " [negated]" } else { "" };
                println!(
                    "    {} Depth {} Size {}: {}{}",
                    marker,
                    depth,
                    size,
                    expr.to_string(),
                    negation_note
                );
            }
            if exprs.len() > 8 {
                println!("    ... and {} more variants", exprs.len() - 8);
            }
            println!();
        }
    }

    // Summary
    println!("Summary:");
    println!("  Functions with canonical form: {}/16", canonicals.len());

    let depths: Vec<_> = canonicals.values().map(|e| e.depth()).collect();
    if !depths.is_empty() {
        let max_depth = depths.iter().max().unwrap();
        let avg_depth: f64 = depths.iter().map(|&d| d as f64).sum::<f64>() / depths.len() as f64;
        println!("  Max depth needed: {}", max_depth);
        println!("  Average depth: {:.2}", avg_depth);
    }
}
