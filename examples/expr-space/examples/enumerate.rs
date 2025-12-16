//! Enumerate all expressions and their semantics.
//!
//! Run with: `cargo run -p expr-space --release --example enumerate`

use ananke_bdd::bdd::Bdd;
use expr_space::{ast::reconstruct_ast, builder::ExpressionSpaceBuilder, encoding::VariableMap, eval::truth_table_name};

fn main() {
    println!("=== Expression Enumeration ===\n");

    let max_depth = 2;
    let bdd = Bdd::default();
    let vars = VariableMap::new(max_depth);

    let mut builder = ExpressionSpaceBuilder::new(&bdd, &vars, max_depth);
    let space = builder.build();

    let count = bdd.sat_count(space, vars.num_vars());
    println!("Total expressions (depth ≤ {}): {}\n", max_depth, count);

    println!("All expressions:");
    println!("{:-<60}", "");

    for (i, path) in bdd.paths(space).enumerate() {
        if let Some(expr) = reconstruct_ast(&path, &vars) {
            let tt = expr.truth_table();
            println!(
                "{:4}. {:04b} {:12} | depth={} size={} | {}",
                i + 1,
                tt,
                truth_table_name(tt),
                expr.depth(),
                expr.size(),
                expr
            );
        }
    }
}
