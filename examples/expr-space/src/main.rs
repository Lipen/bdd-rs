//! Main binary for expression space exploration.
//!
//! Run with: `cargo run -p expr-space --release`
//!
//! ## Key Insight: BDD Node Expansion During Filtering
//!
//! Filtering creates a paradoxical effect: as we remove invalid expressions via
//! constraint intersection, the BDD representation can EXPAND in node count.
//!
//! **Why this happens:**
//! - Raw space: 268M trees share massive structural redundancy → compressed to 584 BDD nodes
//! - Filtered space: 45K trees are more topologically DIVERSE → require 1,417 BDD nodes
//!
//! **Analogy:** Imagine a dense city skyline (many buildings share walls/structure).
//! When you "filter" to only keep buildings with specific architectural features,
//! you end up with scattered, diverse buildings that need more total materials.
//!
//! Each filter operation (`result = result * constraint_filter`) adds:
//! - Constraint intersection (AND operation)
//! - Negation boundaries (NOT operation)
//! - More explicit nodes to represent what's EXCLUDED vs. INCLUDED
//!
//! This is why: no-idempotent filter adds 400 nodes, commutativity adds 526 more.
//! The payoff: correct expression space with canonical forms and variants!

use std::collections::{BinaryHeap, HashMap};

use ananke_bdd::bdd::Bdd;
use clap::Parser;
use expr_space::{
    ast::{reconstruct_ast, Expr},
    builder::ExpressionSpaceBuilder,
    encoding::VariableMap,
    eval::{truth_table_name, SymbolicEvaluator},
    filters::Filters,
};
use num_traits::cast::ToPrimitive;

/// Generic top-K container using a max-heap for streaming tracking.
/// Keeps the K *smallest* items (pops the largest when size > K).
struct TopK<T: Ord> {
    k: usize,
    heap: BinaryHeap<T>,
}

impl<T: Ord> TopK<T> {
    fn new(k: usize) -> Self {
        Self {
            k,
            heap: BinaryHeap::with_capacity(k + 1),
        }
    }

    fn push(&mut self, item: T) {
        self.heap.push(item);
        if self.heap.len() > self.k {
            self.heap.pop(); // Pop the largest when exceeding K
        }
    }

    fn into_sorted_vec(mut self) -> Vec<T> {
        let mut result = Vec::with_capacity(self.heap.len());
        while let Some(item) = self.heap.pop() {
            result.push(item);
        }
        result.reverse(); // Reverse to get ascending order
        result
    }
}

#[derive(Parser)]
#[command(name = "expr-space")]
#[command(about = "Symbolic expression space exploration via BDD")]
struct Args {
    /// Maximum tree depth
    #[arg(short, long, default_value = "3")]
    depth: u32,

    /// Apply filters to reduce redundancy
    #[arg(short, long)]
    filter: bool,

    /// Show semantic partitions
    #[arg(short, long)]
    semantics: bool,

    /// Show sample expressions
    #[arg(short = 'n', long, default_value = "5")]
    samples: usize,
}

fn main() -> color_eyre::Result<()> {
    color_eyre::install()?;
    simplelog::TermLogger::init(
        simplelog::LevelFilter::Info,
        simplelog::Config::default(),
        simplelog::TerminalMode::Mixed,
        simplelog::ColorChoice::Auto,
    )?;

    let args = Args::parse();

    println!("╔══════════════════════════════════════════════════════════════╗");
    println!("║     Symbolic Expression Space Exploration via BDD            ║");
    println!("╚══════════════════════════════════════════════════════════════╝");
    println!();

    // Configuration
    println!("Configuration:");
    println!("  Max depth: {}", args.depth);
    println!("  Filters: {}", if args.filter { "enabled" } else { "disabled" });
    println!();

    // Initialize
    let bdd = Bdd::default();
    let vars = VariableMap::new(args.depth);

    println!("Encoding:");
    println!("  Positions: {}", vars.num_positions());
    println!("  BDD variables: {}", vars.num_vars());
    println!();

    // Build expression space
    println!("Building expression space...");
    let start = std::time::Instant::now();
    let mut builder = ExpressionSpaceBuilder::new(&bdd, &vars, args.depth);
    let mut space = builder.build();
    let build_time = start.elapsed();

    let raw_count = bdd.sat_count(space, vars.num_vars());
    let raw_nodes = bdd.size(space);

    println!("Raw expression space:");
    println!("  Trees: {}", raw_count);
    println!("  BDD nodes: {}", raw_nodes);
    println!("  Build time: {:.3}ms", build_time.as_secs_f64() * 1000.0);
    println!();

    // Apply filters if requested
    if args.filter {
        println!("Applying filters...");
        let filters = Filters::new(&bdd, &vars, args.depth);
        let raw_count_f64 = raw_count.to_string().parse::<f64>().unwrap_or(1.0);

        let no_double_neg = filters.no_double_negation();
        space = bdd.eval(space * no_double_neg);
        let after_neg = bdd.sat_count(space, vars.num_vars());
        let after_neg_nodes = bdd.size(space);
        let after_neg_f64 = after_neg.to_f64().unwrap();
        let reduction_neg = (1.0 - after_neg_f64 / raw_count_f64) * 100.0;
        println!(
            "  After no-double-negation: {} trees ({:.1}% reduction) | {} BDD nodes",
            after_neg, reduction_neg, after_neg_nodes
        );

        let no_const = filters.no_constant_ops();
        space = bdd.eval(space * no_const);
        let after_const = bdd.sat_count(space, vars.num_vars());
        let after_const_nodes = bdd.size(space);
        let after_const_f64 = after_const.to_string().parse::<f64>().unwrap_or(0.0);
        let reduction_const = (1.0 - after_const_f64 / raw_count_f64) * 100.0;
        println!(
            "  After no-constant-ops: {} trees ({:.1}% reduction) | {} BDD nodes",
            after_const, reduction_const, after_const_nodes
        );

        let no_idemp = filters.no_idempotent_simple();
        space = bdd.eval(space * no_idemp);
        let after_idemp = bdd.sat_count(space, vars.num_vars());
        let after_idemp_nodes = bdd.size(space);
        let after_idemp_f64 = after_idemp.to_string().parse::<f64>().unwrap_or(0.0);
        let reduction_idemp = (1.0 - after_idemp_f64 / raw_count_f64) * 100.0;
        println!(
            "  After no-idempotent: {} trees ({:.1}% reduction) | {} BDD nodes",
            after_idemp, reduction_idemp, after_idemp_nodes
        );

        let comm = filters.commutativity_simple();
        space = bdd.eval(space * comm);
        let after_comm = bdd.sat_count(space, vars.num_vars());
        let after_comm_nodes = bdd.size(space);
        let after_comm_f64 = after_comm.to_string().parse::<f64>().unwrap_or(0.0);
        let reduction_comm = (1.0 - after_comm_f64 / raw_count_f64) * 100.0;
        println!(
            "  After commutativity: {} trees ({:.1}% reduction) | {} BDD nodes",
            after_comm, reduction_comm, after_comm_nodes
        );

        println!();
        println!("Filtered expression space:");
        println!("  Trees: {} ({:.1}% of {})", after_comm, 100.0 - reduction_comm, raw_count);
        println!("  BDD nodes: {} (was {} in raw space)", bdd.size(space), raw_nodes);
        println!("  Overall reduction: {:.2}% (from {} to {})", reduction_comm, raw_count, after_comm);
        println!();
    }

    // Semantic partitioning and track actual totals
    let mut actual_totals: HashMap<u8, usize> = HashMap::new();
    if args.semantics {
        println!("Semantic partitioning...");
        let mut eval = SymbolicEvaluator::new(&bdd, &vars, args.depth);
        let partitions = eval.partition_by_semantics(space);

        println!();
        println!("┌────────────┬──────────────┬────────────┐");
        println!("│ Truth Table│ Function     │ Tree Count │");
        println!("├────────────┼──────────────┼────────────┤");

        let mut sorted: Vec<_> = partitions.iter().collect();
        sorted.sort_by_key(|(&tt, _)| tt);

        for (&tt, &partition) in sorted {
            let count = bdd.sat_count(partition, vars.num_vars());
            if count > 0u32.into() {
                let count_usize = count.to_usize().unwrap_or(0);
                actual_totals.insert(tt, count_usize);
                println!("│ {:04b}       │ {:12} │ {:>10} │", tt, truth_table_name(tt), count);
            }
        }
        println!("└────────────┴──────────────┴────────────┘");
        println!();
    }

    // Now extract canonical forms from the filtered space
    println!("Finding canonical forms...");
    let max_canonical_forms: usize = args.samples.max(1);
    let mut canonicals_heap: HashMap<u8, TopK<(usize, usize, bool, String, Vec<i32>)>> = HashMap::new();

    for path in bdd.paths(space) {
        if let Some(expr) = reconstruct_ast(&path, &vars) {
            let tt = expr.truth_table();
            let depth = expr.depth();
            let size = expr.size();
            let is_negated = matches!(expr, Expr::Not(_));
            let expr_str = expr.to_string(); // Tiebreaker for canonical ordering
            let path_i32: Vec<i32> = path.iter().map(|lit| lit.to_dimacs()).collect();

            canonicals_heap
                .entry(tt)
                .or_insert_with(|| TopK::new(max_canonical_forms))
                .push((depth, size, is_negated, expr_str, path_i32));
        }
    }

    let mut canonicals: HashMap<u8, Vec<(Expr, usize, usize, bool)>> = HashMap::new();
    for (tt, topk) in canonicals_heap {
        let best_paths = topk.into_sorted_vec();
        let mut forms: Vec<_> = best_paths
            .into_iter()
            .filter_map(|(d, s, neg, _expr_str, path_i32)| {
                let lit_path: Vec<_> = path_i32.iter().map(|&v| ananke_bdd::types::Lit::from_dimacs(v)).collect();
                reconstruct_ast(&lit_path, &vars).map(|expr| (expr, d, s, neg))
            })
            .collect();
        forms.dedup_by(|a, b| a.0 == b.0);
        canonicals.insert(tt, forms);
    }
    println!();

    // Display canonical forms
    println!("Canonical forms for all 16 Boolean functions:");
    println!();
    println!("┌────────────┬──────────────┬───────┬──────┬─────────────────────────┐");
    println!("│ Truth Table│ Function     │ Depth │ Size │ Canonical Expression    │");
    println!("├────────────┼──────────────┼───────┼──────┼─────────────────────────┤");

    for tt in 0u8..16 {
        if let Some(exprs) = canonicals.get(&tt) {
            if !exprs.is_empty() {
                let (expr, depth, size, _) = &exprs[0];
                println!(
                    "│ {:04b}       │ {:12} │ {:5} │ {:4} │ {:23} │",
                    tt,
                    truth_table_name(tt),
                    depth,
                    size,
                    expr.to_string()
                );
            }
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

    // Show sample expressions (from canonical forms)
    println!("Best canonical forms (limited to {} per function): ", max_canonical_forms);
    println!();
    let show_for = vec![0x01u8, 0x07, 0x06, 0x0E, 0, 0x0F]; // AND, OR, XOR, NAND, TRUE, FALSE
    for &tt in &show_for {
        if let Some(exprs) = canonicals.get(&tt) {
            println!("  {} ({:04b}):", truth_table_name(tt), tt);
            for (idx, (expr, depth, size, _is_neg)) in exprs.iter().take(max_canonical_forms).enumerate() {
                let marker = if idx == 0 { "→ " } else { "  " };
                println!("    {} depth {}, size {}: {}", marker, depth, size, expr);
            }
            if let Some(&total) = actual_totals.get(&tt) {
                // We have actual total from semantics analysis
                let remaining = total.saturating_sub(max_canonical_forms);
                println!("    ... and {} more (of {} total)", remaining, total);
            } else {
                // We don't know the actual total
                println!("    ... and more");
            }
            println!();
        } else {
            println!("  {} ({:04b}): (not found)\n", truth_table_name(tt), tt);
        }
    }

    println!("Done!");
    Ok(())
}
