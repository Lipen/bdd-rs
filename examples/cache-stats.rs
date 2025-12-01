//! Cache statistics analyzer for BDD operations.
//!
//! This example measures cache hit rates for various BDD workloads
//! to inform cache optimization decisions.
//!
//! Run with:
//! ```bash
//! cargo run --release --example cache_stats -- 10 -c 14 16 18 20 22
//! ```

use std::time::Instant;

use bdd_rs::bdd::{Bdd, BddConfig};
use bdd_rs::reference::Ref;
use clap::Parser;

#[derive(Debug, Parser)]
#[command(author, version, about = "Cache statistics analyzer for BDD")]
struct Cli {
    /// N-Queens problem size
    #[arg(default_value = "8")]
    n: usize,

    /// Cache sizes in bits (size = 2^bits). Can specify multiple.
    /// Example: `--cache-bits 12 14 16`
    #[arg(short = 'c', long = "cache-bits", num_args = 1.., value_delimiter = ' ')]
    cache_bits: Option<Vec<usize>>,
}

/// Statistics collected for each cache configuration.
#[derive(Debug, Clone)]
struct CacheStats {
    cache_bits: usize,
    time_ms: f64,
    hits: usize,
    misses: usize,
    faults: usize,
    nodes: usize,
    result_size: u64,
}

impl CacheStats {
    fn hit_rate(&self) -> f64 {
        let total = self.hits + self.misses;
        if total > 0 {
            100.0 * self.hits as f64 / total as f64
        } else {
            0.0
        }
    }

    fn collision_rate(&self) -> f64 {
        let total = self.hits + self.misses;
        if total > 0 {
            100.0 * self.faults as f64 / total as f64
        } else {
            0.0
        }
    }

    fn empty_miss_rate(&self) -> f64 {
        let total = self.hits + self.misses;
        let empty_misses = self.misses.saturating_sub(self.faults);
        if total > 0 {
            100.0 * empty_misses as f64 / total as f64
        } else {
            0.0
        }
    }

    fn total_lookups(&self) -> usize {
        self.hits + self.misses
    }
}

fn main() {
    let cli = Cli::parse();

    // Require at least one cache size
    let cache_sizes: Vec<usize> = cli.cache_bits.unwrap_or_else(|| vec![14, 16, 18, 20]);

    println!("=== BDD Cache Statistics Analyzer ===\n");
    println!("Workload: {}-Queens Problem", cli.n);
    println!(
        "Cache sizes to test: {:?}\n",
        cache_sizes.iter().map(|b| format!("2^{}", b)).collect::<Vec<_>>()
    );
    println!("{}", "=".repeat(80));

    // Collect stats for each cache size
    let mut all_stats: Vec<CacheStats> = Vec::new();

    for &cache_bits in &cache_sizes {
        println!("\n[Cache Size: 2^{} = {} entries]\n", cache_bits, 1usize << cache_bits);

        let config = BddConfig::default().with_cache_bits(cache_bits);
        let bdd = Bdd::with_config(config);

        let start = Instant::now();
        let result = solve_queens(&bdd, cli.n);
        let elapsed = start.elapsed();

        let cache = bdd.cache();
        let stats = CacheStats {
            cache_bits,
            time_ms: elapsed.as_secs_f64() * 1000.0,
            hits: cache.hits(),
            misses: cache.misses(),
            faults: cache.faults(),
            nodes: bdd.num_nodes(),
            result_size: bdd.size(result),
        };

        // Print detailed stats
        println!("  Time:           {:>10.2} ms", stats.time_ms);
        println!("  Cache hits:     {:>10}", stats.hits);
        println!("  Cache misses:   {:>10}", stats.misses);
        println!("  Cache faults:   {:>10}", stats.faults);
        println!("  Hit rate:       {:>10.2} %", stats.hit_rate());
        println!("  Collision rate: {:>10.1} %", stats.collision_rate());
        println!("  Empty misses:   {:>10.1} %", stats.empty_miss_rate());
        println!("  Total lookups:  {:>10}", stats.total_lookups());
        println!("  Allocated nodes:{:>10}", stats.nodes);
        println!("  Result size:    {:>10}", stats.result_size);

        // Verify result
        let sat_count = bdd.sat_count(result, cli.n * cli.n);
        let expected: u64 = match cli.n {
            1 => 1,
            2 => 0,
            3 => 0,
            4 => 2,
            5 => 10,
            6 => 4,
            7 => 40,
            8 => 92,
            9 => 352,
            10 => 724,
            11 => 2680,
            12 => 14200,
            13 => 73712,
            14 => 365596,
            _ => u64::MAX,
        };
        if expected != u64::MAX {
            assert_eq!(sat_count, expected.into(), "Wrong solution count for {}-queens", cli.n);
            println!("  Solutions:      {:>10} ✓", expected);
        }

        all_stats.push(stats);
    }

    // Print comparison table
    println!("\n{}", "=".repeat(80));
    println!("\n=== Comparison Table ===\n");

    println!(
        "{:>12} {:>12} {:>10} {:>10} {:>10} {:>10}",
        "Cache Size", "Time (ms)", "Hit Rate", "Collision", "Lookups", "Nodes"
    );
    println!("{}", "-".repeat(78));

    for stats in &all_stats {
        println!(
            "{:>12} {:>12.1} {:>9.1}% {:>9.1}% {:>10} {:>10}",
            format!("2^{}", stats.cache_bits),
            stats.time_ms,
            stats.hit_rate(),
            stats.collision_rate(),
            format_num(stats.total_lookups()),
            format_num(stats.nodes),
        );
    }

    // Find best configuration
    if let Some(best) = all_stats.iter().min_by(|a, b| a.time_ms.partial_cmp(&b.time_ms).unwrap()) {
        println!("\n  ⭐ Fastest: 2^{} ({:.2} ms)", best.cache_bits, best.time_ms);
    }
    if let Some(best) = all_stats.iter().max_by(|a, b| a.hit_rate().partial_cmp(&b.hit_rate()).unwrap()) {
        println!("  📊 Best hit rate: 2^{} ({:.1}%)", best.cache_bits, best.hit_rate());
    }
    if let Some(best) = all_stats
        .iter()
        .min_by(|a, b| a.collision_rate().partial_cmp(&b.collision_rate()).unwrap())
    {
        println!("  🎯 Lowest collisions: 2^{} ({:.1}%)", best.cache_bits, best.collision_rate());
    }

    println!();
}

/// Format large numbers with K/M suffixes.
fn format_num(n: usize) -> String {
    if n < 1_000 {
        n.to_string()
    } else if n < 1_000_000 {
        format!("{:.1}K", n as f64 / 1_000.0)
    } else {
        format!("{:.2}M", n as f64 / 1_000_000.0)
    }
}

// ============================================================================
// N-Queens Solver (efficient encoding from queens.rs)
// ============================================================================

/// Returns the variable ID for the cell at `(row, col)`.
/// Variables are 1-indexed: `x_{0,0} = 1`, `x_{0,1} = 2`, etc.
fn var(n: usize, row: usize, col: usize) -> u32 {
    (row * n + col + 1) as u32
}

/// Solve N-Queens and return the result BDD.
///
/// Uses efficient encoding that builds intermediate constraint BDDs
/// and combines them, rather than applying pairwise constraints directly.
fn solve_queens(bdd: &Bdd, n: usize) -> Ref {
    // Pre-allocate variables in natural order
    let num_vars = n * n;
    for var_id in 1..=num_vars as u32 {
        bdd.mk_var(var_id);
    }
    assert!(bdd.var_order().len() == num_vars);

    let mut result = bdd.one();

    // Constraint 1: At least one queen per row
    let at_least_one = at_least_one_queen_per_row(bdd, n);
    result = bdd.apply_and(result, at_least_one);

    // Constraint 2: At most one queen per row
    let row_amo = at_most_one_queen_per_line(bdd, n, true);
    result = bdd.apply_and(result, row_amo);

    // Constraint 3: At most one queen per column
    let col_amo = at_most_one_queen_per_line(bdd, n, false);
    result = bdd.apply_and(result, col_amo);

    // Constraint 4: At most one queen per anti-diagonal (/)
    let slash = at_most_one_queen_per_diagonal(bdd, n, true);
    result = bdd.apply_and(result, slash);

    // Constraint 5: At most one queen per diagonal (\)
    let backslash = at_most_one_queen_per_diagonal(bdd, n, false);
    result = bdd.apply_and(result, backslash);

    result
}

/// At least one queen per row: `⋀_i (⋁_j x_{i,j})`
fn at_least_one_queen_per_row(bdd: &Bdd, n: usize) -> Ref {
    let mut result = bdd.one();

    for row in 0..n {
        // Build disjunction: `x_{row,0} ∨ x_{row,1} ∨ ... ∨ x_{row,n-1}`
        let mut row_clause = bdd.zero();
        for col in 0..n {
            let x = bdd.mk_var(var(n, row, col));
            row_clause = bdd.apply_or(row_clause, x);
        }
        result = bdd.apply_and(result, row_clause);
    }

    result
}

/// At most one queen per row/column.
fn at_most_one_queen_per_line(bdd: &Bdd, n: usize, is_row: bool) -> Ref {
    let mut result = bdd.one();

    for i in 0..n {
        // Get all variables in this line
        let vars: Vec<u32> = (0..n).map(|j| if is_row { var(n, i, j) } else { var(n, j, i) }).collect();

        let amo = encode_at_most_one(bdd, &vars);
        result = bdd.apply_and(result, amo);
    }

    result
}

/// At most one queen per diagonal.
/// `slash=true` for anti-diagonals (`/`), `slash=false` for diagonals (`\`).
fn at_most_one_queen_per_diagonal(bdd: &Bdd, n: usize, slash: bool) -> Ref {
    let mut result = bdd.one();

    let (a, b) = if slash { (-(n as i32), n as i32) } else { (0, 2 * n as i32) };

    for k in a..b {
        // Collect cells on this diagonal
        let cells: Vec<(usize, usize)> = (0..n)
            .filter_map(|i| {
                let j = if slash { (i as i32 + k) as usize } else { (k - i as i32) as usize };
                if j < n {
                    Some((i, j))
                } else {
                    None
                }
            })
            .collect();

        if cells.len() <= 1 {
            continue; // No constraint needed for single cell or empty diagonal
        }

        let vars: Vec<u32> = cells.iter().map(|&(i, j)| var(n, i, j)).collect();
        let amo = encode_at_most_one(bdd, &vars);
        result = bdd.apply_and(result, amo);
    }

    result
}

/// Encodes an at-most-one constraint: at most one variable can be true.
/// For each `x`: `x → ¬(⋁_{y≠x} y)`, which is equivalent to `¬x ∨ ¬(⋁_{y≠x} y)`.
fn encode_at_most_one(bdd: &Bdd, vars: &[u32]) -> Ref {
    if vars.len() <= 1 {
        return bdd.one();
    }

    let mut result = bdd.one();

    for (idx, &x_var) in vars.iter().enumerate() {
        let x = bdd.mk_var(x_var);

        // Build disjunction of all other variables
        let mut others = bdd.zero();
        for (other_idx, &y_var) in vars.iter().enumerate() {
            if other_idx != idx {
                let y = bdd.mk_var(y_var);
                others = bdd.apply_or(others, y);
            }
        }

        // x → ¬others, which is ¬x ∨ ¬others
        let implication = bdd.apply_or(-x, -others);
        result = bdd.apply_and(result, implication);
    }

    result
}
