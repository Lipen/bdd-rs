//! Cache statistics analyzer for BDD operations.
//!
//! This example measures cache hit rates for various BDD workloads
//! to inform cache optimization decisions.
//!
//! Run with:
//! ```bash
//! cargo run --release --example cache_stats -- [n-queens size]
//! ```

use std::time::Instant;

use bdd_rs::bdd::{Bdd, BddConfig};
use bdd_rs::reference::Ref;
use clap::Parser;

#[derive(Debug, Parser)]
#[command(author, version, about = "Cache statistics analyzer for BDD")]
struct Cli {
    /// N-Queens problem size
    #[arg(default_value = "6")]
    n: usize,

    /// Cache size in bits (size = 2^bits) for detailed analysis
    #[arg(long, default_value = "14")]
    cache_bits: usize,
}

fn main() {
    let cli = Cli::parse();

    println!("=== BDD Cache Statistics Analyzer ===\n");

    // Test different cache sizes
    let cache_sizes = [12, 14, 16, 18, 20];

    println!("Workload: {}-Queens Problem\n", cli.n);
    println!(
        "{:>12} {:>12} {:>12} {:>12} {:>10} {:>10}",
        "Cache Size", "Time (ms)", "Hits", "Misses", "Hit Rate", "Nodes"
    );
    println!("{}", "-".repeat(80));

    for &cache_bits in &cache_sizes {
        let config = BddConfig::default().with_cache_bits(cache_bits);
        let bdd = Bdd::with_config(config);

        let start = Instant::now();
        let result = solve_queens(&bdd, cli.n);
        let elapsed = start.elapsed();

        let cache = bdd.cache();
        let hits = cache.hits();
        let misses = cache.misses();
        let total = hits + misses;
        let hit_rate = if total > 0 { 100.0 * hits as f64 / total as f64 } else { 0.0 };

        println!(
            "{:>12} {:>12.2} {:>12} {:>12} {:>9.1}% {:>10}",
            format!("2^{}", cache_bits),
            elapsed.as_secs_f64() * 1000.0,
            hits,
            misses,
            hit_rate,
            bdd.num_nodes()
        );

        // Verify result is valid
        let sat_count = bdd.sat_count(result, cli.n * cli.n);
        if cli.n <= 8 {
            let expected: u64 = match cli.n {
                1 => 1,
                2 => 0,
                3 => 0,
                4 => 2,
                5 => 10,
                6 => 4,
                7 => 40,
                8 => 92,
                _ => 0,
            };
            assert_eq!(sat_count, expected.into(), "Wrong solution count for {}-queens", cli.n);
        }
    }

    println!("\n{}", "=".repeat(80));

    // Detailed analysis for the specified cache size
    println!("\nDetailed Analysis (cache_bits={})\n", cli.cache_bits);

    let config = BddConfig::default().with_cache_bits(cli.cache_bits);
    let bdd = Bdd::with_config(config);

    let start = Instant::now();
    let result = solve_queens(&bdd, cli.n);
    let elapsed = start.elapsed();

    let cache = bdd.cache();
    println!("  Cache hits:   {}", cache.hits());
    println!("  Cache misses: {}", cache.misses());
    println!("  Cache faults: {}", cache.faults());
    println!(
        "  Hit rate:     {:.2}%",
        100.0 * cache.hits() as f64 / (cache.hits() + cache.misses()) as f64
    );
    println!("  Final nodes:  {}", bdd.num_nodes());
    println!("  Result size:  {}", bdd.size(result));
    println!("  Time:         {:.2} ms", elapsed.as_secs_f64() * 1000.0);

    // Analysis of faults vs misses
    let empty_misses = cache.misses() - cache.faults();
    println!("\n  Collision analysis:");
    println!(
        "    Key collisions (faults): {} ({:.1}% of lookups)",
        cache.faults(),
        100.0 * cache.faults() as f64 / (cache.hits() + cache.misses()) as f64
    );
    println!(
        "    Empty slot misses:       {} ({:.1}% of lookups)",
        empty_misses,
        100.0 * empty_misses as f64 / (cache.hits() + cache.misses()) as f64
    );
}

/// Solve N-Queens and return the result BDD.
fn solve_queens(bdd: &Bdd, n: usize) -> Ref {
    let var = |i: usize, j: usize| -> Ref { bdd.mk_var((i * n + j + 1) as u32) };

    let mut result = bdd.one();

    // Row constraints
    for i in 0..n {
        let mut at_least_one = bdd.zero();
        for j in 0..n {
            at_least_one = bdd.apply_or(at_least_one, var(i, j));
        }
        result = bdd.apply_and(result, at_least_one);

        for j1 in 0..n {
            for j2 in (j1 + 1)..n {
                let not_both = bdd.apply_or(-var(i, j1), -var(i, j2));
                result = bdd.apply_and(result, not_both);
            }
        }
    }

    // Column constraints
    for j in 0..n {
        for i1 in 0..n {
            for i2 in (i1 + 1)..n {
                let not_both = bdd.apply_or(-var(i1, j), -var(i2, j));
                result = bdd.apply_and(result, not_both);
            }
        }
    }

    // Diagonal constraints
    for i1 in 0..n {
        for j1 in 0..n {
            for i2 in (i1 + 1)..n {
                for j2 in 0..n {
                    let di = i2 - i1;
                    if j2 == j1 + di || (j1 >= di && j2 == j1 - di) {
                        let not_both = bdd.apply_or(-var(i1, j1), -var(i2, j2));
                        result = bdd.apply_and(result, not_both);
                    }
                }
            }
        }
    }

    result
}
