//! Exploring interesting Boolean functions.
//!
//! This example searches for functions with extreme BDD sizes and
//! analyzes their structural properties.
//!
//! Run with: `cargo run -p boolean-functions --example explore -- -n 4`

use std::collections::HashMap;

use bdd_rs::bdd::Bdd;
use boolean_functions::function::{build_bdd_from_truth_table, TruthTable};
use clap::Parser;
use rand::SeedableRng;
use rand_chacha::ChaCha8Rng;

#[derive(Parser, Debug)]
#[command(name = "explore")]
#[command(about = "Explore Boolean functions with extreme BDD sizes")]
struct Args {
    /// Number of variables
    #[arg(short, long, default_value_t = 4)]
    n: usize,

    /// Number of samples to search through
    #[arg(short, long, default_value_t = 10000)]
    samples: usize,

    /// Number of extreme functions to report
    #[arg(short, long, default_value_t = 5)]
    top_k: usize,

    /// Random seed
    #[arg(long)]
    seed: Option<u64>,

    /// Exhaustive search (only for small n)
    #[arg(short, long)]
    exhaustive: bool,
}

/// Information about an interesting function
struct FunctionInfo {
    truth_table: TruthTable,
    size: usize,
    minterm_count: usize,
}

fn main() -> color_eyre::Result<()> {
    color_eyre::install()?;

    let args = Args::parse();

    println!("─── Exploring Interesting Boolean Functions ───\n");

    println!("Variables: n = {}", args.n);
    println!("Search mode: {}", if args.exhaustive { "exhaustive" } else { "random sampling" });

    let bdd = Bdd::default();

    let functions: Vec<FunctionInfo> = if args.exhaustive && args.n <= 4 {
        println!("Enumerating all {} functions...\n", TruthTable::total_count(args.n));

        TruthTable::all_functions(args.n)
            .map(|tt| {
                let minterm_count = tt.count_ones();
                let bdd_ref = build_bdd_from_truth_table(&bdd, &tt);
                let size = bdd.size(bdd_ref) as usize;
                FunctionInfo {
                    truth_table: tt,
                    size,
                    minterm_count,
                }
            })
            .collect()
    } else {
        let mut rng = match args.seed {
            Some(s) => ChaCha8Rng::seed_from_u64(s),
            None => ChaCha8Rng::seed_from_u64(rand::random()),
        };

        println!("Sampling {} random functions...\n", args.samples);

        (0..args.samples)
            .map(|_| {
                let tt = TruthTable::random(args.n, &mut rng);
                let minterm_count = tt.count_ones();
                let bdd_ref = build_bdd_from_truth_table(&bdd, &tt);
                let size = bdd.size(bdd_ref) as usize;
                FunctionInfo {
                    truth_table: tt,
                    size,
                    minterm_count,
                }
            })
            .collect()
    };

    // Find smallest BDD functions
    let mut by_size: Vec<_> = functions.iter().enumerate().collect();
    by_size.sort_by_key(|(_, f)| f.size);

    println!("── Functions with SMALLEST BDD ──\n");
    for (idx, func) in by_size.iter().take(args.top_k) {
        print_function_info(&bdd, args.n, func, *idx);
    }

    println!("\n── Functions with LARGEST BDD ──\n");
    for (idx, func) in by_size.iter().rev().take(args.top_k) {
        print_function_info(&bdd, args.n, func, *idx);
    }

    // Analyze size vs minterm count correlation
    println!("\n── Size vs. Minterm Count Analysis ──");

    let mut by_minterm: HashMap<usize, Vec<usize>> = HashMap::new();
    for func in &functions {
        by_minterm.entry(func.minterm_count).or_default().push(func.size);
    }

    println!("\nMinterms │ Count │  Mean Size  │  Min  │  Max  ");
    println!("─────────┼───────┼─────────────┼───────┼───────");

    let mut minterm_counts: Vec<_> = by_minterm.keys().collect();
    minterm_counts.sort();

    for &minterms in minterm_counts.iter().take(10) {
        let sizes = &by_minterm[minterms];
        let mean: f64 = sizes.iter().sum::<usize>() as f64 / sizes.len() as f64;
        let min = *sizes.iter().min().unwrap();
        let max = *sizes.iter().max().unwrap();
        println!("{:>8} │ {:>5} │ {:>11.2} │ {:>5} │ {:>5}", minterms, sizes.len(), mean, min, max);
    }

    if minterm_counts.len() > 20 {
        println!("  ... ({} more minterm values)", minterm_counts.len() - 20);
        // Show last 10
        for &minterms in minterm_counts.iter().rev().take(10).collect::<Vec<_>>().iter().rev() {
            let sizes = &by_minterm[minterms];
            let mean: f64 = sizes.iter().sum::<usize>() as f64 / sizes.len() as f64;
            let min = *sizes.iter().min().unwrap();
            let max = *sizes.iter().max().unwrap();
            println!("{:>8} │ {:>5} │ {:>11.2} │ {:>5} │ {:>5}", minterms, sizes.len(), mean, min, max);
        }
    }

    // Find symmetric functions
    println!("\n── Special Function Classes ──");

    // BDD size includes the terminal node, so:
    // - Constants (0 and 1) have size 1 (just terminal)
    // - Single variable projections have size 2 (one node + terminal)
    let constants: Vec<_> = functions.iter().filter(|f| f.size == 1).collect();
    println!("Constants (size=1): {}", constants.len());

    let projections: Vec<_> = functions.iter().filter(|f| f.size == 2).collect();
    println!("Projections (size=2): {}", projections.len());

    // Check for symmetric functions (invariant under variable permutation)
    let half_minterms = 1usize << (args.n - 1);
    let balanced: Vec<_> = functions.iter().filter(|f| f.minterm_count == half_minterms).collect();
    println!("Balanced (exactly 2^(n-1) minterms): {}", balanced.len());

    // Size distribution summary
    println!("\n── Size Distribution Summary ──");
    let mut size_counts: HashMap<usize, usize> = HashMap::new();
    for func in &functions {
        *size_counts.entry(func.size).or_insert(0) += 1;
    }

    let mut size_list: Vec<_> = size_counts.iter().collect();
    size_list.sort_by_key(|(&s, _)| s);

    for (size, count) in size_list {
        let pct = 100.0 * *count as f64 / functions.len() as f64;
        let bar_len = (pct * 0.3) as usize;
        println!("  Size {:>2}: {:>6} ({:>5.2}%) {}", size, count, pct, "█".repeat(bar_len));
    }

    // Assert some invariants
    assert!(!functions.is_empty(), "expected at least one function");
    // With exhaustive enumeration, we should find exactly 2 constants
    if args.exhaustive && args.n <= 4 {
        assert_eq!(constants.len(), 2, "expected exactly 2 constants (0 and 1)");
    }

    println!("\nDone.");

    Ok(())
}

fn print_function_info(_bdd: &Bdd, n: usize, func: &FunctionInfo, index: usize) {
    println!("  Function #{}", index);
    println!("    BDD Size:    {}", func.size);
    println!("    Minterms:    {} / {}", func.minterm_count, 1 << n);

    // Print truth table in hex for compact representation
    let hex = format!("{:x}", func.truth_table.bits);
    if hex.len() <= 16 {
        println!("    Truth table: 0x{}", hex);
    } else {
        println!("    Truth table: 0x{}...", &hex[..16]);
    }

    // Print as binary for small functions
    if n <= 4 {
        let binary: String = (0..(1 << n)).map(|i| if func.truth_table.eval(i) { '1' } else { '0' }).collect();
        println!("    Binary:      {}", binary);
    }

    // Try to identify special structure
    let properties = identify_properties(&func.truth_table, n);
    if !properties.is_empty() {
        println!("    Properties:  {}", properties.join(", "));
    }

    println!();
}

fn identify_properties(tt: &TruthTable, n: usize) -> Vec<String> {
    let mut props = Vec::new();

    // Check if constant
    if tt.is_zero() {
        props.push("constant 0".to_string());
        return props;
    }
    if tt.is_one() {
        props.push("constant 1".to_string());
        return props;
    }

    // Check if single variable or its negation
    for v in 1..=n {
        let proj = TruthTable::projection(n, v);
        if tt.bits == proj.bits {
            props.push(format!("x{}", v));
            return props;
        }
        if tt.bits == proj.complement().bits {
            props.push(format!("¬x{}", v));
            return props;
        }
    }

    // Check if balanced
    let half = 1usize << (n - 1);
    if tt.count_ones() == half {
        props.push("balanced".to_string());
    }

    // Check monotone (increasing)
    let is_monotone = (0..(1 << n)).all(|i| {
        if !tt.eval(i) {
            true
        } else {
            // All supersets must also be true
            (0..n).all(|bit| {
                let superset = i | (1 << bit);
                superset >= (1 << n) || tt.eval(superset)
            })
        }
    });
    if is_monotone && !tt.is_zero() {
        props.push("monotone".to_string());
    }

    // Check symmetric (depends only on Hamming weight)
    let is_symmetric = {
        let by_weight: Vec<_> = (0..=n)
            .map(|w| {
                let first_input = (0..(1 << n)).find(|&i| (i as usize).count_ones() as usize == w);
                first_input.map(|i| tt.eval(i))
            })
            .collect();

        (0..(1 << n)).all(|i| {
            let w = (i as usize).count_ones() as usize;
            by_weight[w] == Some(tt.eval(i))
        })
    };
    if is_symmetric {
        props.push("symmetric".to_string());
    }

    props
}
