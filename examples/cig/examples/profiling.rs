//! Performance profiling example for CIG separability analysis.
//!
//! This example generates and analyzes Boolean functions to profile
//! the separability testing and interaction partition algorithms.
//!
//! Run with:
//! ```bash
//! cargo run --release --example profiling --package cig -- --help
//! cargo run --release --example profiling --package cig -- --vars 5 --samples 500000
//! cargo run --release --example profiling --package cig -- --vars 6 --extensive
//! ```
//!
//! Use `release` mode for accurate timing measurements!

use std::time::Instant;

use cig::separability::{find_interaction_partition, test_separability};
use cig::truth_table::TruthTable;
use cig::variable::{Var, VarSet};
use clap::Parser;

#[derive(Parser, Debug)]
#[command(name = "CIG Profiling")]
#[command(about = "Profile CIG separability and partition finding algorithms", long_about = None)]
struct Args {
    /// Number of variables (4-6)
    #[arg(short = 'n', long, default_value = "5")]
    vars: u32,

    /// Number of functions to sample
    #[arg(short, long)]
    samples: Option<usize>,

    /// Perform extensive analysis (deep cofactor testing)
    #[arg(long)]
    extensive: bool,

    /// Profile constructed functions instead of enumerated ones
    #[arg(long)]
    constructed: bool,

    /// Skip interaction partition finding (test only separability)
    #[arg(long)]
    skip_partition: bool,
}

fn main() {
    let args = Args::parse();

    println!("═══════════════════════════════════════════════════════════");
    println!("CIG Separability Performance Profiling");
    println!("═══════════════════════════════════════════════════════════\n");

    if args.constructed {
        println!("Profile: Complex constructed functions\n");
        profile_constructed_functions();
    } else {
        let samples = args.samples.unwrap_or_else(|| match args.vars {
            4 => 65_536,
            5 => 500_000,
            6 => 100_000,
            _ => 50_000,
        });

        if args.extensive {
            println!("Profile: EXTENSIVE analysis of {} {}-variable functions\n", samples, args.vars);
            profile_functions_extensive(args.vars, samples);
        } else {
            println!("Profile: Quick analysis of {} {}-variable functions\n", samples, args.vars);
            profile_functions_quick(args.vars, samples, args.skip_partition);
        }
    }
}

fn profile_functions_quick(n: u32, samples: usize, skip_partition: bool) {
    let max_functions = 1usize << (1usize << n);
    let actual_samples = std::cmp::min(samples, max_functions);

    println!(
        "Total possible functions: 2^(2^{}) = {}",
        n,
        if max_functions > 1_000_000 {
            format!("{:.2}B", max_functions as f64 / 1e9)
        } else {
            format!("{}", max_functions)
        }
    );
    println!("Sampling: {}\n", actual_samples);

    let mut separable_count = 0usize;
    let mut irreducible_count = 0usize;
    let mut avg_blocks = 0.0f64;
    let mut partition_time = 0.0f64;
    let mut separability_time = 0.0f64;

    let start = Instant::now();

    for i in 0..actual_samples {
        if i % (std::cmp::max(actual_samples / 10, 1)) == 0 && i > 0 {
            let elapsed = start.elapsed().as_secs_f64();
            let rate = i as f64 / elapsed;
            let remaining = (actual_samples - i) as f64 / rate;
            println!(
                "[{:7}/{:7}] {:.2}s elapsed | {:.0} funcs/sec | ~{:.1}s remaining",
                i, actual_samples, elapsed, rate, remaining
            );
        }

        let f = function_from_index(i as u32, n);

        // Partition finding (compute once)
        let s = Instant::now();
        let ip = find_interaction_partition(&f);
        partition_time += s.elapsed().as_secs_f64();

        let all_vars = ip.variables(); // Get vars from partition, not from function
        let num_blocks = ip.num_blocks();
        if num_blocks == 1 {
            irreducible_count += 1;
        }
        avg_blocks += num_blocks as f64;

        // Quick separability check (only if not skipped)
        if !skip_partition && all_vars.len() >= 2 {
            let vars_vec: Vec<Var> = all_vars.iter().collect();
            let split = vars_vec.len() / 2;
            let a_vars: VarSet = vars_vec[..split].iter().copied().collect();
            let b_vars: VarSet = vars_vec[split..].iter().copied().collect();

            let s = Instant::now();
            let result = test_separability(&f, &a_vars, &b_vars);
            separability_time += s.elapsed().as_secs_f64();

            if result.is_separable {
                separable_count += 1;
            }
        }
    }

    let total_elapsed = start.elapsed();

    println!("\n[Summary]");
    println!("  Total analyzed:      {}", actual_samples);
    println!("  Time elapsed:        {:.3}s", total_elapsed.as_secs_f64());
    println!(
        "  Rate:                {:.0} functions/sec",
        actual_samples as f64 / total_elapsed.as_secs_f64()
    );
    println!(
        "  Separable (first partition): {} ({:.2}%)",
        separable_count,
        100.0 * separable_count as f64 / actual_samples as f64
    );

    if !skip_partition {
        println!(
            "  Irreducible:         {} ({:.2}%)",
            irreducible_count,
            100.0 * irreducible_count as f64 / actual_samples as f64
        );
        println!("  Avg partition blocks: {:.3}", avg_blocks / actual_samples as f64);
        println!("\n[Timing Breakdown]");
        println!(
            "  Separability tests:  {:.3}s ({:.1}%)",
            separability_time,
            100.0 * separability_time / total_elapsed.as_secs_f64()
        );
        println!(
            "  Partition finding:   {:.3}s ({:.1}%)",
            partition_time,
            100.0 * partition_time / total_elapsed.as_secs_f64()
        );
    } else {
        println!("\n[Timing]");
        println!("  Separability tests:  {:.3}s", separability_time);
    }

    println!("\n─────────────────────────────────────────────────────────");
}

fn profile_functions_extensive(n: u32, samples: usize) {
    let max_functions = 1usize << (1usize << n);
    let actual_samples = std::cmp::min(samples, max_functions);

    println!(
        "Total possible functions: 2^(2^{}) = {}",
        n,
        if max_functions > 1_000_000 {
            format!("{:.2}B", max_functions as f64 / 1e9)
        } else {
            format!("{}", max_functions)
        }
    );
    println!("Sampling: {} (EXTENSIVE mode - deep cofactor analysis)\n", actual_samples);

    let mut stats = PartitionStats::default();
    let mut separability_stats = SeparabilityStats::default();
    let mut operator_consistency = [0usize; 3]; // AND, OR, XOR

    let start = Instant::now();

    let mut generated = 0;
    for i in 0..actual_samples * 10 {
        // Skip constant functions
        if i % (std::cmp::max(actual_samples / 2, 1)) == 0 && generated > 0 {
            let elapsed = start.elapsed().as_secs_f64();
            let rate = generated as f64 / elapsed;
            let remaining = (actual_samples - generated) as f64 / rate;
            println!(
                "[{:7}/{:7}] {:5.1}s | {:.0} funcs/sec | ~{:.1}s remaining",
                generated, actual_samples, elapsed, rate, remaining
            );
        }

        let f = function_from_index(i as u32, n);

        // Find partition
        let ip = find_interaction_partition(&f);
        let all_vars = ip.variables();

        // Skip constant functions (0 variables)
        if all_vars.is_empty() {
            continue;
        }

        generated += 1;
        let num_blocks = ip.num_blocks();

        stats.total += 1;
        stats.block_distribution[std::cmp::min(num_blocks, 6)] += 1;
        stats.sum_blocks += num_blocks as f64;

        if num_blocks == 1 {
            stats.irreducible += 1;
        } else if num_blocks == all_vars.len() {
            stats.fully_separable += 1;
        }

        // Test all pairwise partitions
        if all_vars.len() >= 2 {
            let vars_vec: Vec<Var> = all_vars.iter().collect();

            for split in 1..vars_vec.len() {
                let a_vars: VarSet = vars_vec[..split].iter().copied().collect();
                let b_vars: VarSet = vars_vec[split..].iter().copied().collect();

                let result = test_separability(&f, &a_vars, &b_vars);
                if result.is_separable {
                    separability_stats.total_tests += 1;
                    separability_stats.separable_count += 1;

                    if let Some(op) = result.operator {
                        match op {
                            cig::separability::Operator::And => operator_consistency[0] += 1,
                            cig::separability::Operator::Or => operator_consistency[1] += 1,
                            cig::separability::Operator::Xor => operator_consistency[2] += 1,
                        }
                    }
                } else {
                    separability_stats.total_tests += 1;
                }
            }
        }

        if generated >= actual_samples {
            break;
        }
    }

    let total_elapsed = start.elapsed();

    println!("\n[Overall Statistics]");
    println!("  Functions analyzed: {}", stats.total);
    println!("  Time elapsed:       {:.3}s", total_elapsed.as_secs_f64());
    println!(
        "  Rate:               {:.0} functions/sec",
        stats.total as f64 / total_elapsed.as_secs_f64()
    );

    println!("\n[Partition Distribution]");
    println!(
        "  Fully separable:    {} ({:.2}%)",
        stats.fully_separable,
        100.0 * stats.fully_separable as f64 / stats.total as f64
    );
    println!(
        "  Irreducible (1 block): {} ({:.2}%)",
        stats.irreducible,
        100.0 * stats.irreducible as f64 / stats.total as f64
    );
    println!("  Average blocks:     {:.3}", stats.sum_blocks / stats.total as f64);
    println!("\n  Block count distribution:");
    for (blocks, count) in stats.block_distribution.iter().enumerate() {
        if *count > 0 {
            let label = if blocks == 6 { "6+".to_string() } else { blocks.to_string() };
            println!(
                "    {} blocks: {:7} ({:.2}%)",
                label,
                count,
                100.0 * *count as f64 / stats.total as f64
            );
        }
    }

    println!("\n[Separability Analysis]");
    println!("  Total partition tests: {}", separability_stats.total_tests);
    println!(
        "  Separable partitions:  {} ({:.2}%)",
        separability_stats.separable_count,
        100.0 * separability_stats.separable_count as f64 / separability_stats.total_tests as f64
    );

    println!("\n  Separable by operator:");
    println!("    AND: {}", operator_consistency[0]);
    println!("    OR:  {}", operator_consistency[1]);
    println!("    XOR: {}", operator_consistency[2]);

    println!("\n─────────────────────────────────────────────────────────");
}

#[derive(Default)]
struct PartitionStats {
    total: usize,
    irreducible: usize,
    fully_separable: usize,
    sum_blocks: f64,
    block_distribution: [usize; 7], // 0-6+ blocks
}

#[derive(Default)]
struct SeparabilityStats {
    total_tests: usize,
    separable_count: usize,
}

fn profile_constructed_functions() {
    let functions: Vec<(&str, u32, fn(&[bool]) -> bool)> = vec![
        ("3-bit parity", 3, |x: &[bool]| x.iter().fold(false, |a, &b| a ^ b)),
        ("4-bit parity", 4, |x: &[bool]| x.iter().fold(false, |a, &b| a ^ b)),
        ("3-bit majority", 3, parity_3bit_maj),
        ("4-bit majority", 4, parity_4bit_maj),
        ("3x3 multiplier", 6, multiplier_product),
        ("Full adder sum", 3, adder_sum),
        ("Full adder carry", 3, adder_carry),
        ("Mux 2-bit sel", 6, mux_2bit),
        ("Complex composed", 4, complex_composed),
    ];

    println!("{:25} | vars | blocks | time (µs) | rate (k/s)", "Function");
    println!("{:-<25}-+------+--------+-----------+-----------", "");

    for (name, n, func) in functions {
        let f = TruthTable::from_expr(n, func);

        let start = Instant::now();
        let ip = find_interaction_partition(&f);
        let elapsed = start.elapsed();

        let all_vars = ip.variables(); // Get from partition, not from function
        let essential_vars = all_vars.len();
        let blocks = ip.num_blocks();
        let micros = elapsed.as_secs_f64() * 1_000_000.0;
        let rate = 1.0 / elapsed.as_secs_f64() / 1000.0;

        println!("{:25} | {:4} | {:6} | {:9.1} | {:9.1}", name, essential_vars, blocks, micros, rate);
    }

    println!("\n─────────────────────────────────────────────────────────\n");
}

// Constructed function helpers
fn parity_3bit_maj(x: &[bool]) -> bool {
    let ones = x.iter().filter(|&&b| b).count();
    ones >= 2
}

fn parity_4bit_maj(x: &[bool]) -> bool {
    let ones = x.iter().filter(|&&b| b).count();
    ones >= 2
}

fn multiplier_product(x: &[bool]) -> bool {
    let p1 = x[0] && x[1];
    let p2 = x[2] && x[3] && x[4];
    p1 ^ p2 ^ x[5]
}

fn adder_sum(x: &[bool]) -> bool {
    x[0] ^ x[1] ^ x[2]
}

fn adder_carry(x: &[bool]) -> bool {
    (x[0] && x[1]) || (x[0] && x[2]) || (x[1] && x[2])
}

fn mux_2bit(x: &[bool]) -> bool {
    let sel = (x[4] as usize) | ((x[5] as usize) << 1);
    x[sel]
}

fn complex_composed(x: &[bool]) -> bool {
    let p1 = (x[0] && x[1]) ^ (x[2] && x[3]);
    let p2 = x[0] ^ x[2];
    p1 || p2
}

/// Generate the i-th Boolean function of n variables using formula-based approach.
/// Each index maps to a deterministic but varied formula.
fn function_from_index(idx: u32, n: u32) -> TruthTable {
    let formula_id = idx % 8; // 8 different formula types

    TruthTable::from_expr(n, move |x| {
        // Mix indexing with various formulas to get diverse functions
        let x_val = x.iter().enumerate().fold(0u32, |acc, (i, &b)| acc | ((b as u32) << i));
        let mixed = x_val.wrapping_mul(idx.wrapping_add(1)).wrapping_add(formula_id as u32);

        match formula_id {
            0 => mixed & 1 == 1,                            // Parity-like
            1 => mixed.count_ones() > n / 2,                // Majority-like
            2 => (mixed ^ idx) & 1 == 1,                    // XOR variant
            3 => (x_val & (idx as u32)) != 0,               // AND-based
            4 => (x_val | (idx as u32)) == (1u32 << n) - 1, // OR-based
            5 => mixed.wrapping_add(idx) & 1 == 1,          // Shifted parity
            6 => (mixed >> (idx % n)) & 1 == 1,             // Rotation
            _ => (mixed ^ (mixed >> 1)) & 1 == 1,           // Gray code
        }
    })
}
