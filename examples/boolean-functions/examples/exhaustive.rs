//! Exhaustive enumeration of Boolean functions for small n.
//!
//! This example demonstrates exhaustive analysis of all 2^(2^n) Boolean functions
//! for small values of n (typically n ≤ 4).
//!
//! Run with: `cargo run -p boolean-functions --example exhaustive -- -n 3`

use boolean_functions::analysis::{bounds, VariableSummary};
use boolean_functions::function::TruthTable;
use boolean_functions::viz::{render_density, render_histogram, render_statistics, HistogramConfig};
use clap::Parser;

#[derive(Parser, Debug)]
#[command(name = "exhaustive")]
#[command(about = "Exhaustive enumeration of Boolean functions")]
struct Args {
    /// Number of variables (recommended: 2-4)
    #[arg(short, long, default_value_t = 3)]
    n: usize,

    /// Show individual function details
    #[arg(short, long)]
    verbose: bool,
}

fn main() -> color_eyre::Result<()> {
    color_eyre::install()?;

    let args = Args::parse();
    let n = args.n;

    println!("─── Exhaustive Boolean Function Enumeration ───\n");

    // Warn if n is too large
    let total = TruthTable::total_count(n);
    println!("Variables:        n = {}", n);
    println!("Total functions:  2^(2^{}) = {}", n, total);

    if n > 4 {
        println!("\nWarning: n > 4 will take a very long time!");
        println!("   n=5 has 4,294,967,296 functions.");
        println!("   Consider using Monte Carlo sampling instead.\n");
    }

    if n > 5 {
        println!("Aborting: n = {} is too large for exhaustive enumeration.", n);
        println!("   Use --example monte_carlo instead.");
        return Ok(());
    }

    println!("\nEnumerating all functions...\n");

    // Perform exhaustive enumeration
    let summary = VariableSummary::exhaustive(n);

    // Assert expected properties
    assert_eq!(summary.distribution.total as u64, total.try_into().unwrap_or(u64::MAX));
    // Size 1 = constants (terminal only), should have exactly 2 (0 and 1)
    assert_eq!(summary.distribution.count(1), 2, "should have exactly 2 constants (0 and 1)");

    // Print summary
    println!("{}", summary.summary_table());

    // Print statistics table
    println!("\n{}", render_statistics(&summary.stats, &format!("BDD Size Statistics (n={})", n)));

    // Print histogram
    let sizes: Vec<usize> = summary
        .distribution
        .sorted_counts()
        .iter()
        .flat_map(|(s, c)| std::iter::repeat(*s).take(*c))
        .collect();

    println!(
        "\n{}",
        render_histogram(
            &sizes,
            &HistogramConfig {
                height: 12,
                bins: 15,
                ..Default::default()
            }
        )
    );

    // Print density
    println!("\n{}", render_density(&summary.distribution, 60));

    // Theoretical analysis
    println!("\n─── Theoretical Bounds ───");
    println!("Maximum possible BDD size: {}", bounds::max_size(n));
    println!("Expected size (Shannon):   {:.2}", bounds::expected_size(n));
    println!("Observed mean:             {:.2}", summary.stats.mean);
    println!("Observed median:           {:.0}", summary.stats.median);

    // Detailed breakdown by size
    if args.verbose {
        println!("\n─── Detailed Size Breakdown ───");
        for (size, count) in summary.distribution.sorted_counts() {
            let pct = 100.0 * count as f64 / summary.distribution.total as f64;
            println!("  Size {:>2}: {:>6} functions ({:>5.2}%)", size, count, pct);
        }
    }

    // BDD size includes terminal, so:
    // Size 1 = constants (0 and 1), Size 2 = projections
    println!("\n─── Special Functions ───");
    println!("Size 1 (constants):   {} functions", summary.distribution.count(1));
    println!("Size 2 (projections): {} functions", summary.distribution.count(2));

    // Compare across multiple n
    if n <= 4 {
        println!("\n─── Comparison Across n ───\n");
        println!("  n   Total funcs       Mean        Max      %% size=1");
        println!("────  ─────────────  ──────────  ──────────  ─────────");

        for i in 1..=n {
            let s = VariableSummary::exhaustive(i);
            // Size 1 = constants (terminal only)
            let pct_const = 100.0 * s.distribution.count(1) as f64 / s.distribution.total as f64;
            println!(
                "{:>3}   {:>13}   {:>10.2}  {:>10.0}  {:>8.4}%",
                i,
                TruthTable::total_count(i),
                s.stats.mean,
                s.stats.max,
                pct_const
            );
        }
    }

    println!("\nDone.");

    Ok(())
}
