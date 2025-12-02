//! Monte Carlo sampling of Boolean functions.
//!
//! This example demonstrates statistical sampling when exhaustive enumeration
//! is infeasible. It provides confidence intervals using multiple methods.
//!
//! Run with: `cargo run -p boolean-functions --example monte_carlo -- -n 5 -s 10000`

use boolean_functions::function::TruthTable;
use boolean_functions::sampling::{MonteCarloSampler, SamplingConfig};
use boolean_functions::stats::{chebyshev_mean_bound, hoeffding_sample_size};
use boolean_functions::viz::{render_histogram, render_statistics, HistogramConfig};
use clap::Parser;
use rand::SeedableRng;
use rand_chacha::ChaCha8Rng;

#[derive(Parser, Debug)]
#[command(name = "monte_carlo")]
#[command(about = "Monte Carlo sampling of Boolean functions")]
struct Args {
    /// Number of variables
    #[arg(short, long, default_value_t = 5)]
    n: usize,

    /// Number of samples
    #[arg(short, long, default_value_t = 10000)]
    samples: usize,

    /// Confidence level (e.g., 0.95 for 95%)
    #[arg(short, long, default_value_t = 0.95)]
    confidence: f64,

    /// Random seed (optional)
    #[arg(long)]
    seed: Option<u64>,

    /// Number of bootstrap resamples
    #[arg(short, long, default_value_t = 1000)]
    bootstrap: usize,
}

fn main() -> color_eyre::Result<()> {
    color_eyre::install()?;

    let args = Args::parse();

    println!("─── Monte Carlo Sampling of Boolean Functions ───\n");

    let total = TruthTable::total_count(args.n);
    println!("Variables:        n = {}", args.n);
    if args.n <= 5 {
        println!("Total functions:  2^(2^{}) = {}", args.n, total);
    } else {
        println!("Total functions:  2^(2^{}) = 10^{}", args.n, total.to_string().len() - 1);
    }
    println!(
        "Sample size:      {} ({:.2e}% of total)",
        args.samples,
        100.0 * args.samples as f64 / total.to_string().parse::<f64>().unwrap_or(f64::INFINITY)
    );
    println!("Confidence level: {:.0}%", args.confidence * 100.0);
    println!();

    // Setup RNG
    let mut rng = match args.seed {
        Some(s) => {
            println!("Random seed:      {}", s);
            ChaCha8Rng::seed_from_u64(s)
        }
        None => {
            let seed = rand::random();
            println!("Random seed:      {} (auto-generated)", seed);
            ChaCha8Rng::seed_from_u64(seed)
        }
    };
    println!();

    // Configure sampling
    let config = SamplingConfig::new(args.n, args.samples)
        .with_confidence(args.confidence)
        .with_bootstrap(args.bootstrap);

    println!("Sampling {} random Boolean functions...\n", args.samples);

    // Run sampling
    let sampler = MonteCarloSampler::new(config);
    let result = sampler.sample(&mut rng);

    // Print results
    println!("{}", result.summary());

    // Detailed statistics
    println!("\n{}", render_statistics(&result.stats, "Sample Statistics"));

    // Histogram
    println!(
        "\n{}",
        render_histogram(
            &result.sizes,
            &HistogramConfig {
                height: 15,
                bins: 25,
                ..Default::default()
            }
        )
    );

    // Confidence interval comparison
    println!("\n─── Confidence Interval Methods ───\n");
    println!("Method             Lower         Upper         Width");
    println!("───────────────  ───────────   ───────────   ─────────────");
    println!(
        "CLT              {:>11.4}   {:>11.4}   {:>13.4}",
        result.clt_ci.lower,
        result.clt_ci.upper,
        result.clt_ci.width()
    );
    println!(
        "t-distribution   {:>11.4}   {:>11.4}   {:>13.4}",
        result.t_ci.lower,
        result.t_ci.upper,
        result.t_ci.width()
    );
    if let Some(ref boot) = result.bootstrap {
        println!(
            "Bootstrap        {:>11.4}   {:>11.4}   {:>13.4}",
            boot.percentile_ci.lower,
            boot.percentile_ci.upper,
            boot.percentile_ci.width()
        );
    }

    // Assert confidence interval contains sample mean
    assert!(
        result.clt_ci.lower <= result.stats.mean && result.stats.mean <= result.clt_ci.upper,
        "CLT CI should contain sample mean"
    );
    assert!(
        result.t_ci.lower <= result.stats.mean && result.stats.mean <= result.t_ci.upper,
        "t-distribution CI should contain sample mean"
    );

    // Tail bounds
    println!("\n── Tail Bounds (Chebyshev) ──");
    for k in [2.0, 3.0, 4.0] {
        let bound = chebyshev_mean_bound(&result.stats, k);
        println!(
            "  P(|X̄ - μ| ≥ {:.1}σ) ≤ {:.4}  (threshold: {:.2})",
            k,
            1.0 / (k * k),
            bound.threshold
        );
    }

    // Sample size analysis
    println!("\n── Sample Size Requirements (Hoeffding) ──");
    let max_size = result.stats.max as f64;
    let range = max_size; // Assuming min is 0

    for &epsilon in &[0.1, 0.05, 0.01] {
        for &delta in &[0.05, 0.01] {
            let n_required = hoeffding_sample_size(epsilon * result.stats.mean, delta, range);
            println!(
                "  For ε = {:.0}% of mean, δ = {:.0}%: n ≥ {}",
                epsilon * 100.0,
                delta * 100.0,
                n_required
            );
        }
    }

    // Size distribution summary
    println!("\n── Size Distribution ──");
    let dist = &result.size_distribution;
    if dist.len() <= 15 {
        for (size, count) in dist {
            let pct = 100.0 * *count as f64 / result.sizes.len() as f64;
            let bar_len = (pct * 0.5) as usize;
            println!("  {:>3}: {:>5} ({:>5.2}%) {}", size, count, pct, "█".repeat(bar_len));
        }
    } else {
        println!("  (showing summary for {} distinct sizes)", dist.len());
        let total_unique = dist.len();
        let top_5: Vec<_> = {
            let mut sorted = dist.clone();
            sorted.sort_by(|a, b| b.1.cmp(&a.1));
            sorted.into_iter().take(5).collect()
        };
        println!("  Most common sizes:");
        for (size, count) in top_5 {
            let pct = 100.0 * count as f64 / result.sizes.len() as f64;
            println!("    Size {:>3}: {:>5} ({:>5.2}%)", size, count, pct);
        }
        println!("  Total distinct sizes: {}", total_unique);
    }

    // Interpretation
    println!("\n─── Interpretation ───");
    println!("The sample mean {:.2} estimates the true population mean.", result.stats.mean);
    println!(
        "With {:.0}% confidence, the true mean lies in [{:.2}, {:.2}].",
        args.confidence * 100.0,
        result.t_ci.lower,
        result.t_ci.upper
    );
    println!("The standard error {:.4} measures estimation precision.", result.stats.std_error);
    println!(
        "Relative error: +/-{:.2}% of the mean.",
        100.0 * result.stats.std_error / result.stats.mean
    );

    println!("\nDone.");

    Ok(())
}
