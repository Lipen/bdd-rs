//! Statistical analysis demonstration.
//!
//! This example demonstrates the statistical methods for analyzing
//! BDD size distributions, including confidence intervals, tail bounds,
//! and bootstrap resampling.
//!
//! Run with: `cargo run -p boolean-functions --example statistics`

use bdd_rs::bdd::Bdd;
use boolean_functions::function::random_function_with_bdd;
use boolean_functions::stats::{
    bootstrap, chebyshev_bound, chebyshev_mean_bound, clt_confidence_interval, empirical_tail_bound, hoeffding_bound,
    hoeffding_sample_size, iqr, quantiles, t_confidence_interval, Statistics,
};
use clap::Parser;
use rand::SeedableRng;
use rand_chacha::ChaCha8Rng;
use std::collections::BTreeMap;

#[derive(Parser, Debug)]
#[command(name = "statistics")]
#[command(about = "Demonstrate statistical analysis methods")]
struct Args {
    /// Number of variables
    #[arg(short, long, default_value_t = 4)]
    n: usize,

    /// Number of samples
    #[arg(short, long, default_value_t = 5000)]
    samples: usize,

    /// Random seed
    #[arg(long, default_value_t = 42)]
    seed: u64,

    /// Verbose output with additional details
    #[arg(short, long)]
    verbose: bool,
}

/// Compute skewness (third standardized moment).
fn skewness(sample: &[f64], stats: &Statistics) -> f64 {
    if stats.std_dev == 0.0 {
        return 0.0;
    }
    let n = sample.len() as f64;
    let m3 = sample.iter().map(|x| (x - stats.mean).powi(3)).sum::<f64>() / n;
    m3 / stats.std_dev.powi(3)
}

/// Compute excess kurtosis (fourth standardized moment minus 3).
fn kurtosis(sample: &[f64], stats: &Statistics) -> f64 {
    if stats.std_dev == 0.0 {
        return 0.0;
    }
    let n = sample.len() as f64;
    let m4 = sample.iter().map(|x| (x - stats.mean).powi(4)).sum::<f64>() / n;
    m4 / stats.std_dev.powi(4) - 3.0
}

/// Print a simple ASCII histogram.
fn print_histogram(counts: &BTreeMap<usize, usize>, max_width: usize) {
    let max_count = *counts.values().max().unwrap_or(&1);
    let total: usize = counts.values().sum();

    for (&size, &count) in counts {
        let bar_len = (count * max_width) / max_count;
        let pct = 100.0 * count as f64 / total as f64;
        println!("  {:>3} | {:5.1}% | {}", size, pct, "█".repeat(bar_len));
    }
}

fn main() -> color_eyre::Result<()> {
    color_eyre::install()?;

    let args = Args::parse();

    println!("─── Statistical Analysis of BDD Size Distribution ───\n");

    println!("Parameters:");
    println!("  Variables:    n = {}", args.n);
    println!("  Sample size:  {}", args.samples);
    println!("  Random seed:  {}", args.seed);
    println!();

    // Generate samples
    let bdd = Bdd::default();
    let mut rng = ChaCha8Rng::seed_from_u64(args.seed);

    println!("Generating {} random Boolean functions...", args.samples);

    let sizes: Vec<usize> = (0..args.samples)
        .map(|_| random_function_with_bdd(&bdd, args.n, &mut rng).size)
        .collect();

    // Build frequency distribution
    let mut counts: BTreeMap<usize, usize> = BTreeMap::new();
    for &s in &sizes {
        *counts.entry(s).or_insert(0) += 1;
    }

    let float_sizes: Vec<f64> = sizes.iter().map(|&s| s as f64).collect();
    let stats = Statistics::from_sample(&float_sizes);

    println!("Done.\n");

    // 1. Distribution overview
    println!("─── 1. Distribution Overview ───\n");

    println!("Size  | Freq   | Distribution");
    println!("──────┼────────┼─────────────────────────────────────────");
    print_histogram(&counts, 40);

    // Mode calculation
    let mode = counts.iter().max_by_key(|(_, &c)| c).map(|(&s, _)| s).unwrap();
    println!();
    println!("Mode: {} (most frequent size)", mode);

    // 2. Descriptive statistics
    println!("\n─── 2. Descriptive Statistics ───\n");

    println!("Central Tendency:");
    println!("  Mean (x̄):       {:.4}", stats.mean);
    println!("  Median:         {:.1}", stats.median);
    println!("  Mode:           {}", mode);

    println!("\nDispersion:");
    println!("  Variance (s²):  {:.4}", stats.variance);
    println!("  Std dev (s):    {:.4}", stats.std_dev);
    println!("  Range:          [{:.0}, {:.0}]", stats.min, stats.max);
    println!("  IQR:            {:.1}", iqr(&float_sizes));

    let cv = stats.std_dev / stats.mean * 100.0;
    println!("  CV:             {:.2}%  (coefficient of variation)", cv);

    let skew = skewness(&float_sizes, &stats);
    let kurt = kurtosis(&float_sizes, &stats);
    println!("\nShape:");
    println!("  Skewness:       {:.4}  {}", skew, skew_interpretation(skew));
    println!("  Excess Kurt.:   {:.4}  {}", kurt, kurt_interpretation(kurt));

    println!("\nPrecision:");
    println!("  Std error (SE): {:.4}  (s / sqrt(n))", stats.std_error);
    println!("  Rel. SE:        {:.4}%  (SE / mean)", stats.std_error / stats.mean * 100.0);

    // Quantiles
    if args.verbose {
        let qs = quantiles(&float_sizes, &[0.05, 0.10, 0.25, 0.50, 0.75, 0.90, 0.95]);
        println!("\nQuantiles:");
        println!("   5%: {:.0}     10%: {:.0}     25%: {:.0} (Q1)", qs[0], qs[1], qs[2]);
        println!("  50%: {:.0} (median)", qs[3]);
        println!("  75%: {:.0} (Q3)   90%: {:.0}     95%: {:.0}", qs[4], qs[5], qs[6]);
    }

    // 3. Confidence intervals
    println!("\n─── 3. Confidence Intervals for the Mean ───\n");

    println!("Goal: Estimate the true population mean μ from our sample.\n");

    println!("Level    CLT Interval            t-dist Interval         Width");
    println!("───────  ──────────────────────  ──────────────────────  ─────────");

    for &conf in &[0.90, 0.95, 0.99] {
        let clt = clt_confidence_interval(&stats, conf);
        let t = t_confidence_interval(&stats, conf);

        println!(
            "{:>5.0}%   [{:>7.4}, {:>7.4}]    [{:>7.4}, {:>7.4}]     {:.4}",
            conf * 100.0,
            clt.lower,
            clt.upper,
            t.lower,
            t.upper,
            t.width()
        );
    }

    println!();
    println!("Note: CLT uses Normal distribution; t-distribution is more");
    println!("      conservative for smaller samples. Both converge as n→∞.");

    // 4. Bootstrap
    println!("\n─── 4. Bootstrap Resampling ───\n");

    println!("Bootstrap constructs an empirical sampling distribution by");
    println!("resampling with replacement from the observed data.\n");

    let num_resamples = 10000;
    println!("Performing {} bootstrap resamples...", num_resamples);

    let boot = bootstrap(&float_sizes, num_resamples, 0.95, &mut rng);

    println!();
    println!("Bootstrap estimate of the mean:  {:.4}", boot.mean);
    println!("Bootstrap standard error:        {:.4}", boot.std_error);
    println!(
        "95% Percentile CI:               [{:.4}, {:.4}]",
        boot.percentile_ci.lower, boot.percentile_ci.upper
    );

    println!("\nComparison with analytical methods:");
    println!("                    Analytical    Bootstrap    Difference");
    println!(
        "  Mean              {:>10.4}   {:>10.4}    {:>+.4}",
        stats.mean,
        boot.mean,
        boot.mean - stats.mean
    );
    println!(
        "  Std Error         {:>10.4}   {:>10.4}    {:>+.4}",
        stats.std_error,
        boot.std_error,
        boot.std_error - stats.std_error
    );

    let t_ci = t_confidence_interval(&stats, 0.95);
    println!(
        "  95% CI width      {:>10.4}   {:>10.4}    {:>+.4}",
        t_ci.width(),
        boot.percentile_ci.width(),
        boot.percentile_ci.width() - t_ci.width()
    );

    // Assert bootstrap is reasonable
    assert!(
        (boot.mean - stats.mean).abs() / stats.mean < 0.01,
        "bootstrap mean should be close to sample mean"
    );

    // 5. Tail bounds
    println!("\n─── 5. Concentration Inequalities ───\n");

    println!("Chebyshev's inequality: P(|X - μ| ≥ k·σ) ≤ 1/k²\n");
    println!("This is distribution-free but often loose.\n");

    println!("    k     Threshold   Chebyshev Bound   Empirical Prob");
    println!("  ─────   ─────────   ───────────────   ──────────────");

    for k in [1.5, 2.0, 2.5, 3.0, 4.0] {
        let _cheb = chebyshev_bound(&stats, k);
        let threshold = stats.mean + k * stats.std_dev;
        let emp = empirical_tail_bound(&float_sizes, threshold);
        let cheb_bound = 1.0 / (k * k);

        let ratio = if emp.upper_prob > 0.0 {
            cheb_bound / emp.upper_prob
        } else {
            f64::INFINITY
        };

        println!(
            "  {:>5.1}   {:>9.2}   {:>15.4}   {:>14.4}  (bound is {:.0}× actual)",
            k, threshold, cheb_bound, emp.upper_prob, ratio
        );
    }

    println!();
    println!("Chebyshev bound for the sample mean (uses SE instead of σ):");

    for k in [2.0, 3.0, 4.0] {
        let bound = chebyshev_mean_bound(&stats, k);
        println!(
            "  P(|X̄ - μ| ≥ {:.1}·SE) ≤ {:.4}  (deviation ≥ {:.4})",
            k,
            1.0 / (k * k),
            bound.threshold - stats.mean
        );
    }

    // 6. Hoeffding bounds
    println!("\n─── 6. Hoeffding Bounds ───\n");

    let range = stats.max - stats.min;
    println!(
        "For bounded random variables in [{:.0}, {:.0}] (range = {:.0}):",
        stats.min, stats.max, range
    );
    println!("P(X̄ - μ ≥ ε) ≤ exp(-2nε²/range²)\n");

    println!("  Relative ε    Absolute ε    Hoeffding Bound");
    println!("  ──────────    ──────────    ───────────────");

    for pct in [0.01, 0.05, 0.10, 0.20] {
        let eps = pct * stats.mean;
        let bound = hoeffding_bound(stats.n, eps, range);
        println!("  {:>8.0}%     {:>10.2}    {:>15.2e}", pct * 100.0, eps, bound);
    }

    // 7. Sample size requirements
    println!("\n─── 7. Sample Size Planning ───\n");

    println!("How many samples are needed for a given precision?\n");

    println!("Hoeffding-based (conservative): n ≥ range²·ln(2/δ) / (2ε²)\n");

    println!("  Precision    Confidence    Required n (Hoeffding)");
    println!("  ─────────    ──────────    ──────────────────────");

    for &eps_pct in &[0.01, 0.05, 0.10] {
        let eps = eps_pct * stats.mean;
        for &delta in &[0.05, 0.01] {
            let n_req = hoeffding_sample_size(eps, delta, range);
            println!(
                "  ±{:>4.0}%        {:>5.0}%        {:>15}",
                eps_pct * 100.0,
                (1.0 - delta) * 100.0,
                n_req
            );
        }
    }

    println!("\nCLT-based (practical): n ≈ (z·σ/ε)²\n");

    println!("  Precision    Required n (95% conf.)");
    println!("  ─────────    ──────────────────────");

    for &margin_pct in &[0.01, 0.05, 0.10] {
        let margin = margin_pct * stats.mean;
        let n_clt = ((1.96 * stats.std_dev / margin).powi(2)).ceil() as usize;
        println!("  ±{:>4.0}%        {:>15}", margin_pct * 100.0, n_clt);
    }

    println!("\nNote: Hoeffding is distribution-free but very conservative.");
    println!("      CLT-based estimates are practical for n > 30.");

    // Summary
    println!("\n─── Summary ───\n");

    let ci = t_confidence_interval(&stats, 0.95);
    println!("For {} variables with {} samples:", args.n, args.samples);
    println!("  Mean BDD size:     {:.2}", stats.mean);
    println!("  95% CI:            [{:.2}, {:.2}]", ci.lower, ci.upper);
    println!("  Relative precision: ±{:.2}%", ci.width() / stats.mean / 2.0 * 100.0);
    println!();
    println!("  Distribution shape: {} (skewness = {:.2})", skew_interpretation(skew), skew);
    println!(
        "  Tails:              {} (excess kurtosis = {:.2})",
        kurt_interpretation(kurt),
        kurt
    );

    // Final assertions
    assert!(ci.width() > 0.0, "confidence interval should have positive width");
    assert!(stats.std_error < stats.std_dev, "std error should be less than std dev");
    assert!(stats.min >= 1.0, "BDD size should be at least 1 (terminal node)");

    println!("\nDone.");

    Ok(())
}

fn skew_interpretation(skew: f64) -> &'static str {
    if skew.abs() < 0.5 {
        "(approximately symmetric)"
    } else if skew > 0.0 {
        "(right-skewed / positive)"
    } else {
        "(left-skewed / negative)"
    }
}

fn kurt_interpretation(kurt: f64) -> &'static str {
    if kurt.abs() < 0.5 {
        "(mesokurtic, normal-like)"
    } else if kurt > 0.0 {
        "(leptokurtic, heavy tails)"
    } else {
        "(platykurtic, light tails)"
    }
}
