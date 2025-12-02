//! Statistical analysis tools for BDD size distribution.
//!
//! This module provides statistical methods for analyzing samples:
//! - Basic statistics (mean, variance, standard deviation)
//! - Confidence intervals using various methods
//! - Tail bounds (Chernoff, Chebyshev)
//! - Bootstrap resampling

use rand::Rng;
use statrs::distribution::{ContinuousCDF, Normal, StudentsT};

/// Basic statistics computed from a sample.
#[derive(Debug, Clone)]
pub struct Statistics {
    /// Sample size
    pub n: usize,
    /// Sample mean
    pub mean: f64,
    /// Sample variance (unbiased, using n-1)
    pub variance: f64,
    /// Sample standard deviation
    pub std_dev: f64,
    /// Minimum value
    pub min: f64,
    /// Maximum value
    pub max: f64,
    /// Median
    pub median: f64,
    /// Standard error of the mean
    pub std_error: f64,
}

impl Statistics {
    /// Compute statistics from a sample.
    pub fn from_sample(sample: &[f64]) -> Self {
        assert!(!sample.is_empty(), "Cannot compute statistics from empty sample");

        let n = sample.len();
        let mean = sample.iter().sum::<f64>() / n as f64;

        let variance = if n > 1 {
            sample.iter().map(|x| (x - mean).powi(2)).sum::<f64>() / (n - 1) as f64
        } else {
            0.0
        };

        let std_dev = variance.sqrt();
        let std_error = std_dev / (n as f64).sqrt();

        let mut sorted = sample.to_vec();
        sorted.sort_by(|a, b| a.partial_cmp(b).unwrap());

        let min = sorted[0];
        let max = sorted[n - 1];
        let median = if n % 2 == 0 {
            (sorted[n / 2 - 1] + sorted[n / 2]) / 2.0
        } else {
            sorted[n / 2]
        };

        Self {
            n,
            mean,
            variance,
            std_dev,
            min,
            max,
            median,
            std_error,
        }
    }

    /// Compute statistics from integer samples.
    pub fn from_usize_sample(sample: &[usize]) -> Self {
        let floats: Vec<f64> = sample.iter().map(|&x| x as f64).collect();
        Self::from_sample(&floats)
    }
}

/// A confidence interval.
#[derive(Debug, Clone, Copy)]
pub struct ConfidenceInterval {
    /// Lower bound
    pub lower: f64,
    /// Upper bound
    pub upper: f64,
    /// Confidence level (e.g., 0.95 for 95%)
    pub confidence: f64,
}

impl ConfidenceInterval {
    /// Create a new confidence interval.
    pub fn new(lower: f64, upper: f64, confidence: f64) -> Self {
        Self { lower, upper, confidence }
    }

    /// Interval width
    pub fn width(&self) -> f64 {
        self.upper - self.lower
    }

    /// Check if a value is within the interval.
    pub fn contains(&self, value: f64) -> bool {
        value >= self.lower && value <= self.upper
    }
}

impl std::fmt::Display for ConfidenceInterval {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "[{:.4}, {:.4}] ({:.0}% CI)", self.lower, self.upper, self.confidence * 100.0)
    }
}

/// Tail bound information.
#[derive(Debug, Clone)]
pub struct TailBound {
    /// The threshold value
    pub threshold: f64,
    /// Probability that sample exceeds threshold (upper tail)
    pub upper_prob: f64,
    /// Probability that sample is below threshold (lower tail)
    pub lower_prob: f64,
    /// Method used to compute the bound
    pub method: TailBoundMethod,
}

/// Method used for tail bound computation.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TailBoundMethod {
    /// Chebyshev inequality (uses only mean and variance)
    Chebyshev,
    /// Chernoff bound (for bounded random variables)
    Chernoff,
    /// Empirical (direct from sample)
    Empirical,
}

impl std::fmt::Display for TailBound {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "P(X > {:.2}) ≤ {:.6} ({:?})", self.threshold, self.upper_prob, self.method)
    }
}

/// Compute a confidence interval for the mean using the Central Limit Theorem.
///
/// This assumes the sample size is large enough (typically n ≥ 30) for the
/// CLT approximation to be valid.
pub fn clt_confidence_interval(stats: &Statistics, confidence: f64) -> ConfidenceInterval {
    let alpha = 1.0 - confidence;
    let z = Normal::new(0.0, 1.0).unwrap().inverse_cdf(1.0 - alpha / 2.0);

    let margin = z * stats.std_error;
    ConfidenceInterval::new(stats.mean - margin, stats.mean + margin, confidence)
}

/// Compute a confidence interval using Student's t-distribution.
///
/// More accurate than CLT for smaller samples.
pub fn t_confidence_interval(stats: &Statistics, confidence: f64) -> ConfidenceInterval {
    if stats.n <= 1 {
        return ConfidenceInterval::new(f64::NEG_INFINITY, f64::INFINITY, confidence);
    }

    let alpha = 1.0 - confidence;
    let df = (stats.n - 1) as f64;
    let t = StudentsT::new(0.0, 1.0, df).unwrap().inverse_cdf(1.0 - alpha / 2.0);

    let margin = t * stats.std_error;
    ConfidenceInterval::new(stats.mean - margin, stats.mean + margin, confidence)
}

/// Result of bootstrap resampling.
#[derive(Debug, Clone)]
pub struct BootstrapResult {
    /// Bootstrap sample means
    pub means: Vec<f64>,
    /// Bootstrap estimate of the mean
    pub mean: f64,
    /// Bootstrap standard error
    pub std_error: f64,
    /// Percentile-based confidence interval
    pub percentile_ci: ConfidenceInterval,
    /// BCa (bias-corrected and accelerated) confidence interval
    pub bca_ci: Option<ConfidenceInterval>,
}

/// Perform bootstrap resampling to estimate the sampling distribution.
///
/// # Arguments
/// * `sample` - The original sample
/// * `num_resamples` - Number of bootstrap resamples (typically 1000-10000)
/// * `confidence` - Confidence level for intervals
/// * `rng` - Random number generator
pub fn bootstrap<R: Rng>(sample: &[f64], num_resamples: usize, confidence: f64, rng: &mut R) -> BootstrapResult {
    let n = sample.len();
    let mut means = Vec::with_capacity(num_resamples);

    // Generate bootstrap resamples
    for _ in 0..num_resamples {
        let mut resample_sum = 0.0;
        for _ in 0..n {
            let idx = rng.gen_range(0..n);
            resample_sum += sample[idx];
        }
        means.push(resample_sum / n as f64);
    }

    // Sort for percentile calculation
    means.sort_by(|a, b| a.partial_cmp(b).unwrap());

    // Bootstrap mean and standard error
    let bootstrap_mean = means.iter().sum::<f64>() / num_resamples as f64;
    let bootstrap_var = means.iter().map(|x| (x - bootstrap_mean).powi(2)).sum::<f64>() / (num_resamples - 1) as f64;
    let std_error = bootstrap_var.sqrt();

    // Percentile confidence interval
    let alpha = 1.0 - confidence;
    let lower_idx = ((alpha / 2.0) * num_resamples as f64) as usize;
    let upper_idx = ((1.0 - alpha / 2.0) * num_resamples as f64) as usize;
    let percentile_ci = ConfidenceInterval::new(
        means[lower_idx.min(num_resamples - 1)],
        means[upper_idx.min(num_resamples - 1)],
        confidence,
    );

    BootstrapResult {
        means,
        mean: bootstrap_mean,
        std_error,
        percentile_ci,
        bca_ci: None, // BCa is more complex, omitted for simplicity
    }
}

/// Compute a Chebyshev tail bound.
///
/// Chebyshev's inequality: P(|X - μ| ≥ kσ) ≤ 1/k²
///
/// This is distribution-free but often loose.
pub fn chebyshev_bound(stats: &Statistics, k: f64) -> TailBound {
    let prob = 1.0 / (k * k);
    let threshold = stats.mean + k * stats.std_dev;

    TailBound {
        threshold,
        upper_prob: prob / 2.0, // One-sided
        lower_prob: prob / 2.0,
        method: TailBoundMethod::Chebyshev,
    }
}

/// Compute a Chebyshev bound for the sample mean.
///
/// By the law of large numbers, the sample mean has variance σ²/n.
pub fn chebyshev_mean_bound(stats: &Statistics, k: f64) -> TailBound {
    let prob = 1.0 / (k * k);
    let threshold = stats.mean + k * stats.std_error;

    TailBound {
        threshold,
        upper_prob: prob / 2.0,
        lower_prob: prob / 2.0,
        method: TailBoundMethod::Chebyshev,
    }
}

/// Compute a Hoeffding/Chernoff-style bound for bounded random variables.
///
/// For random variables in [a, b], we have:
/// P(X̄ - μ ≥ ε) ≤ exp(-2nε²/(b-a)²)
///
/// # Arguments
/// * `n` - Sample size
/// * `epsilon` - Deviation from mean
/// * `range` - Range of the random variable (b - a)
pub fn hoeffding_bound(n: usize, epsilon: f64, range: f64) -> f64 {
    let exponent = -2.0 * (n as f64) * epsilon * epsilon / (range * range);
    exponent.exp()
}

/// Compute the sample size needed for a given precision using Hoeffding.
///
/// Returns n such that P(|X̄ - μ| ≥ ε) ≤ δ
pub fn hoeffding_sample_size(epsilon: f64, delta: f64, range: f64) -> usize {
    let n = (range * range) * (2.0_f64.ln() / delta.ln().abs()) / (2.0 * epsilon * epsilon);
    n.ceil() as usize
}

/// Compute empirical tail probabilities.
pub fn empirical_tail_bound(sample: &[f64], threshold: f64) -> TailBound {
    let upper_count = sample.iter().filter(|&&x| x > threshold).count();
    let lower_count = sample.iter().filter(|&&x| x < threshold).count();

    TailBound {
        threshold,
        upper_prob: upper_count as f64 / sample.len() as f64,
        lower_prob: lower_count as f64 / sample.len() as f64,
        method: TailBoundMethod::Empirical,
    }
}

/// Compute multiple quantiles from a sample.
pub fn quantiles(sample: &[f64], probs: &[f64]) -> Vec<f64> {
    let mut sorted = sample.to_vec();
    sorted.sort_by(|a, b| a.partial_cmp(b).unwrap());

    probs
        .iter()
        .map(|&p| {
            let idx = (p * (sorted.len() - 1) as f64) as usize;
            sorted[idx.min(sorted.len() - 1)]
        })
        .collect()
}

/// Compute the interquartile range (IQR).
pub fn iqr(sample: &[f64]) -> f64 {
    let qs = quantiles(sample, &[0.25, 0.75]);
    qs[1] - qs[0]
}

/// Estimate the mode using kernel density estimation (simplified).
pub fn estimate_mode(sample: &[f64], bins: usize) -> f64 {
    let stats = Statistics::from_sample(sample);
    let bin_width = (stats.max - stats.min) / bins as f64;

    if bin_width == 0.0 {
        return stats.mean;
    }

    let mut counts = vec![0usize; bins];
    for &x in sample {
        let bin = ((x - stats.min) / bin_width) as usize;
        counts[bin.min(bins - 1)] += 1;
    }

    let max_bin = counts.iter().enumerate().max_by_key(|(_, c)| *c).unwrap().0;
    stats.min + (max_bin as f64 + 0.5) * bin_width
}

#[cfg(test)]
mod tests {
    use rand::SeedableRng;
    use rand_chacha::ChaCha8Rng;

    use super::*;

    #[test]
    fn test_statistics() {
        let sample = vec![1.0, 2.0, 3.0, 4.0, 5.0];
        let stats = Statistics::from_sample(&sample);

        assert_eq!(stats.n, 5);
        assert!((stats.mean - 3.0).abs() < 1e-10);
        assert!((stats.variance - 2.5).abs() < 1e-10);
        assert_eq!(stats.min, 1.0);
        assert_eq!(stats.max, 5.0);
        assert_eq!(stats.median, 3.0);
    }

    #[test]
    fn test_confidence_intervals() {
        let sample: Vec<f64> = (1..=100).map(|x| x as f64).collect();
        let stats = Statistics::from_sample(&sample);

        let clt_ci = clt_confidence_interval(&stats, 0.95);
        assert!(clt_ci.contains(stats.mean));
        assert!(clt_ci.lower < stats.mean);
        assert!(clt_ci.upper > stats.mean);

        let t_ci = t_confidence_interval(&stats, 0.95);
        assert!(t_ci.contains(stats.mean));
    }

    #[test]
    fn test_bootstrap() {
        let mut rng = ChaCha8Rng::seed_from_u64(42);
        let sample: Vec<f64> = (1..=50).map(|x| x as f64).collect();

        let result = bootstrap(&sample, 1000, 0.95, &mut rng);
        assert_eq!(result.means.len(), 1000);
        assert!(result.percentile_ci.contains(25.5)); // True mean
    }

    #[test]
    fn test_hoeffding() {
        // For n=100, ε=0.1, range=1: P ≤ exp(-2*100*0.01/1) = exp(-2) ≈ 0.135
        let bound = hoeffding_bound(100, 0.1, 1.0);
        assert!((bound - (-2.0_f64).exp()).abs() < 1e-10);
    }
}
