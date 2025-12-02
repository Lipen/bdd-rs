//! Monte Carlo sampling strategies for Boolean function exploration.
//!
//! This module provides efficient sampling strategies for exploring
//! the space of Boolean functions.

use bdd_rs::bdd::Bdd;
use rand::Rng;

use crate::function::{random_function_with_bdd, BooleanFunction, TruthTable};
use crate::stats::{bootstrap, clt_confidence_interval, t_confidence_interval, BootstrapResult, ConfidenceInterval, Statistics};

/// Configuration for Monte Carlo sampling.
#[derive(Debug, Clone)]
pub struct SamplingConfig {
    /// Number of variables
    pub n: usize,
    /// Number of samples
    pub num_samples: usize,
    /// Confidence level for intervals (e.g., 0.95)
    pub confidence: f64,
    /// Number of bootstrap resamples (0 to disable)
    pub bootstrap_resamples: usize,
    /// Random seed (None for random)
    pub seed: Option<u64>,
}

impl SamplingConfig {
    /// Create a new configuration with defaults.
    pub fn new(n: usize, num_samples: usize) -> Self {
        Self {
            n,
            num_samples,
            confidence: 0.95,
            bootstrap_resamples: 1000,
            seed: None,
        }
    }

    /// Set the confidence level.
    pub fn with_confidence(mut self, confidence: f64) -> Self {
        self.confidence = confidence;
        self
    }

    /// Set the number of bootstrap resamples.
    pub fn with_bootstrap(mut self, resamples: usize) -> Self {
        self.bootstrap_resamples = resamples;
        self
    }

    /// Set the random seed.
    pub fn with_seed(mut self, seed: u64) -> Self {
        self.seed = Some(seed);
        self
    }
}

impl Default for SamplingConfig {
    fn default() -> Self {
        Self::new(4, 1000)
    }
}

/// Results from Monte Carlo sampling.
#[derive(Debug)]
pub struct SamplingResult {
    /// Configuration used
    pub config: SamplingConfig,
    /// Sample statistics
    pub stats: Statistics,
    /// Raw size samples
    pub sizes: Vec<usize>,
    /// CLT-based confidence interval for mean
    pub clt_ci: ConfidenceInterval,
    /// t-distribution confidence interval for mean
    pub t_ci: ConfidenceInterval,
    /// Bootstrap result (if enabled)
    pub bootstrap: Option<BootstrapResult>,
    /// Size distribution counts (size -> count)
    pub size_distribution: Vec<(usize, usize)>,
}

impl SamplingResult {
    /// Get the estimated mean BDD size.
    pub fn mean_size(&self) -> f64 {
        self.stats.mean
    }

    /// Get the standard error of the mean.
    pub fn std_error(&self) -> f64 {
        self.stats.std_error
    }

    /// Get the 95% confidence interval.
    pub fn confidence_interval(&self) -> ConfidenceInterval {
        self.t_ci
    }

    /// Print a summary of the results.
    pub fn summary(&self) -> String {
        let mut s = String::new();
        s.push_str(&format!(
            "Monte Carlo Sampling Results (n={}, samples={})\n",
            self.config.n, self.config.num_samples
        ));
        s.push_str(&"─".repeat(60));
        s.push('\n');
        s.push_str(&format!("Mean BDD size: {:.4}\n", self.stats.mean));
        s.push_str(&format!("Std deviation: {:.4}\n", self.stats.std_dev));
        s.push_str(&format!("Std error:     {:.4}\n", self.stats.std_error));
        s.push_str(&format!("Min size:      {:.0}\n", self.stats.min));
        s.push_str(&format!("Max size:      {:.0}\n", self.stats.max));
        s.push_str(&format!("Median:        {:.0}\n", self.stats.median));
        s.push_str(&format!("\nConfidence Intervals ({:.0}%):\n", self.config.confidence * 100.0));
        s.push_str(&format!("  CLT:       {}\n", self.clt_ci));
        s.push_str(&format!("  t-dist:    {}\n", self.t_ci));
        if let Some(ref boot) = self.bootstrap {
            s.push_str(&format!("  Bootstrap: {}\n", boot.percentile_ci));
        }
        s
    }
}

/// A Monte Carlo sampler for Boolean functions.
pub struct MonteCarloSampler {
    config: SamplingConfig,
}

impl MonteCarloSampler {
    /// Create a new sampler with the given configuration.
    pub fn new(config: SamplingConfig) -> Self {
        Self { config }
    }

    /// Run the sampling and return results.
    pub fn sample<R: Rng>(&self, rng: &mut R) -> SamplingResult {
        let bdd = Bdd::default();
        let mut sizes = Vec::with_capacity(self.config.num_samples);

        // Collect samples
        for _ in 0..self.config.num_samples {
            let func = random_function_with_bdd(&bdd, self.config.n, rng);
            sizes.push(func.size);
        }

        self.analyze_samples(sizes, rng)
    }

    /// Analyze pre-collected samples.
    pub fn analyze_samples<R: Rng>(&self, sizes: Vec<usize>, rng: &mut R) -> SamplingResult {
        let float_sizes: Vec<f64> = sizes.iter().map(|&s| s as f64).collect();
        let stats = Statistics::from_sample(&float_sizes);

        // Confidence intervals
        let clt_ci = clt_confidence_interval(&stats, self.config.confidence);
        let t_ci = t_confidence_interval(&stats, self.config.confidence);

        // Bootstrap (if enabled)
        let bootstrap_result = if self.config.bootstrap_resamples > 0 {
            Some(bootstrap(
                &float_sizes,
                self.config.bootstrap_resamples,
                self.config.confidence,
                rng,
            ))
        } else {
            None
        };

        // Size distribution
        let mut size_counts = std::collections::HashMap::new();
        for &s in &sizes {
            *size_counts.entry(s).or_insert(0) += 1;
        }
        let mut size_distribution: Vec<_> = size_counts.into_iter().collect();
        size_distribution.sort_by_key(|&(s, _)| s);

        SamplingResult {
            config: self.config.clone(),
            stats,
            sizes,
            clt_ci,
            t_ci,
            bootstrap: bootstrap_result,
            size_distribution,
        }
    }
}

/// Sample with adaptive stopping based on desired precision.
///
/// Continues sampling until the confidence interval width is below the threshold.
pub struct AdaptiveSampler {
    /// Number of variables
    pub n: usize,
    /// Maximum number of samples
    pub max_samples: usize,
    /// Minimum number of samples before checking precision
    pub min_samples: usize,
    /// Target confidence interval width (relative to mean)
    pub target_precision: f64,
    /// Confidence level
    pub confidence: f64,
    /// Check interval (how often to compute statistics)
    pub check_interval: usize,
}

impl AdaptiveSampler {
    /// Create a new adaptive sampler.
    pub fn new(n: usize) -> Self {
        Self {
            n,
            max_samples: 100_000,
            min_samples: 100,
            target_precision: 0.01, // 1% of mean
            confidence: 0.95,
            check_interval: 100,
        }
    }

    /// Run adaptive sampling.
    pub fn sample<R: Rng>(&self, rng: &mut R) -> (Vec<usize>, usize) {
        let bdd = Bdd::default();
        let mut sizes = Vec::new();
        let mut samples_taken = 0;

        loop {
            // Take a batch of samples
            for _ in 0..self.check_interval {
                if samples_taken >= self.max_samples {
                    return (sizes, samples_taken);
                }
                let func = random_function_with_bdd(&bdd, self.n, rng);
                sizes.push(func.size);
                samples_taken += 1;
            }

            // Check if we have enough precision
            if samples_taken >= self.min_samples {
                let float_sizes: Vec<f64> = sizes.iter().map(|&s| s as f64).collect();
                let stats = Statistics::from_sample(&float_sizes);

                if stats.mean > 0.0 {
                    let ci = t_confidence_interval(&stats, self.confidence);
                    let relative_width = ci.width() / stats.mean;

                    if relative_width <= self.target_precision {
                        return (sizes, samples_taken);
                    }
                }
            }
        }
    }
}

/// Stratified sampling based on function properties.
///
/// Samples functions from different "strata" defined by properties
/// like number of minterms, symmetry, etc.
pub struct StratifiedSampler {
    /// Number of variables
    pub n: usize,
    /// Number of samples per stratum
    pub samples_per_stratum: usize,
}

impl StratifiedSampler {
    /// Create a new stratified sampler.
    pub fn new(n: usize, samples_per_stratum: usize) -> Self {
        Self { n, samples_per_stratum }
    }

    /// Sample from strata based on minterm count.
    ///
    /// Strata are defined by intervals of minterm count.
    pub fn sample_by_minterm_count<R: Rng>(&self, num_strata: usize, rng: &mut R) -> Vec<(usize, Vec<BooleanFunction>)> {
        let bdd = Bdd::default();
        let num_minterms = 1usize << self.n;
        let strata_size = (num_minterms + 1) / num_strata;

        let mut results = Vec::new();

        for stratum in 0..num_strata {
            let min_count = stratum * strata_size;
            let max_count = ((stratum + 1) * strata_size).min(num_minterms);

            let mut functions = Vec::new();
            let mut attempts = 0;
            let max_attempts = self.samples_per_stratum * 1000;

            while functions.len() < self.samples_per_stratum && attempts < max_attempts {
                attempts += 1;
                let tt = TruthTable::random(self.n, rng);
                let count = tt.count_ones();

                if count >= min_count && count < max_count {
                    let func = BooleanFunction::from_truth_table(&bdd, &tt);
                    functions.push(func);
                }
            }

            results.push((stratum, functions));
        }

        results
    }
}

#[cfg(test)]
mod tests {
    use rand::SeedableRng;
    use rand_chacha::ChaCha8Rng;

    use super::*;

    #[test]
    fn test_monte_carlo_sampling() {
        let mut rng = ChaCha8Rng::seed_from_u64(42);
        let config = SamplingConfig::new(3, 100);
        let sampler = MonteCarloSampler::new(config);
        let result = sampler.sample(&mut rng);

        assert_eq!(result.sizes.len(), 100);
        assert!(result.stats.mean > 0.0);
        assert!(result.clt_ci.contains(result.stats.mean));
    }

    #[test]
    fn test_adaptive_sampling() {
        let mut rng = ChaCha8Rng::seed_from_u64(42);
        let sampler = AdaptiveSampler {
            n: 3,
            max_samples: 1000,
            min_samples: 50,
            target_precision: 0.1,
            confidence: 0.95,
            check_interval: 50,
        };

        let (sizes, count) = sampler.sample(&mut rng);
        assert!(!sizes.is_empty());
        assert!(count >= 50);
        assert!(count <= 1000);
    }
}
