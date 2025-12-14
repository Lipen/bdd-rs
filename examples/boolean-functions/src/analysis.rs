//! BDD size distribution analysis.
//!
//! This module provides tools for analyzing the distribution of BDD sizes
//! across Boolean functions.

use std::collections::HashMap;

use ananke_bdd::bdd::Bdd;
use num_bigint::BigUint;

use crate::function::{build_bdd_from_truth_table, TruthTable};
use crate::stats::Statistics;

/// Distribution of BDD sizes for Boolean functions.
#[derive(Debug, Clone)]
pub struct SizeDistribution {
    /// Number of variables
    pub n: usize,
    /// Mapping from size to count
    pub counts: HashMap<usize, usize>,
    /// Total number of functions analyzed
    pub total: usize,
    /// Whether this is exhaustive (all functions) or sampled
    pub exhaustive: bool,
}

impl SizeDistribution {
    /// Create a new empty distribution.
    pub fn new(n: usize, exhaustive: bool) -> Self {
        Self {
            n,
            counts: HashMap::new(),
            total: 0,
            exhaustive,
        }
    }

    /// Add a size observation.
    pub fn add(&mut self, size: usize) {
        *self.counts.entry(size).or_insert(0) += 1;
        self.total += 1;
    }

    /// Add multiple observations from a slice.
    pub fn add_all(&mut self, sizes: &[usize]) {
        for &s in sizes {
            self.add(s);
        }
    }

    /// Get the count for a specific size.
    pub fn count(&self, size: usize) -> usize {
        *self.counts.get(&size).unwrap_or(&0)
    }

    /// Get the probability of a specific size.
    pub fn probability(&self, size: usize) -> f64 {
        if self.total == 0 {
            return 0.0;
        }
        self.count(size) as f64 / self.total as f64
    }

    /// Get all sizes and their counts, sorted by size.
    pub fn sorted_counts(&self) -> Vec<(usize, usize)> {
        let mut v: Vec<_> = self.counts.iter().map(|(&s, &c)| (s, c)).collect();
        v.sort_by_key(|&(s, _)| s);
        v
    }

    /// Get statistics from the distribution.
    pub fn statistics(&self) -> Statistics {
        let sizes: Vec<f64> = self
            .counts
            .iter()
            .flat_map(|(&s, &c)| std::iter::repeat(s as f64).take(c))
            .collect();
        Statistics::from_sample(&sizes)
    }

    /// Get the minimum observed size.
    pub fn min_size(&self) -> Option<usize> {
        self.counts.keys().min().copied()
    }

    /// Get the maximum observed size.
    pub fn max_size(&self) -> Option<usize> {
        self.counts.keys().max().copied()
    }

    /// Get the mode (most common size).
    pub fn mode(&self) -> Option<usize> {
        self.counts.iter().max_by_key(|(_, &c)| c).map(|(&s, _)| s)
    }

    /// Compute the CDF at a given size.
    pub fn cdf(&self, size: usize) -> f64 {
        if self.total == 0 {
            return 0.0;
        }
        let cum: usize = self.counts.iter().filter(|(&s, _)| s <= size).map(|(_, &c)| c).sum();
        cum as f64 / self.total as f64
    }

    /// Merge with another distribution.
    pub fn merge(&mut self, other: &SizeDistribution) {
        assert_eq!(self.n, other.n);
        for (&size, &count) in &other.counts {
            *self.counts.entry(size).or_insert(0) += count;
        }
        self.total += other.total;
        self.exhaustive = self.exhaustive && other.exhaustive;
    }
}

/// Histogram for visualizing size distributions.
#[derive(Debug, Clone)]
pub struct SizeHistogram {
    /// Bin edges (lower bounds)
    pub bins: Vec<usize>,
    /// Counts per bin
    pub counts: Vec<usize>,
    /// Total count
    pub total: usize,
}

impl SizeHistogram {
    /// Create a histogram from a size distribution.
    pub fn from_distribution(dist: &SizeDistribution, num_bins: usize) -> Self {
        let min = dist.min_size().unwrap_or(0);
        let max = dist.max_size().unwrap_or(0);

        if min == max || num_bins == 0 {
            return Self {
                bins: vec![min],
                counts: vec![dist.total],
                total: dist.total,
            };
        }

        let bin_width = ((max - min) / num_bins).max(1);
        let mut bins = Vec::new();
        let mut counts = Vec::new();

        let mut bin_start = min;
        while bin_start <= max {
            bins.push(bin_start);
            let bin_end = bin_start + bin_width;
            let count: usize = dist
                .counts
                .iter()
                .filter(|(&s, _)| s >= bin_start && s < bin_end)
                .map(|(_, &c)| c)
                .sum();
            counts.push(count);
            bin_start = bin_end;
        }

        Self {
            bins,
            counts,
            total: dist.total,
        }
    }

    /// Create a histogram with fixed bin size.
    pub fn with_bin_size(dist: &SizeDistribution, bin_size: usize) -> Self {
        let min = dist.min_size().unwrap_or(0);
        let max = dist.max_size().unwrap_or(0);
        let num_bins = ((max - min) / bin_size.max(1)) + 1;
        Self::from_distribution(dist, num_bins)
    }

    /// Render as ASCII art.
    pub fn to_ascii(&self, _width: usize, height: usize) -> String {
        if self.counts.is_empty() {
            return String::from("(empty histogram)");
        }

        let max_count = *self.counts.iter().max().unwrap_or(&1);
        let mut lines = Vec::new();

        // Y-axis scale
        let scale = max_count as f64 / height as f64;

        // Build rows from top to bottom
        for row in (0..height).rev() {
            let threshold = ((row + 1) as f64 * scale) as usize;
            let mut line = String::new();

            // Y-axis label
            if row == height - 1 {
                line.push_str(&format!("{:>6}│", max_count));
            } else if row == 0 {
                line.push_str(&format!("{:>6}│", 0));
            } else {
                line.push_str("      │");
            }

            // Bars
            for &count in &self.counts {
                if count >= threshold {
                    line.push('█');
                } else if count > ((row as f64) * scale) as usize {
                    line.push('▄');
                } else {
                    line.push(' ');
                }
            }

            lines.push(line);
        }

        // X-axis
        lines.push(format!("      └{}", "─".repeat(self.counts.len())));

        // X-axis labels
        if !self.bins.is_empty() {
            let first = self.bins[0];
            let last = *self.bins.last().unwrap();
            lines.push(format!("       {:>width$}{:>width$}", first, last, width = self.counts.len() / 2));
        }

        lines.join("\n")
    }
}

/// Compute exhaustive size distribution for small n.
///
/// Warning: Only practical for n ≤ 4 (65536 functions) or maybe n = 5 with patience.
pub fn exhaustive_distribution(n: usize) -> SizeDistribution {
    let bdd = Bdd::default();
    let mut dist = SizeDistribution::new(n, true);

    for tt in TruthTable::all_functions(n) {
        let bdd_ref = build_bdd_from_truth_table(&bdd, &tt);
        let size = bdd.size(bdd_ref) as usize;
        dist.add(size);
    }

    dist
}

/// Summary statistics for a given n.
#[derive(Debug, Clone)]
pub struct VariableSummary {
    /// Number of variables
    pub n: usize,
    /// Total number of functions (2^(2^n))
    pub total_functions: BigUint,
    /// Statistics from sampling or exhaustive enumeration
    pub stats: Statistics,
    /// Distribution
    pub distribution: SizeDistribution,
}

impl VariableSummary {
    /// Create from exhaustive enumeration.
    pub fn exhaustive(n: usize) -> Self {
        let dist = exhaustive_distribution(n);
        let stats = dist.statistics();
        let total_functions = TruthTable::total_count(n);

        Self {
            n,
            total_functions,
            stats,
            distribution: dist,
        }
    }

    /// Print a summary table.
    pub fn summary_table(&self) -> String {
        let mut s = String::new();
        s.push_str(&format!("n = {}\n", self.n));
        s.push_str(&format!("Total functions: {}\n", self.total_functions));
        s.push_str(&format!(
            "Analyzed: {} ({})\n",
            self.distribution.total,
            if self.distribution.exhaustive { "exhaustive" } else { "sampled" }
        ));
        s.push_str(&format!("Mean BDD size: {:.4}\n", self.stats.mean));
        s.push_str(&format!("Std deviation: {:.4}\n", self.stats.std_dev));
        s.push_str(&format!("Min size: {:.0}\n", self.stats.min));
        s.push_str(&format!("Max size: {:.0}\n", self.stats.max));
        s.push_str(&format!("Median: {:.0}\n", self.stats.median));
        s.push_str(&format!("Mode: {:?}\n", self.distribution.mode()));
        s
    }
}

/// Theoretical bounds on BDD size.
pub mod bounds {
    /// Maximum possible BDD size for n variables.
    ///
    /// This is at most 2^n - 1 (a complete decision tree minus sharing).
    pub fn max_size(n: usize) -> usize {
        (1 << n) - 1
    }

    /// Expected BDD size for a random function (Shannon's bound).
    ///
    /// Most functions have BDD size Θ(2^n / n).
    pub fn expected_size(n: usize) -> f64 {
        if n == 0 {
            return 0.0;
        }
        (1 << n) as f64 / n as f64
    }

    /// Number of functions with BDD size at most k.
    ///
    /// This is a rough upper bound based on counting arguments.
    pub fn count_small_functions(n: usize, k: usize) -> f64 {
        // Very rough: each of k nodes can be one of n variables
        // with 2 children from {0,1,...,k-1} ∪ {⊤,⊥}
        // This is a massive overcount, but illustrative
        let choices_per_node = n * (k + 2) * (k + 2);
        (choices_per_node as f64).powi(k as i32)
    }

    /// Shannon entropy of a distribution.
    pub fn entropy(probs: &[f64]) -> f64 {
        probs.iter().filter(|&&p| p > 0.0).map(|&p| -p * p.log2()).sum()
    }
}

/// Find extreme functions (smallest/largest BDD).
pub fn find_extreme_functions(n: usize, sample_size: usize) -> (Vec<TruthTable>, Vec<TruthTable>) {
    use rand::SeedableRng;
    use rand_chacha::ChaCha8Rng;

    let bdd = Bdd::default();
    let mut rng = ChaCha8Rng::seed_from_u64(42);

    let mut min_size = usize::MAX;
    let mut max_size = 0;
    let mut min_functions = Vec::new();
    let mut max_functions = Vec::new();

    for _ in 0..sample_size {
        let tt = TruthTable::random(n, &mut rng);
        let bdd_ref = build_bdd_from_truth_table(&bdd, &tt);
        let size = bdd.size(bdd_ref) as usize;

        if size < min_size {
            min_size = size;
            min_functions.clear();
            min_functions.push(tt.clone());
        } else if size == min_size && min_functions.len() < 10 {
            min_functions.push(tt.clone());
        }

        if size > max_size {
            max_size = size;
            max_functions.clear();
            max_functions.push(tt);
        } else if size == max_size && max_functions.len() < 10 {
            max_functions.push(tt);
        }
    }

    (min_functions, max_functions)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_size_distribution() {
        let mut dist = SizeDistribution::new(3, false);
        dist.add(2);
        dist.add(2);
        dist.add(3);
        dist.add(4);

        assert_eq!(dist.total, 4);
        assert_eq!(dist.count(2), 2);
        assert_eq!(dist.probability(2), 0.5);
        assert_eq!(dist.min_size(), Some(2));
        assert_eq!(dist.max_size(), Some(4));
        assert_eq!(dist.mode(), Some(2));
    }

    #[test]
    fn test_exhaustive_small() {
        // n=2: 16 functions
        let dist = exhaustive_distribution(2);
        assert_eq!(dist.total, 16);
        assert!(dist.exhaustive);

        // Check known counts:
        // Size 1: 2 functions (constants 0 and 1 - just terminal)
        // Size 2: 4 functions (projections x1, ¬x1, x2, ¬x2 - one node + terminal)
        assert_eq!(dist.count(1), 2);
        assert_eq!(dist.count(2), 4);
    }

    #[test]
    fn test_histogram() {
        let mut dist = SizeDistribution::new(3, false);
        for s in 1..=10 {
            for _ in 0..s {
                dist.add(s);
            }
        }

        let hist = SizeHistogram::from_distribution(&dist, 5);
        assert!(!hist.counts.is_empty());
        assert_eq!(hist.total, dist.total);
    }

    #[test]
    fn test_theoretical_bounds() {
        assert_eq!(bounds::max_size(3), 7);
        assert_eq!(bounds::max_size(4), 15);

        // Expected size for n=4 should be around 16/4 = 4
        let exp = bounds::expected_size(4);
        assert!((exp - 4.0).abs() < 0.1);
    }
}
