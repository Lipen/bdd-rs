//! Visualization utilities for BDD size distributions.
//!
//! Provides ASCII-based visualization tools for terminal output.

use crate::analysis::SizeDistribution;
use crate::stats::Statistics;

/// Configuration for ASCII histogram.
#[derive(Debug, Clone)]
pub struct HistogramConfig {
    /// Width in characters
    pub width: usize,
    /// Height in characters
    pub height: usize,
    /// Number of bins
    pub bins: usize,
    /// Whether to show axis labels
    pub show_labels: bool,
    /// Character for filled bars
    pub fill_char: char,
    /// Character for empty space
    pub empty_char: char,
}

impl Default for HistogramConfig {
    fn default() -> Self {
        Self {
            width: 60,
            height: 15,
            bins: 20,
            show_labels: true,
            fill_char: '█',
            empty_char: ' ',
        }
    }
}

/// Render a histogram of sizes.
pub fn render_histogram(sizes: &[usize], config: &HistogramConfig) -> String {
    if sizes.is_empty() {
        return String::from("(no data)");
    }

    let min = *sizes.iter().min().unwrap();
    let max = *sizes.iter().max().unwrap();

    if min == max {
        return format!("All {} samples have size {}\n", sizes.len(), min);
    }

    let bin_width = ((max - min) as f64 / config.bins as f64).max(1.0);
    let mut bin_counts = vec![0usize; config.bins];

    for &s in sizes {
        let bin = (((s - min) as f64) / bin_width) as usize;
        bin_counts[bin.min(config.bins - 1)] += 1;
    }

    let max_count = *bin_counts.iter().max().unwrap_or(&1);
    let scale = config.height as f64 / max_count as f64;

    let mut lines = Vec::new();

    // Title
    lines.push(format!("BDD Size Distribution (n={} samples)", sizes.len()));
    lines.push(String::new());

    // Histogram body
    for row in (0..config.height).rev() {
        let mut line = String::new();

        // Y-axis label
        if row == config.height - 1 {
            line.push_str(&format!("{:>6} │", max_count));
        } else if row == 0 {
            line.push_str(&format!("{:>6} │", 0));
        } else {
            line.push_str("       │");
        }

        // Bars
        for &count in &bin_counts {
            let bar_height = (count as f64 * scale) as usize;
            if bar_height >= row + 1 {
                line.push(config.fill_char);
            } else {
                line.push(config.empty_char);
            }
        }

        lines.push(line);
    }

    // X-axis
    lines.push(format!("       └{}", "─".repeat(config.bins)));

    // X-axis labels
    if config.show_labels {
        let label_line = format!("        {:<width$}{:>width$}", min, max, width = config.bins / 2);
        lines.push(label_line);
        lines.push(format!("        {:^width$}", "BDD Size", width = config.bins));
    }

    lines.join("\n")
}

/// Render statistics as a formatted table.
pub fn render_statistics(stats: &Statistics, title: &str) -> String {
    let mut lines = Vec::new();

    lines.push(format!("─── {} ───", title));
    lines.push(String::new());
    lines.push(format!("Sample Size:    {}", stats.n));
    lines.push(format!("Mean:           {:.4}", stats.mean));
    lines.push(format!("Std Deviation:  {:.4}", stats.std_dev));
    lines.push(format!("Std Error:      {:.4}", stats.std_error));
    lines.push(format!("Variance:       {:.4}", stats.variance));
    lines.push(String::new());
    lines.push(format!("Minimum:        {:.0}", stats.min));
    lines.push(format!("Maximum:        {:.0}", stats.max));
    lines.push(format!("Median:         {:.0}", stats.median));

    lines.join("\n")
}

/// Render a comparison table across multiple n values.
pub fn render_comparison_table(summaries: &[(usize, Statistics)]) -> String {
    let mut lines: Vec<String> = Vec::new();

    lines.push("  n      Mean     Std Dev       Min       Max    Median".to_string());
    lines.push("────   ────────   ────────   ────────  ────────  ────────".to_string());

    for (n, stats) in summaries {
        lines.push(format!(
            "{:>3}    {:>8.2}   {:>8.2}   {:>8.0}  {:>8.0}  {:>8.0}",
            n, stats.mean, stats.std_dev, stats.min, stats.max, stats.median
        ));
    }

    lines.join("\n")
}

/// Render a probability density estimate.
pub fn render_density(dist: &SizeDistribution, width: usize) -> String {
    let sorted = dist.sorted_counts();
    if sorted.is_empty() {
        return String::from("(no data)");
    }

    let max_count = sorted.iter().map(|(_, c)| *c).max().unwrap_or(1);
    let max_bar = width - 15;

    let mut lines = Vec::new();
    lines.push(format!("Size Distribution (total: {})", dist.total));
    lines.push(String::new());

    for (size, count) in &sorted {
        let bar_len = (*count as f64 / max_count as f64 * max_bar as f64) as usize;
        let bar = "█".repeat(bar_len);
        let prob = *count as f64 / dist.total as f64;
        lines.push(format!(
            "{:>4} │{:<bar_width$}│ {:>5} ({:.1}%)",
            size,
            bar,
            count,
            prob * 100.0,
            bar_width = max_bar
        ));
    }

    lines.join("\n")
}

/// Render a box plot (ASCII approximation).
pub fn render_boxplot(sizes: &[usize], width: usize) -> String {
    if sizes.is_empty() {
        return String::from("(no data)");
    }

    let mut sorted: Vec<_> = sizes.to_vec();
    sorted.sort();

    let n = sorted.len();
    let min = sorted[0];
    let max = sorted[n - 1];
    let q1 = sorted[n / 4];
    let median = sorted[n / 2];
    let q3 = sorted[3 * n / 4];

    let range = (max - min) as f64;
    if range == 0.0 {
        return format!("All values = {}", min);
    }

    let scale = |v: usize| -> usize { ((v - min) as f64 / range * (width - 2) as f64) as usize };

    let mut line = vec![' '; width];

    // Draw whiskers
    let min_pos = 0;
    let max_pos = width - 1;
    line[min_pos] = '├';
    line[max_pos] = '┤';

    // Draw IQR box
    let q1_pos = scale(q1).min(width - 1);
    let q3_pos = scale(q3).min(width - 1);
    for i in q1_pos..=q3_pos {
        line[i] = '─';
    }
    line[q1_pos] = '┌';
    line[q3_pos] = '┐';

    // Draw median
    let med_pos = scale(median).min(width - 1);
    line[med_pos] = '┃';

    // Draw whisker lines
    for i in 1..q1_pos {
        line[i] = '─';
    }
    for i in (q3_pos + 1)..max_pos {
        line[i] = '─';
    }

    let mut result = String::new();
    result.push_str("Box Plot:\n");
    result.push_str(&line.iter().collect::<String>());
    result.push('\n');
    result.push_str(&format!("{:<width$}{:>width$}\n", min, max, width = width / 2));
    result.push_str(&format!("Min={}, Q1={}, Median={}, Q3={}, Max={}", min, q1, median, q3, max));

    result
}

/// Render a sparkline (compact inline histogram).
pub fn sparkline(sizes: &[usize], width: usize) -> String {
    if sizes.is_empty() {
        return String::new();
    }

    let chars = ['▁', '▂', '▃', '▄', '▅', '▆', '▇', '█'];
    let min = *sizes.iter().min().unwrap();
    let max = *sizes.iter().max().unwrap();

    if min == max {
        return chars[4].to_string().repeat(width.min(sizes.len()));
    }

    // Bin the data
    let bin_size = (sizes.len() + width - 1) / width;
    let mut bins = Vec::new();

    for chunk in sizes.chunks(bin_size) {
        let avg = chunk.iter().sum::<usize>() as f64 / chunk.len() as f64;
        bins.push(avg);
    }

    let bin_min = bins.iter().cloned().fold(f64::INFINITY, f64::min);
    let bin_max = bins.iter().cloned().fold(f64::NEG_INFINITY, f64::max);
    let range = bin_max - bin_min;

    bins.iter()
        .map(|&v| {
            let idx = if range > 0.0 {
                ((v - bin_min) / range * (chars.len() - 1) as f64) as usize
            } else {
                chars.len() / 2
            };
            chars[idx.min(chars.len() - 1)]
        })
        .collect()
}

/// Progress bar for long-running operations.
pub struct ProgressBar {
    total: usize,
    current: usize,
    width: usize,
    prefix: String,
}

impl ProgressBar {
    /// Create a new progress bar.
    pub fn new(total: usize, prefix: &str) -> Self {
        Self {
            total,
            current: 0,
            width: 40,
            prefix: prefix.to_string(),
        }
    }

    /// Update the progress.
    pub fn update(&mut self, current: usize) {
        self.current = current;
    }

    /// Increment by one.
    pub fn inc(&mut self) {
        self.current += 1;
    }

    /// Render the progress bar.
    pub fn render(&self) -> String {
        let progress = self.current as f64 / self.total as f64;
        let filled = (progress * self.width as f64) as usize;
        let empty = self.width - filled;

        format!(
            "\r{} [{}{}] {}/{} ({:.1}%)",
            self.prefix,
            "█".repeat(filled),
            "░".repeat(empty),
            self.current,
            self.total,
            progress * 100.0
        )
    }

    /// Check if complete.
    pub fn is_done(&self) -> bool {
        self.current >= self.total
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_histogram_render() {
        let sizes: Vec<usize> = (1..=20).collect();
        let config = HistogramConfig::default();
        let output = render_histogram(&sizes, &config);
        assert!(output.contains("BDD Size Distribution"));
    }

    #[test]
    fn test_sparkline() {
        let sizes = vec![1, 2, 3, 4, 5, 4, 3, 2, 1];
        let spark = sparkline(&sizes, 9);
        assert_eq!(spark.chars().count(), 9);
    }

    #[test]
    fn test_progress_bar() {
        let mut pb = ProgressBar::new(100, "Testing");
        pb.update(50);
        let output = pb.render();
        assert!(output.contains("50/100"));
        assert!(output.contains("50.0%"));
    }
}
