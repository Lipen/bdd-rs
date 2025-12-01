//! Boundary value analysis for test generation.
//!
//! Generates edge-case test values based on interval constraints.

use std::collections::{HashMap, HashSet};

use super::core::Witness;
use super::interval::Interval;

/// Boundary value generator for systematic edge case testing.
///
/// Generates test values at interval boundaries and other critical points
/// to maximize bug-finding potential.
///
/// # Strategies
///
/// - **Off-by-one**: Values at `min-1`, `min+1`, `max-1`, `max+1`
/// - **Special values**: `0`, `-1`, `1`, extreme values
/// - **Powers of two**: `1, 2, 4, 8, ...` (useful for bit-level bugs)
///
/// # Example
///
/// ```rust
/// use tbdd_pbt::theory::BoundaryValueGenerator;
/// use tbdd_pbt::theory::Interval;
///
/// let generator = BoundaryValueGenerator::new();
/// let interval = Interval::new(0, 100);
/// let values = generator.generate(&interval);
///
/// assert!(values.contains(&0));    // min
/// assert!(values.contains(&100));  // max
/// assert!(values.contains(&50));   // midpoint
/// ```
#[derive(Debug, Clone)]
pub struct BoundaryValueGenerator {
    /// Include off-by-one values.
    pub off_by_one: bool,
    /// Include special values (0, -1, MAX, MIN).
    pub special_values: bool,
    /// Include powers of 2 boundaries.
    pub powers_of_two: bool,
}

impl Default for BoundaryValueGenerator {
    fn default() -> Self {
        Self {
            off_by_one: true,
            special_values: true,
            powers_of_two: false,
        }
    }
}

impl BoundaryValueGenerator {
    /// Create a generator with default settings.
    pub fn new() -> Self {
        Self::default()
    }

    /// Enable all boundary value strategies.
    pub fn all() -> Self {
        Self {
            off_by_one: true,
            special_values: true,
            powers_of_two: true,
        }
    }

    /// Generate boundary values for an interval.
    pub fn generate(&self, interval: &Interval) -> Vec<i64> {
        let mut values = Vec::new();

        if interval.is_empty() {
            return values;
        }

        // Core boundaries
        values.push(interval.min);
        values.push(interval.max);

        // Midpoint
        let mid = interval.min.saturating_add(interval.max) / 2;
        if mid != interval.min && mid != interval.max {
            values.push(mid);
        }

        // Off-by-one
        if self.off_by_one {
            if interval.min > i64::MIN / 2 {
                values.push(interval.min.saturating_sub(1));
            }
            if interval.max < i64::MAX / 2 {
                values.push(interval.max.saturating_add(1));
            }
            if interval.min < interval.max {
                values.push(interval.min.saturating_add(1));
                values.push(interval.max.saturating_sub(1));
            }
        }

        // Special values
        if self.special_values {
            for special in [0, -1, 1, i64::MAX / 2, i64::MIN / 2] {
                if special >= interval.min && special <= interval.max {
                    values.push(special);
                }
            }
        }

        // Powers of 2
        if self.powers_of_two {
            for exp in 0..62 {
                let pow = 1i64 << exp;
                if pow >= interval.min && pow <= interval.max {
                    values.push(pow);
                }
                if -pow >= interval.min && -pow <= interval.max {
                    values.push(-pow);
                }
            }
        }

        // Remove duplicates and excluded value
        values.sort();
        values.dedup();
        if let Some(excluded) = interval.excluded {
            values.retain(|&v| v != excluded);
        }

        values
    }

    /// Generate boundary test cases for multiple variables.
    pub fn generate_test_cases(&self, intervals: &HashMap<String, Interval>) -> Vec<Witness> {
        if intervals.is_empty() {
            return vec![Witness::new()];
        }

        // Generate boundary values for each variable
        let var_values: Vec<(String, Vec<i64>)> = intervals
            .iter()
            .map(|(var, interval)| (var.clone(), self.generate(interval)))
            .collect();

        // For each variable, pick boundary combinations
        // Use representative sampling to avoid explosion
        let mut test_cases = Vec::new();

        // Add corner cases: all mins, all maxs, all mids
        let mut all_min = Witness::new();
        let mut all_max = Witness::new();
        let mut all_mid = Witness::new();

        for (var, values) in &var_values {
            if !values.is_empty() {
                all_min.values.insert(var.clone(), values[0]);
                all_max.values.insert(var.clone(), *values.last().unwrap());
                all_mid.values.insert(var.clone(), values[values.len() / 2]);
            }
        }

        test_cases.push(all_min);
        test_cases.push(all_max);
        test_cases.push(all_mid);

        // Add single-variable boundary variations
        for (var, values) in &var_values {
            for &val in values.iter().take(5) {
                // Limit per variable
                let mut witness = Witness::new();
                for (v, vals) in &var_values {
                    let base_val = vals.get(vals.len() / 2).copied().unwrap_or(0);
                    witness.values.insert(v.clone(), if v == var { val } else { base_val });
                }
                test_cases.push(witness);
            }
        }

        // Deduplicate
        let mut seen = HashSet::new();
        test_cases.retain(|w| {
            let key: Vec<_> = w.values.iter().collect();
            seen.insert(format!("{:?}", key))
        });

        test_cases
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn basic_generation() {
        let generator = BoundaryValueGenerator::new();
        let interval = Interval::new(0, 100);
        let values = generator.generate(&interval);

        // Should include min, max, and midpoint at minimum
        assert!(values.contains(&0));
        assert!(values.contains(&100));
        assert!(values.contains(&50));
    }

    #[test]
    fn off_by_one_values() {
        let generator = BoundaryValueGenerator::new();
        let interval = Interval::new(10, 20);
        let values = generator.generate(&interval);

        // Should include off-by-one values
        assert!(values.contains(&9)); // min - 1
        assert!(values.contains(&11)); // min + 1
        assert!(values.contains(&19)); // max - 1
        assert!(values.contains(&21)); // max + 1
    }

    #[test]
    fn special_values() {
        let generator = BoundaryValueGenerator::new();
        let interval = Interval::new(-10, 10);
        let values = generator.generate(&interval);

        // Should include special values like 0, -1, 1
        assert!(values.contains(&0));
        assert!(values.contains(&-1));
        assert!(values.contains(&1));
    }

    #[test]
    fn powers_of_two() {
        let generator = BoundaryValueGenerator::all();
        let interval = Interval::new(0, 100);
        let values = generator.generate(&interval);

        // With powers_of_two enabled
        assert!(values.contains(&1));
        assert!(values.contains(&2));
        assert!(values.contains(&4));
        assert!(values.contains(&8));
        assert!(values.contains(&16));
        assert!(values.contains(&32));
        assert!(values.contains(&64));
    }

    #[test]
    fn excluded_value() {
        let generator = BoundaryValueGenerator::new();
        let mut interval = Interval::new(0, 10);
        interval.excluded = Some(5);
        let values = generator.generate(&interval);

        // Should not include excluded value
        assert!(!values.contains(&5));
    }

    #[test]
    fn empty_interval() {
        let generator = BoundaryValueGenerator::new();
        let interval = Interval::new(10, 5); // Empty
        let values = generator.generate(&interval);

        assert!(values.is_empty());
    }

    #[test]
    fn single_point_interval() {
        let generator = BoundaryValueGenerator::new();
        let interval = Interval::new(42, 42);
        let values = generator.generate(&interval);

        assert!(values.contains(&42));
    }

    #[test]
    fn test_cases_generation() {
        let generator = BoundaryValueGenerator::new();
        let mut intervals = HashMap::new();
        intervals.insert("x".to_string(), Interval::new(0, 10));
        intervals.insert("y".to_string(), Interval::new(-5, 5));

        let test_cases = generator.generate_test_cases(&intervals);

        // Should generate multiple test cases
        assert!(!test_cases.is_empty());

        // Each test case should have both variables
        for tc in &test_cases {
            assert!(tc.values.contains_key("x"));
            assert!(tc.values.contains_key("y"));
        }
    }
}
