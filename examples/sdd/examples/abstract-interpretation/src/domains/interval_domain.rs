//! Interval abstract domain for comparison with SDD
//!
//! Simple interval domain: tracks [min, max] for each variable

use std::collections::HashMap;

use crate::language::Var;

/// Abstract state using interval domain
#[derive(Debug, Clone)]
pub struct IntervalDomain {
    intervals: HashMap<Var, (i32, i32)>,
}

impl IntervalDomain {
    /// Create top state (unrestricted intervals)
    pub fn top() -> Self {
        IntervalDomain { intervals: HashMap::new() }
    }

    /// Create bottom state (empty)
    pub fn bottom() -> Self {
        IntervalDomain {
            intervals: {
                let mut map = HashMap::new();
                // Mark as bottom with invalid interval
                map.insert(Var::new(1), (1, 0));
                map
            },
        }
    }

    /// Set interval for variable
    pub fn set_interval(&mut self, var: Var, min: i32, max: i32) {
        self.intervals.insert(var, (min, max));
    }

    /// Get interval for variable
    pub fn get_interval(&self, var: Var) -> Option<(i32, i32)> {
        self.intervals.get(&var).copied()
    }

    /// Check if bottom
    pub fn is_bottom(&self) -> bool {
        for &(min, max) in self.intervals.values() {
            if min > max {
                return true;
            }
        }
        false
    }

    /// Join two interval domains
    pub fn join(&self, other: &IntervalDomain) -> IntervalDomain {
        let mut result = IntervalDomain::top();

        let all_vars: std::collections::HashSet<_> = self.intervals.keys().chain(other.intervals.keys()).copied().collect();

        for var in all_vars {
            let (min1, max1) = self.intervals.get(&var).copied().unwrap_or((0, 7));
            let (min2, max2) = other.intervals.get(&var).copied().unwrap_or((0, 7));
            result.set_interval(var, min1.min(min2), max1.max(max2));
        }

        result
    }

    /// Size approximation (for comparison)
    pub fn approx_size(&self) -> usize {
        let mut size = 1;
        for &(min, max) in self.intervals.values() {
            size *= ((max - min + 1) as usize).max(1);
        }
        size
    }

    pub fn summary(&self) -> String {
        if self.is_bottom() {
            "⊥ (bottom)".to_string()
        } else if self.intervals.is_empty() {
            "T (top)".to_string()
        } else {
            let mut parts = Vec::new();
            let mut vars: Vec<_> = self.intervals.keys().collect();
            vars.sort();
            for var in vars {
                let (min, max) = self.intervals[var];
                parts.push(format!("{}∈[{},{}]", var, min, max));
            }
            parts.join(", ")
        }
    }
}
