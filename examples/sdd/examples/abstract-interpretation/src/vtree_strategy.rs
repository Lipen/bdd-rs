//! VTree strategies for structuring SDD decomposition
//!
//! The vtree determines how SDDs decompose Boolean functions.
//! Different strategies suit different problem structures.

use crate::language::Var;

/// VTree strategy selection
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum VtreeStrategy {
    /// Balanced binary tree - symmetric, general-purpose
    Balanced,
    /// Right-linear: x1, (x2, (x3, x4...)) - variable order matters
    RightLinear,
    /// Left-linear: ((x1, x2), (x3, x4)) - opposite structure
    LeftLinear,
    /// Syntactic: Based on variable appearance order in program
    Syntactic,
    /// Semantic: Cluster variables based on predicate dependencies
    Semantic,
}

impl VtreeStrategy {
    /// Order variables according to strategy
    pub fn order_variables(&self, vars: &[Var]) -> Vec<Var> {
        let mut ordered = vars.to_vec();

        match self {
            VtreeStrategy::Balanced => {
                // Already sorted by default
                ordered.sort_unstable();
            }
            VtreeStrategy::RightLinear => {
                // Sort in increasing order (right-linear)
                ordered.sort_unstable();
            }
            VtreeStrategy::LeftLinear => {
                // Sort in reverse order
                ordered.sort_unstable();
                ordered.reverse();
            }
            VtreeStrategy::Syntactic => {
                // Keep order as given (program appearance order)
                // Already in order from program_vars()
            }
            VtreeStrategy::Semantic => {
                // For semantic, we'd need dependency analysis
                // For now, approximate with sorted order
                ordered.sort_unstable();
            }
        }

        ordered
    }

    /// Get a human-readable description
    pub fn description(&self) -> &'static str {
        match self {
            VtreeStrategy::Balanced => "Balanced vtree: Symmetric binary tree, general-purpose",
            VtreeStrategy::RightLinear => "Right-linear vtree: Sequential left-skewed tree",
            VtreeStrategy::LeftLinear => "Left-linear vtree: Sequential right-skewed tree",
            VtreeStrategy::Syntactic => "Syntactic vtree: Based on program variable order",
            VtreeStrategy::Semantic => "Semantic vtree: Based on predicate variable dependencies",
        }
    }
}

impl std::fmt::Display for VtreeStrategy {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            VtreeStrategy::Balanced => write!(f, "Balanced"),
            VtreeStrategy::RightLinear => write!(f, "RightLinear"),
            VtreeStrategy::LeftLinear => write!(f, "LeftLinear"),
            VtreeStrategy::Syntactic => write!(f, "Syntactic"),
            VtreeStrategy::Semantic => write!(f, "Semantic"),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_vtree_strategies() {
        let vars = vec![Var::new(3), Var::new(1), Var::new(2)];

        let balanced = VtreeStrategy::Balanced.order_variables(&vars);
        assert_eq!(balanced, vec![Var::new(1), Var::new(2), Var::new(3)]);

        let right_linear = VtreeStrategy::RightLinear.order_variables(&vars);
        assert_eq!(right_linear, vec![Var::new(1), Var::new(2), Var::new(3)]);

        let left_linear = VtreeStrategy::LeftLinear.order_variables(&vars);
        assert_eq!(left_linear, vec![Var::new(3), Var::new(2), Var::new(1)]);
    }
}
