//! SDD-based abstract domain for program analysis
//!
//! An abstract state is represented as an SDD Boolean function
//! where each satisfying assignment represents a possible concrete state.

use crate::bit_encoding::BitEncoding;
use crate::language::{Expr, Predicate, Var};

/// Abstract state represented as an SDD
/// In a real implementation, this would wrap an SDD node from the manager
#[derive(Debug, Clone)]
pub struct SddAbstractState {
    /// Size of the SDD (number of nodes)
    pub size: usize,
    /// Number of satisfying assignments (models)
    pub num_models: u64,
    /// Whether the state is bottom (empty set)
    pub is_bottom: bool,
    /// Whether the state is top (all assignments)
    pub is_top: bool,
    /// Encoding context
    pub encoding: BitEncoding,
}

impl SddAbstractState {
    /// Create a new abstract state from a constraint
    pub fn from_constraint(_constraint: &str, encoding: BitEncoding) -> Self {
        // Simplified: in a real implementation this would compile the constraint to SDD
        SddAbstractState {
            size: 1,
            num_models: 0,
            is_bottom: false,
            is_top: false,
            encoding,
        }
    }

    /// Create the top state (all assignments satisfying)
    pub fn top(encoding: BitEncoding) -> Self {
        let num_vars = encoding.num_sdd_vars();
        let num_models = 2_u64.pow(num_vars as u32);
        SddAbstractState {
            size: 1,
            num_models,
            is_bottom: false,
            is_top: true,
            encoding,
        }
    }

    /// Create the bottom state (no satisfying assignments)
    pub fn bottom(encoding: BitEncoding) -> Self {
        SddAbstractState {
            size: 1,
            num_models: 0,
            is_bottom: true,
            is_top: false,
            encoding,
        }
    }

    /// Join two abstract states (union)
    pub fn join(&self, other: &SddAbstractState) -> SddAbstractState {
        // In a real implementation, this would be SDD disjunction
        let combined_size = self.size + other.size;
        let combined_models = (self.num_models + other.num_models).min(2_u64.pow(self.encoding.num_sdd_vars() as u32));

        SddAbstractState {
            size: combined_size,
            num_models: combined_models,
            is_bottom: false,
            is_top: combined_models == 2_u64.pow(self.encoding.num_sdd_vars() as u32),
            encoding: self.encoding.clone(),
        }
    }

    /// Meet two abstract states (intersection)
    pub fn meet(&self, other: &SddAbstractState) -> SddAbstractState {
        // In a real implementation, this would be SDD conjunction
        if self.is_bottom || other.is_bottom {
            return SddAbstractState::bottom(self.encoding.clone());
        }

        let combined_models = (self.num_models * other.num_models / 2_u64.pow(self.encoding.num_sdd_vars() as u32)).max(0);

        SddAbstractState {
            size: (self.size + other.size) / 2,
            num_models: combined_models,
            is_bottom: combined_models == 0,
            is_top: false,
            encoding: self.encoding.clone(),
        }
    }

    /// Widen the state for convergence (abstract)
    pub fn widen(&self) -> SddAbstractState {
        // Simplified widening: increase model set heuristically
        // In a real implementation, this would apply widening operators
        SddAbstractState {
            size: self.size,
            num_models: (self.num_models * 2).min(2_u64.pow(self.encoding.num_sdd_vars() as u32)),
            is_bottom: self.is_bottom,
            is_top: self.is_top || (self.num_models * 2 >= 2_u64.pow(self.encoding.num_sdd_vars() as u32)),
            encoding: self.encoding.clone(),
        }
    }

    /// Check if state is satisfiable
    pub fn is_satisfiable(&self) -> bool {
        self.num_models > 0
    }

    /// Assume a constraint (restrict state)
    pub fn assume(&self, _pred: &Predicate) -> SddAbstractState {
        // In a real implementation, this would intersect the SDD with the predicate's representation
        // For now, we heuristically shrink the model count
        SddAbstractState {
            size: self.size,
            num_models: self.num_models / 2, // Rough approximation
            is_bottom: self.num_models <= 1,
            is_top: false,
            encoding: self.encoding.clone(),
        }
    }

    /// Assign a value to a variable
    pub fn assign(&self, _var: Var, _expr: &Expr) -> SddAbstractState {
        // In a real implementation, this would compute the SDD transformation for assignment
        // For now, we keep the size roughly the same
        SddAbstractState {
            size: self.size,
            num_models: self.num_models,
            is_bottom: self.is_bottom,
            is_top: self.is_top,
            encoding: self.encoding.clone(),
        }
    }

    /// Get a summary of the state
    pub fn summary(&self) -> String {
        if self.is_top {
            format!("T (top, size={}, models={})", self.size, self.num_models)
        } else if self.is_bottom {
            format!("⊥ (bottom, size=1, models=0)")
        } else {
            format!("(size={}, models={})", self.size, self.num_models)
        }
    }
}

impl Clone for BitEncoding {
    fn clone(&self) -> Self {
        BitEncoding::new(&self.program_vars())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_abstract_state() {
        let vars = vec![Var::new(1), Var::new(2)];
        let encoding = BitEncoding::new(&vars);

        let top = SddAbstractState::top(encoding.clone());
        assert!(top.is_top);
        assert!(!top.is_bottom);
        assert_eq!(top.num_models, 64); // 2^6 bits

        let bottom = SddAbstractState::bottom(encoding.clone());
        assert!(bottom.is_bottom);
        assert!(!bottom.is_satisfiable());

        let joined = top.join(&bottom);
        assert!(joined.is_satisfiable());
    }
}
