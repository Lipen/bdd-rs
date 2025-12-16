use crate::reference::ZddId;
use crate::types::{NodeId, Var};

/// A ZDD node representing a decision point in the diagram.
///
/// # Fields
///
/// - `var`: Variable (element) at this decision point (1-indexed)
/// - `lo`: Low child — sets NOT containing this variable
/// - `hi`: High child — sets containing this variable (with variable removed)
/// - `next`: Next node in hash collision chain
///
/// # Invariant
///
/// **Zero-suppression rule**: `hi` is NEVER `ZddId::ZERO`.
/// Nodes where `hi = ⊥` are eliminated (replaced by `lo`).
///
/// # Semantics
///
/// A ZDD node represents the family:
/// ```text
/// F(node) = F(lo) ∪ {S ∪ {var} | S ∈ F(hi)}
/// ```
///
/// - `lo` branch: sets that don't contain `var`
/// - `hi` branch: sets that contain `var` (stored without `var`)
#[derive(Debug, Copy, Clone)]
pub struct ZddNode {
    /// Decision variable (element that may or may not be in the set).
    pub var: Var,
    /// Low child: sets NOT containing var.
    pub lo: ZddId,
    /// High child: sets containing var (NEVER ZERO due to zero-suppression).
    pub hi: ZddId,
    /// Next node in collision chain for unique table.
    pub next: NodeId,
    /// Precomputed hash for efficient lookup.
    hash: u64,
}

impl Default for ZddNode {
    fn default() -> Self {
        Self {
            var: Var::ZERO,
            lo: ZddId::INVALID,
            hi: ZddId::INVALID,
            next: Self::NO_NEXT,
            hash: 0,
        }
    }
}

impl ZddNode {
    /// Sentinel value for end of hash collision chain.
    pub const NO_NEXT: NodeId = NodeId::INVALID;

    /// Creates a new ZDD node.
    ///
    /// # Panics
    ///
    /// Debug-panics if `hi == ZddId::ZERO` (violates zero-suppression).
    pub fn new(var: Var, lo: ZddId, hi: ZddId) -> Self {
        debug_assert!(!hi.is_zero(), "ZDD node cannot have hi=ZERO (zero-suppression rule)");
        let hash = Self::compute_hash(var, lo, hi);
        Self {
            var,
            lo,
            hi,
            next: Self::NO_NEXT,
            hash,
        }
    }

    /// Computes hash from (var, lo, hi).
    fn compute_hash(var: Var, lo: ZddId, hi: ZddId) -> u64 {
        use std::hash::{Hash, Hasher};
        let mut hasher = std::collections::hash_map::DefaultHasher::new();
        var.id().hash(&mut hasher);
        lo.raw().hash(&mut hasher);
        hi.raw().hash(&mut hasher);
        hasher.finish()
    }

    /// Returns the precomputed hash.
    pub fn hash(&self) -> u64 {
        self.hash
    }
}

impl PartialEq for ZddNode {
    fn eq(&self, other: &Self) -> bool {
        self.hash == other.hash && self.var == other.var && self.lo == other.lo && self.hi == other.hi
    }
}

impl Eq for ZddNode {}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_node_creation() {
        let node = ZddNode::new(Var::new(1), ZddId::ZERO, ZddId::ONE);
        assert_eq!(node.var, Var::new(1));
        assert_eq!(node.lo, ZddId::ZERO);
        assert_eq!(node.hi, ZddId::ONE);
    }

    #[test]
    fn test_node_equality() {
        let n1 = ZddNode::new(Var::new(1), ZddId::ZERO, ZddId::ONE);
        let n2 = ZddNode::new(Var::new(1), ZddId::ZERO, ZddId::ONE);
        let n3 = ZddNode::new(Var::new(2), ZddId::ZERO, ZddId::ONE);

        assert_eq!(n1, n2);
        assert_ne!(n1, n3);
    }
}
