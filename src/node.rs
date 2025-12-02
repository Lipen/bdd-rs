use crate::reference::Ref;
use crate::types::{NodeId, Var};
use crate::utils::MyHash;

/// A BDD node representing a decision point in the diagram.
///
/// # Fields
///
/// - `variable`: Variable ID (1-indexed, 0 for terminals)
/// - `low`: Low child (followed when variable is false)
/// - `high`: High child (followed when variable is true)
/// - `next`: Next node in hash collision chain (intrusive linked list)
///
/// # Structure
///
/// Each node represents a Shannon decomposition:
/// ```text
/// f = (¬v ∧ f_low) ∨ (v ∧ f_high)
/// ```
///
/// Nodes are stored in per-level subtables, where each subtable contains
/// all nodes for a specific variable level. The `next` field implements
/// collision chaining for the hash table, following CUDD's intrusive design.
///
/// # Memory Layout
///
/// ```text
/// +----------+-----+------+------+
/// | variable | low | high | next |
/// +----------+-----+------+------+
///     4B       4B    4B     4B    = 16 bytes total
/// ```
#[derive(Debug, Copy, Clone)]
pub struct Node {
    pub variable: Var,
    pub low: Ref,
    pub high: Ref,
    /// Next node in collision chain. [`NO_NEXT`][Node::NO_NEXT] means end of chain.
    pub next: NodeId,
    /// Precomputed hash of `(variable, low, high)` for fast comparisons.
    hash: u64,
}

impl Default for Node {
    fn default() -> Self {
        Self {
            variable: Var::ZERO,
            low: Ref::INVALID,
            high: Ref::INVALID,
            next: Self::NO_NEXT,
            hash: 0,
        }
    }
}

impl Node {
    /// Sentinel value for end of hash collision chain.
    pub const NO_NEXT: NodeId = NodeId::INVALID;

    /// Creates a new node with the given variable and children.
    ///
    /// The `next` pointer is initialized to `NO_NEXT` (end of chain).
    pub fn new(variable: Var, low: Ref, high: Ref) -> Self {
        let hash = MyHash::hash(&(variable, low, high));
        Self {
            variable,
            low,
            high,
            next: Self::NO_NEXT,
            hash,
        }
    }
}

impl MyHash for Node {
    fn hash(&self) -> u64 {
        self.hash
    }
}

impl PartialEq for Node {
    fn eq(&self, other: &Self) -> bool {
        self.hash == other.hash && self.variable == other.variable && self.low == other.low && self.high == other.high
    }
}

impl Eq for Node {}
