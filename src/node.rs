use crate::reference::Ref;
use crate::types::Var;
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
    /// Next node in collision chain. `0` means end of chain.
    pub next: u32,
    /// Precomputed hash of (variable, low, high) for fast comparisons.
    hash: u64,
}

impl Default for Node {
    fn default() -> Self {
        Self {
            variable: Var::ZERO,
            low: Ref::ZERO,
            high: Ref::ZERO,
            next: 0,
            hash: 0,
        }
    }
}

impl Node {
    /// Creates a new node with the given variable and children.
    ///
    /// The `next` pointer is initialized to `0` (end of chain).
    pub fn new(variable: Var, low: Ref, high: Ref) -> Self {
        let hash = {
            let x = variable.id() as u64;
            let y = MyHash::hash(&low);
            let z = MyHash::hash(&high);
            MyHash::hash(&(y, z, x))
        };
        Self {
            variable,
            low,
            high,
            next: 0,
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
        self.variable == other.variable && self.low == other.low && self.high == other.high
    }
}

impl Eq for Node {}
