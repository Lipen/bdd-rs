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
///
/// # Structure
///
/// Each node represents a Shannon decomposition:
/// ```text
/// f = (¬v ∧ f_low) ∨ (v ∧ f_high)
/// ```
///
/// Nodes are stored in per-level subtables, where each subtable contains
/// all nodes for a specific variable level. This enables efficient variable
/// reordering by swapping subtables directly, without forwarding pointers.
#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub struct Node {
    pub variable: Var,
    pub low: Ref,
    pub high: Ref,
}

impl Default for Node {
    fn default() -> Self {
        Self {
            variable: Var::ZERO,
            low: Ref::ZERO,
            high: Ref::ZERO,
        }
    }
}

impl MyHash for Node {
    fn hash(&self) -> u64 {
        let x = self.variable.id() as u64;
        let y = MyHash::hash(&self.low);
        let z = MyHash::hash(&self.high);
        MyHash::hash(&(y, z, x))
    }
}

impl Node {
    /// Creates a new node with the given variable and children.
    pub fn new(variable: Var, low: Ref, high: Ref) -> Self {
        Self { variable, low, high }
    }
}
