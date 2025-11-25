use crate::reference::Ref;
use crate::types::Var;
use crate::utils::MyHash;

/// A BDD node with CUDD-style forwarding pointer for efficient reordering.
///
/// # Fields
///
/// - `variable`: Variable ID (1-indexed, 0 for terminals)
/// - `low`: Low child (followed when variable is false)
/// - `high`: High child (followed when variable is true)
/// - `next`: Forwarding pointer for in-place variable swap (Ref::ZERO if none)
///
/// # Forwarding Pointers
///
/// During variable reordering, nodes are transformed in-place. Instead of
/// updating all references to a node immediately, we set a forwarding pointer
/// (`next`) that points to the replacement node. Node access methods must
/// follow forwarding chains to get the actual node.
///
/// After garbage collection, forwarding chains are removed and nodes are compacted.
#[derive(Debug, Copy, Clone)]
pub struct Node {
    pub variable: Var,
    pub low: Ref,
    pub high: Ref,
    pub next: Ref,
}

// Custom PartialEq that ignores the `next` field (forwarding pointer)
// This is critical for the unique table to find existing nodes correctly
impl PartialEq for Node {
    fn eq(&self, other: &Self) -> bool {
        self.variable == other.variable && self.low == other.low && self.high == other.high
    }
}

impl Eq for Node {}

impl Default for Node {
    fn default() -> Self {
        Self {
            variable: Var::ZERO,
            low: Ref::ZERO,
            high: Ref::ZERO,
            next: Ref::ZERO,
        }
    }
}

impl MyHash for Node {
    fn hash(&self) -> u64 {
        let x = self.variable.id() as u64;
        let y = MyHash::hash(&self.low);
        let z = MyHash::hash(&self.high);
        // Note: 'next' is NOT part of hash (forwarding is temporary)
        MyHash::hash(&(y, z, x))
    }
}

impl Node {
    /// Creates a new node with the given variable and children.
    pub fn new(variable: Var, low: Ref, high: Ref) -> Self {
        Self {
            variable,
            low,
            high,
            next: Ref::ZERO,
        }
    }

    /// Checks if this node has a forwarding pointer.
    pub fn is_forwarded(&self) -> bool {
        self.next != Ref::ZERO
    }

    /// Returns the forwarding destination, or None if not forwarded.
    pub fn forwarding_dest(&self) -> Option<Ref> {
        if self.is_forwarded() {
            Some(self.next)
        } else {
            None
        }
    }

    /// Sets the forwarding pointer.
    pub fn set_forwarding(&mut self, dest: Ref) {
        self.next = dest;
    }

    /// Clears the forwarding pointer.
    pub fn clear_forwarding(&mut self) {
        self.next = Ref::ZERO;
    }
}
