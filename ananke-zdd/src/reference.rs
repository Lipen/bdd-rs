use std::fmt::{Display, Formatter};

use crate::types::NodeId;

/// A reference to a ZDD node.
///
/// Unlike BDD's `Ref`, ZDDs don't use complement edges, so `ZddId` is
/// simply a node index wrapper.
///
/// # Terminal Values
///
/// - `ZddId::ZERO` (⊥) — Empty family: no sets
/// - `ZddId::ONE` (⊤) — Family containing only the empty set: {∅}
#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash)]
#[repr(transparent)]
pub struct ZddId(u32);

impl ZddId {
    /// Empty family (⊥): contains no sets.
    pub const ZERO: ZddId = ZddId(0);

    /// Family containing only empty set (⊤): {∅}.
    pub const ONE: ZddId = ZddId(1);

    /// Sentinel for invalid references.
    pub const INVALID: ZddId = ZddId(0xFFFF_FFFF);

    /// Creates a ZddId from a NodeId.
    pub const fn from_node(id: NodeId) -> Self {
        ZddId(id.raw())
    }

    /// Creates a ZddId from a raw index.
    pub const fn new(index: u32) -> Self {
        ZddId(index)
    }

    /// Returns the underlying NodeId.
    pub const fn node_id(self) -> NodeId {
        NodeId::new(self.0)
    }

    /// Returns the raw index value.
    pub const fn raw(self) -> u32 {
        self.0
    }

    /// Returns the index for array access.
    pub const fn index(self) -> usize {
        self.0 as usize
    }

    /// Returns true if this is a terminal (ZERO or ONE).
    pub const fn is_terminal(self) -> bool {
        self.0 <= 1
    }

    /// Returns true if this is the empty family.
    pub const fn is_zero(self) -> bool {
        self.0 == 0
    }

    /// Returns true if this is the {∅} family.
    pub const fn is_one(self) -> bool {
        self.0 == 1
    }
}

impl Default for ZddId {
    fn default() -> Self {
        ZddId::INVALID
    }
}

impl Display for ZddId {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self.0 {
            0 => write!(f, "⊥"),
            1 => write!(f, "⊤"),
            _ => write!(f, "#{}", self.0),
        }
    }
}

impl From<NodeId> for ZddId {
    fn from(id: NodeId) -> Self {
        ZddId::from_node(id)
    }
}

impl From<ZddId> for NodeId {
    fn from(id: ZddId) -> Self {
        id.node_id()
    }
}

impl From<u32> for ZddId {
    fn from(index: u32) -> Self {
        ZddId::new(index)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_terminals() {
        assert!(ZddId::ZERO.is_zero());
        assert!(ZddId::ZERO.is_terminal());
        assert!(!ZddId::ZERO.is_one());

        assert!(ZddId::ONE.is_one());
        assert!(ZddId::ONE.is_terminal());
        assert!(!ZddId::ONE.is_zero());
    }

    #[test]
    fn test_non_terminal() {
        let id = ZddId::new(42);
        assert!(!id.is_terminal());
        assert!(!id.is_zero());
        assert!(!id.is_one());
        assert_eq!(id.raw(), 42);
    }

    #[test]
    fn test_display() {
        assert_eq!(format!("{}", ZddId::ZERO), "⊥");
        assert_eq!(format!("{}", ZddId::ONE), "⊤");
        assert_eq!(format!("{}", ZddId::new(42)), "#42");
    }
}
