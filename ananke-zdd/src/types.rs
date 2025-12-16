use std::fmt;

/// A node identifier (index into the node storage array).
///
/// `NodeId` is a type-safe wrapper around `u32` that represents an index
/// into the ZDD manager's node storage.
///
/// # Invariants
///
/// - `NodeId(0)` is the ZERO terminal (⊥, empty family)
/// - `NodeId(1)` is the ONE terminal (⊤, family containing empty set)
/// - Decision nodes start at index 2
#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash)]
pub struct NodeId(u32);

impl NodeId {
    /// The ZERO terminal node (empty family).
    pub const ZERO: NodeId = NodeId(0);

    /// The ONE terminal node (family containing empty set).
    pub const ONE: NodeId = NodeId(1);

    /// Sentinel value for invalid/uninitialized node references.
    pub const INVALID: NodeId = NodeId(0xFFFF_FFFF);

    /// Creates a new NodeId from a raw index.
    pub const fn new(index: u32) -> Self {
        NodeId(index)
    }

    /// Returns the raw value.
    pub const fn raw(self) -> u32 {
        self.0
    }

    /// Returns the node index as a `usize` for array indexing.
    pub const fn index(self) -> usize {
        self.0 as usize
    }

    /// Returns true if this is a terminal node (ZERO or ONE).
    pub const fn is_terminal(self) -> bool {
        self.0 <= 1
    }

    /// Returns true if this is the ZERO terminal.
    pub const fn is_zero(self) -> bool {
        self.0 == 0
    }

    /// Returns true if this is the ONE terminal.
    pub const fn is_one(self) -> bool {
        self.0 == 1
    }
}

impl fmt::Display for NodeId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.0 {
            0 => write!(f, "⊥"),
            1 => write!(f, "⊤"),
            _ => write!(f, "@{}", self.0),
        }
    }
}

impl From<u32> for NodeId {
    fn from(index: u32) -> Self {
        NodeId::new(index)
    }
}

impl From<NodeId> for u32 {
    fn from(id: NodeId) -> Self {
        id.0
    }
}

impl From<NodeId> for usize {
    fn from(id: NodeId) -> Self {
        id.0 as usize
    }
}

/// A variable identifier (1-indexed).
///
/// Variables represent elements that can be members of sets.
/// Variable IDs are 1-indexed (0 is reserved).
#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash, PartialOrd, Ord)]
pub struct Var(u32);

impl Var {
    /// Special zero value (reserved, not a valid variable).
    pub const ZERO: Var = Var(0);

    /// Creates a new variable with the given ID.
    ///
    /// # Panics
    ///
    /// Panics in debug mode if `id == 0`.
    pub const fn new(id: u32) -> Self {
        debug_assert!(id > 0, "Variable IDs must be >= 1");
        Var(id)
    }

    /// Returns the raw variable ID.
    pub const fn id(self) -> u32 {
        self.0
    }

    /// Creates a variable from raw ID without checking.
    pub const unsafe fn from_raw_unchecked(id: u32) -> Self {
        Var(id)
    }

    /// Returns true if this is the reserved zero variable.
    pub const fn is_zero(self) -> bool {
        self.0 == 0
    }
}

impl fmt::Display for Var {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "x{}", self.0)
    }
}

impl From<u32> for Var {
    fn from(id: u32) -> Self {
        Var::new(id)
    }
}

impl From<Var> for u32 {
    fn from(v: Var) -> Self {
        v.0
    }
}

/// A level in the variable ordering (0 = top).
#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash, PartialOrd, Ord)]
pub struct Level(u32);

impl Level {
    /// Creates a new level.
    pub const fn new(level: u32) -> Self {
        Level(level)
    }

    /// Returns the raw level value.
    pub const fn raw(self) -> u32 {
        self.0
    }

    /// Returns the level as usize for indexing.
    pub const fn index(self) -> usize {
        self.0 as usize
    }
}

impl fmt::Display for Level {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "L{}", self.0)
    }
}

impl From<u32> for Level {
    fn from(level: u32) -> Self {
        Level::new(level)
    }
}

impl From<usize> for Level {
    fn from(level: usize) -> Self {
        Level::new(level as u32)
    }
}
