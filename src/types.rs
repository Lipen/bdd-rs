///! Type-safe wrappers for BDD variables, levels, literals, and node IDs.
///!
///! This module provides newtype wrappers that enforce compile-time distinction
///! between variable IDs, level indices, and node IDs, preventing common mistakes
///! in BDD manipulation code.
use std::fmt;
use std::ops::Neg;

/// A node identifier (index into the node storage array).
///
/// `NodeId` is a type-safe wrapper around `u32` that represents an index
/// into the BDD manager's node storage. It prevents accidentally using
/// raw integers or other index types where a node ID is expected.
///
/// # Invariants
///
/// - `NodeId(0)` is the terminal node
/// - `NodeId::INVALID` (0x7FFF_FFFF) is a sentinel for uninitialized references
/// - Valid node IDs are in the range `0..0x7FFF_FFFF`
///
/// # Usage
///
/// `NodeId` is primarily obtained from [`Ref::index()`][crate::reference::Ref::index]
/// and used to index into the node storage via [`Bdd::node()`][crate::bdd::Bdd::node].
#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash)]
pub struct NodeId(u32);

impl NodeId {
    /// The terminal node (index 0).
    pub const TERMINAL: NodeId = NodeId(0);

    /// Sentinel value for invalid/uninitialized node references.
    pub const INVALID: NodeId = NodeId(0x7FFF_FFFF);

    /// Creates a new NodeId from a raw index.
    ///
    /// # Panics
    ///
    /// Panics if `index >= 0x7FFF_FFFF`.
    pub const fn new(index: u32) -> Self {
        debug_assert!(index < 0x7FFF_FFFF, "NodeId index is too large");
        NodeId(index)
    }

    /// Creates a NodeId from a raw index without checking.
    ///
    /// # Safety
    ///
    /// The caller must ensure that `index < 0x7FFF_FFFF`.
    pub const unsafe fn from_raw_unchecked(index: u32) -> Self {
        NodeId(index)
    }

    /// Returns the inner value of NodeId.
    pub const fn raw(self) -> u32 {
        self.0
    }

    /// Returns the node index as a `usize` for array indexing.
    pub const fn index(self) -> usize {
        self.0 as usize
    }

    /// Returns true if this is the terminal node.
    pub const fn is_terminal(self) -> bool {
        self.0 == 0
    }

    /// Returns true if this is the INVALID sentinel.
    pub const fn is_invalid(self) -> bool {
        self.0 == 0x7FFF_FFFF
    }
}

impl fmt::Display for NodeId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "@{}", self.0)
    }
}

impl From<u32> for NodeId {
    fn from(index: u32) -> Self {
        NodeId::new(index)
    }
}

// Into<u32>
impl From<NodeId> for u32 {
    fn from(id: NodeId) -> Self {
        id.0
    }
}

// Into<usize>
impl From<NodeId> for usize {
    fn from(id: NodeId) -> Self {
        id.0 as usize
    }
}

/// A variable identifier (1-indexed).
///
/// Variables represent Boolean decision points in a BDD. Unlike levels,
/// variable IDs are stable across reordering operations.
///
/// # Invariants
///
/// - Variable IDs must be >= 1 (0 is reserved for terminals)
/// - Variable IDs are independent of their position in the variable ordering
///
/// # Note on Ordering
///
/// `Var` does not implement `Ord` or `PartialOrd` because variable IDs
/// are not comparable in a meaningful way for BDD operations. To compare
/// variables according to the current ordering, use [`Bdd::var_precedes`][crate::bdd::Bdd::var_precedes]
/// or [`Bdd::top_variable`][crate::bdd::Bdd::top_variable].
#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash)]
pub struct Var(u32);

impl Var {
    /// Special zero value representing terminal nodes.
    ///
    /// This is the only valid `Var` with ID 0. It should only be used
    /// internally to mark terminal nodes in the BDD structure.
    pub const ZERO: Var = Var(0);

    /// Creates a new variable with the given ID.
    ///
    /// # Panics
    ///
    /// Panics if `id == 0`. Variables must be 1-indexed.
    /// Use `Var::ZERO` for terminal nodes.
    pub fn new(id: u32) -> Self {
        assert_ne!(id, 0, "Variable IDs must be >= 1 (use Var::ZERO for terminals)");
        Var(id)
    }

    /// Returns the raw variable ID as a `u32`.
    pub fn id(self) -> u32 {
        self.0
    }

    /// Creates a variable from a raw ID without checking.
    ///
    /// # Safety
    ///
    /// The caller must ensure that `id >= 1` or that they intend
    /// to create `Var::ZERO` for terminal nodes.
    pub const unsafe fn from_raw_unchecked(id: u32) -> Self {
        Var(id)
    }

    /// Returns true if this is the terminal marker (Var::ZERO).
    pub fn is_terminal(self) -> bool {
        self.0 == 0
    }

    /// Creates a positive literal from this variable.
    pub fn pos(self) -> Lit {
        Lit::pos(self)
    }

    /// Creates a negative literal from this variable.
    pub fn neg(self) -> Lit {
        Lit::neg(self)
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

/// A literal (possibly negated variable).
///
/// Literals are represented efficiently using a single `u32` where:
/// - The variable ID is stored in the upper 31 bits (shifted left by 1)
/// - The sign bit is stored in the LSB (0 = positive, 1 = negative)
///
/// This encoding allows for efficient storage and manipulation while
/// maintaining type safety.
///
/// # Examples
///
/// ```
/// use bdd_rs::types::{Var, Lit};
///
/// let x1 = Var::new(1);
///
/// // Create literals from variables
/// let pos_x1 = Lit::pos(x1);   // x₁
/// let neg_x1 = Lit::neg(x1);   // ¬x₁
///
/// // Or use the convenience methods
/// let pos_x1 = x1.pos();       // x₁
/// let neg_x1 = x1.neg();       // ¬x₁
///
/// // Negate literals
/// assert_eq!(-pos_x1, neg_x1);
/// assert_eq!(-neg_x1, pos_x1);
///
/// // Check properties
/// assert!(pos_x1.is_positive());
/// assert!(neg_x1.is_negative());
/// assert_eq!(pos_x1.var(), x1);
/// assert_eq!(neg_x1.var(), x1);
/// ```
#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash)]
pub struct Lit(u32);

impl Lit {
    /// Creates a positive literal from a variable.
    pub fn pos(var: Var) -> Self {
        debug_assert!(!var.is_terminal(), "Cannot create literal from terminal variable");
        Lit(var.0 << 1)
    }

    /// Creates a negative literal from a variable.
    pub fn neg(var: Var) -> Self {
        debug_assert!(!var.is_terminal(), "Cannot create literal from terminal variable");
        Lit((var.0 << 1) | 1)
    }

    /// Creates a literal from a signed integer (DIMACS-style).
    ///
    /// Positive integers create positive literals, negative integers
    /// create negative literals. Zero is not allowed.
    ///
    /// # Panics
    ///
    /// Panics if `value == 0`.
    pub fn from_dimacs(value: i32) -> Self {
        assert_ne!(value, 0, "Literal value cannot be zero");
        if value > 0 {
            Lit::pos(Var::new(value as u32))
        } else {
            Lit::neg(Var::new((-value) as u32))
        }
    }

    /// Returns the variable of this literal.
    pub fn var(self) -> Var {
        // Safety: We only create Lit from valid Var, so this is safe
        unsafe { Var::from_raw_unchecked(self.0 >> 1) }
    }

    /// Returns true if this literal is positive (not negated).
    pub fn is_positive(self) -> bool {
        (self.0 & 1) == 0
    }

    /// Returns true if this literal is negative (negated).
    pub fn is_negative(self) -> bool {
        (self.0 & 1) == 1
    }

    /// Returns the DIMACS-style signed integer representation.
    ///
    /// Positive literals return positive integers, negative literals
    /// return negative integers.
    pub fn to_dimacs(self) -> i32 {
        let var_id = (self.0 >> 1) as i32;
        if self.is_positive() {
            var_id
        } else {
            -var_id
        }
    }
}

impl Neg for Lit {
    type Output = Lit;

    fn neg(self) -> Self::Output {
        Lit(self.0 ^ 1)
    }
}

impl fmt::Display for Lit {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.is_negative() {
            write!(f, "¬x{}", self.var().id())
        } else {
            write!(f, "x{}", self.var().id())
        }
    }
}

impl From<i32> for Lit {
    fn from(value: i32) -> Self {
        Lit::from_dimacs(value)
    }
}

/// A level in the variable ordering (0-indexed).
///
/// Levels represent the position of a variable in the current ordering.
/// Unlike variable IDs, levels change when variables are reordered.
///
/// # Invariants
///
/// - Level 0 is the topmost level (closest to root)
/// - Levels increase downward toward terminals
/// - After reordering, the same variable may be at a different level
#[derive(Debug, Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub struct Level(usize);

impl Level {
    /// Creates a new level with the given index.
    pub fn new(index: usize) -> Self {
        Level(index)
    }

    /// Returns the raw level index as a `usize`.
    pub fn index(self) -> usize {
        self.0
    }

    /// Returns the next level down (index + 1).
    pub fn next(self) -> Self {
        Level(self.0 + 1)
    }

    /// Returns the previous level up (index - 1), or None if at level 0.
    pub fn prev(self) -> Option<Self> {
        if self.0 > 0 {
            Some(Level(self.0 - 1))
        } else {
            None
        }
    }

    /// Checks if this is the top level (level 0).
    pub fn is_top(self) -> bool {
        self.0 == 0
    }
}

impl fmt::Display for Level {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "L{}", self.0)
    }
}

impl From<usize> for Level {
    fn from(index: usize) -> Self {
        Level(index)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_var_creation() {
        let v1 = Var::new(1);
        let v2 = Var::new(2);
        assert_eq!(v1.id(), 1);
        assert_eq!(v2.id(), 2);
        // assert!(v1 < v2); // FORBIDDEN: Variables are incomparable!
    }

    #[test]
    #[should_panic(expected = "Variable IDs must be >= 1")]
    fn test_var_zero_panics() {
        Var::new(0);
    }

    #[test]
    fn test_var_zero_constant() {
        assert_eq!(Var::ZERO.id(), 0);
        assert!(Var::ZERO.is_terminal());
        assert!(!Var::new(1).is_terminal());
    }

    #[test]
    fn test_level_creation() {
        let l0 = Level::new(0);
        let l1 = Level::new(1);
        assert_eq!(l0.index(), 0);
        assert_eq!(l1.index(), 1);
        assert!(l0 < l1);
    }

    #[test]
    fn test_level_navigation() {
        let l0 = Level::new(0);
        let l1 = l0.next();
        let l2 = l1.next();
        assert_eq!(l0.prev(), None);
        assert_eq!(l1.prev(), Some(l0));
        assert_eq!(l2.prev(), Some(l1));
        assert!(l0.is_top());
        assert!(!l1.is_top());
        assert!(!l2.is_top());
    }

    #[test]
    fn test_lit_positive() {
        let x1 = Var::new(1);
        let lit = Lit::pos(x1);
        assert!(lit.is_positive());
        assert!(!lit.is_negative());
        assert_eq!(lit.var(), x1);
        assert_eq!(lit.to_dimacs(), 1);
    }

    #[test]
    fn test_lit_negative() {
        let x2 = Var::new(2);
        let lit = Lit::neg(x2);
        assert!(!lit.is_positive());
        assert!(lit.is_negative());
        assert_eq!(lit.var(), x2);
        assert_eq!(lit.to_dimacs(), -2);
    }

    #[test]
    fn test_lit_negation() {
        let x1 = Var::new(1);
        let pos = x1.pos();
        let neg = x1.neg();
        assert_eq!(-pos, neg);
        assert_eq!(-neg, pos);
        assert_eq!(-(-pos), pos);
    }

    #[test]
    fn test_lit_from_dimacs() {
        let pos = Lit::from_dimacs(3);
        let neg = Lit::from_dimacs(-3);
        assert_eq!(pos.var(), Var::new(3));
        assert!(pos.is_positive());
        assert_eq!(neg.var(), Var::new(3));
        assert!(neg.is_negative());
    }

    #[test]
    fn test_lit_from_i32() {
        let pos: Lit = 5.into();
        let neg: Lit = (-5).into();
        assert_eq!(pos.var(), Var::new(5));
        assert!(pos.is_positive());
        assert_eq!(neg.var(), Var::new(5));
        assert!(neg.is_negative());
    }

    #[test]
    #[should_panic(expected = "Literal value cannot be zero")]
    fn test_lit_zero_panics() {
        Lit::from_dimacs(0);
    }

    #[test]
    fn test_lit_display() {
        let x1 = Var::new(1);
        assert_eq!(format!("{}", x1.pos()), "x1");
        assert_eq!(format!("{}", x1.neg()), "¬x1");
    }
}
