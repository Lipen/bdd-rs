///! Type-safe wrappers for BDD variables and levels.
///!
///! This module provides newtype wrappers that enforce compile-time distinction
///! between variable IDs and level indices, preventing common mistakes in BDD
///! manipulation code.
use std::fmt;

/// A variable identifier (1-indexed).
///
/// Variables represent Boolean decision points in a BDD. Unlike levels,
/// variable IDs are stable across reordering operations.
///
/// # Invariants
///
/// - Variable IDs must be >= 1 (0 is reserved for terminals)
/// - Variable IDs are independent of their position in the variable ordering
#[derive(Debug, Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub struct Var(u32);

impl Var {
    /// Creates a new variable with the given ID.
    ///
    /// # Panics
    ///
    /// Panics if `id == 0`. Variables must be 1-indexed.
    pub fn new(id: u32) -> Self {
        assert_ne!(id, 0, "Variable IDs must be >= 1");
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
    /// The caller must ensure that `id >= 1`.
    pub unsafe fn from_raw_unchecked(id: u32) -> Self {
        Var(id)
    }
}

impl fmt::Display for Var {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "x{}", self.0)
    }
}

impl From<Var> for u32 {
    fn from(var: Var) -> Self {
        var.0
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

impl From<Level> for usize {
    fn from(level: Level) -> Self {
        level.0
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
        assert!(v1 < v2);
    }

    #[test]
    #[should_panic(expected = "Variable IDs must be >= 1")]
    fn test_var_zero_panics() {
        Var::new(0);
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
        let _l2 = l1.next();

        assert_eq!(l1.prev(), Some(l0));
        assert_eq!(l0.prev(), None);
        assert!(l0.is_top());
        assert!(!l1.is_top());
    }
}
