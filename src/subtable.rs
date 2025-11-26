//! Per-level subtable for BDD nodes.
//!
//! This module implements hash tables for BDD nodes organized by level.
//! Each subtable stores nodes with the same variable, using `(low, high)` as the key.
//!
//! # Design (CUDD-inspired)
//!
//! Following CUDD's approach, the BDD manager maintains:
//!
//! 1. A simple `Vec<Node>` for node storage (indexed by node ID)
//! 2. A vector of subtables for hash-based lookup:
//!
//! ```text
//! subtables[0] → Subtable for level 0 (e.g., variable x1)
//! subtables[1] → Subtable for level 1 (e.g., variable x2)
//! subtables[2] → Subtable for level 2 (e.g., variable x3)
//! ...
//! ```
//!
//! Each subtable is a hash map from `(low, high)` children to node index.
//! Since all nodes in a subtable have the same variable, we don't need to
//! include the variable in the key.
//!
//! # Benefits
//!
//! - **Efficient lookup**: O(1) to find if a node with given children exists
//! - **Efficient reordering**: Swapping variables just rebuilds subtable entries
//! - **Simple storage**: Nodes are stored in a plain Vec, indexed directly
//!
//! # Variable Reordering
//!
//! When swapping adjacent levels, we:
//! 1. Restructure nodes at the swap level
//! 2. Update ancestor nodes that reference swapped nodes
//! 3. Rebuild subtables (simple and correct)

use std::collections::HashMap;

use crate::reference::Ref;
use crate::types::Var;

/// A subtable storing BDD nodes for a single variable/level.
///
/// Nodes in a subtable all have the same variable. The hash table is keyed
/// by (low, high) children since the variable is implicit.
#[derive(Debug, Clone)]
pub struct Subtable {
    /// The variable for all nodes in this subtable.
    pub variable: Var,

    /// Map from (low, high) to node index in the global storage.
    nodes: HashMap<(Ref, Ref), u32>,
}

impl Subtable {
    /// Create a new empty subtable for the given variable.
    pub fn new(variable: Var) -> Self {
        Self {
            variable,
            nodes: HashMap::new(),
        }
    }

    /// Look up a node by its children.
    ///
    /// Returns the storage index if a node with these children exists.
    pub fn find(&self, low: Ref, high: Ref) -> Option<u32> {
        self.nodes.get(&(low, high)).copied()
    }

    /// Insert a node into the subtable.
    ///
    /// # Arguments
    ///
    /// * `low` - Low child reference
    /// * `high` - High child reference
    /// * `index` - Storage index of the node
    pub fn insert(&mut self, low: Ref, high: Ref, index: u32) {
        self.nodes.insert((low, high), index);
    }

    /// Remove a node from the subtable.
    ///
    /// Returns the storage index if the node was present.
    pub fn remove(&mut self, low: Ref, high: Ref) -> Option<u32> {
        self.nodes.remove(&(low, high))
    }

    /// Get the number of nodes in this subtable.
    pub fn len(&self) -> usize {
        self.nodes.len()
    }

    /// Check if the subtable is empty.
    pub fn is_empty(&self) -> bool {
        self.nodes.is_empty()
    }

    /// Iterate over all node indices in this subtable.
    pub fn indices(&self) -> impl Iterator<Item = u32> + '_ {
        self.nodes.values().copied()
    }

    /// Iterate over all (low, high, index) tuples.
    pub fn iter(&self) -> impl Iterator<Item = (Ref, Ref, u32)> + '_ {
        self.nodes.iter().map(|(&(low, high), &idx)| (low, high, idx))
    }

    /// Clear all nodes from the subtable.
    pub fn clear(&mut self) {
        self.nodes.clear();
    }

    /// Update a node's children in the subtable.
    ///
    /// This removes the old entry and inserts a new one.
    /// Used during variable reordering when children change.
    pub fn update(&mut self, old_low: Ref, old_high: Ref, new_low: Ref, new_high: Ref, index: u32) {
        self.nodes.remove(&(old_low, old_high));
        self.nodes.insert((new_low, new_high), index);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_subtable_basic() {
        let mut st = Subtable::new(Var::new(1));

        // Use valid Ref indices (non-zero)
        let low = -Ref::positive(1); // ~@1 (negated one, represents zero)
        let high = Ref::positive(1); // @1 (one)

        assert!(st.find(low, high).is_none());

        st.insert(low, high, 42);
        assert_eq!(st.find(low, high), Some(42));
        assert_eq!(st.len(), 1);

        st.remove(low, high);
        assert!(st.find(low, high).is_none());
        assert!(st.is_empty());
    }

    #[test]
    fn test_subtable_multiple_nodes() {
        let mut st = Subtable::new(Var::new(1));

        // Use valid Ref indices (non-zero)
        st.insert(-Ref::positive(1), Ref::positive(1), 10);
        st.insert(Ref::positive(2), Ref::positive(3), 20);
        st.insert(-Ref::positive(1), Ref::positive(3), 30);

        assert_eq!(st.len(), 3);
        assert_eq!(st.find(-Ref::positive(1), Ref::positive(1)), Some(10));
        assert_eq!(st.find(Ref::positive(2), Ref::positive(3)), Some(20));
        assert_eq!(st.find(-Ref::positive(1), Ref::positive(3)), Some(30));
    }
}
