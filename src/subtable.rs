//! Per-level subtable for BDD nodes with intrusive hashing.
//!
//! This module implements hash tables for BDD nodes organized by level,
//! using CUDD-style intrusive collision chains.
//!
//! # Design (CUDD-style intrusive hash table)
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
//! Each subtable is an array of buckets (head pointers). Collision chains
//! are stored intrusively via the `Node.next` field, meaning nodes themselves
//! form the linked list --- no separate Entry wrapper needed.
//!
//! ```text
//! Subtable for level k:
//! ┌─────────────────────────────────────────────────┐
//! │ buckets: [u32; 2^bits]                          │
//! │   [0] ─────► Node@5 ──► Node@12 ──► ∅           │
//! │   [1] ─────► ∅                                  │
//! │   [2] ─────► Node@3 ──► ∅                       │
//! │   ...                                           │
//! └─────────────────────────────────────────────────┘
//! ```
//!
//! # Hash Function
//!
//! Hash is computed from `(low, high)` children (variable is implicit):
//! ```text
//! bucket_index = hash(low, high) & bitmask
//! ```
//!
//! # Benefits
//!
//! - **Memory efficient**: No separate `Entry<T>` wrapper, just `Node.next`
//! - **Cache friendly**: Nodes are stored contiguously in global Vec
//! - **Efficient lookup**: O(1) average to find if a node exists
//! - **Efficient reordering**: Swapping variables just rebuilds chains

use crate::node::Node;
use crate::reference::Ref;
use crate::types::{NodeId, Var};
use crate::utils::MyHash;

/// Default number of bucket bits (2^16 = 65536 buckets per level).
const DEFAULT_BUCKET_BITS: usize = 16;

/// A subtable storing BDD nodes for a single variable/level.
///
/// Uses intrusive hashing: collision chains are stored via `Node.next`,
/// and `buckets` array holds head pointers (node indices) to each chain.
#[derive(Debug, Clone)]
pub struct Subtable {
    /// The variable for all nodes in this subtable.
    pub variable: Var,

    /// Bucket array: each entry is a head pointer (node index) to a collision chain.
    /// [`NO_NEXT`](Node::NO_NEXT) indicates an empty bucket.
    buckets: Vec<NodeId>,

    /// Bitmask for hash function: `bucket_index = hash & bitmask`.
    bitmask: u64,

    /// Number of nodes in this subtable.
    count: usize,
}

impl Subtable {
    /// Create a new empty subtable for the given variable.
    pub fn new(variable: Var) -> Self {
        Self::with_bucket_bits(variable, DEFAULT_BUCKET_BITS)
    }

    /// Create a new subtable with specified bucket count (2^bits).
    pub fn with_bucket_bits(variable: Var, bits: usize) -> Self {
        let num_buckets = 1 << bits;
        let bitmask = (num_buckets - 1) as u64;
        Self {
            variable,
            buckets: vec![Node::NO_NEXT; num_buckets],
            bitmask,
            count: 0,
        }
    }

    /// Compute bucket index from (low, high) children.
    #[inline]
    fn bucket_index(&self, low: Ref, high: Ref) -> usize {
        let hash = hash_children(low, high);
        (hash & self.bitmask) as usize
    }

    /// Look up a node by its children, using the given node storage.
    ///
    /// Returns the node index if a node with these children exists.
    pub fn find(&self, low: Ref, high: Ref, nodes: &[Node]) -> Option<NodeId> {
        let bucket_idx = self.bucket_index(low, high);
        let mut current = self.buckets[bucket_idx];

        while current != Node::NO_NEXT {
            let node = nodes[current.index()];
            if node.low == low && node.high == high {
                return Some(current);
            }
            current = node.next;
        }

        None
    }

    /// Insert a node into the subtable (prepend to collision chain).
    ///
    /// **Important**: Caller must set `nodes[id].next` to the returned value.
    /// This is done via `insert` for convenience.
    ///
    /// # Arguments
    ///
    /// * `low` - Low child reference
    /// * `high` - High child reference
    /// * `id` - Node ID being inserted
    ///
    /// # Returns
    ///
    /// The previous head of the bucket (to be stored in `nodes[id].next`).
    fn insert_raw(&mut self, low: Ref, high: Ref, id: NodeId) -> NodeId {
        let bucket_idx = self.bucket_index(low, high);
        let old_head = self.buckets[bucket_idx];
        self.buckets[bucket_idx] = id;
        self.count += 1;
        old_head
    }

    /// Insert a node and update its `next` pointer in the node storage.
    pub fn insert(&mut self, low: Ref, high: Ref, id: NodeId, nodes: &mut [Node]) {
        let old_head = self.insert_raw(low, high, id);
        nodes[id.index()].next = old_head;
    }

    /// Insert with automatic resizing if load factor is too high.
    pub fn insert_with_resize(&mut self, low: Ref, high: Ref, id: NodeId, nodes: &mut [Node]) {
        if self.should_resize() {
            self.resize(nodes);
        }
        self.insert(low, high, id, nodes);
    }

    /// Remove a node from the subtable.
    ///
    /// Returns true if the node was found and removed.
    pub fn remove(&mut self, low: Ref, high: Ref, nodes: &mut [Node]) -> bool {
        let bucket_idx = self.bucket_index(low, high);
        let mut prev = Node::NO_NEXT;
        let mut current = self.buckets[bucket_idx];

        while current != Node::NO_NEXT {
            let node = &nodes[current.index()];

            if node.low == low && node.high == high {
                // Found it - unlink from chain
                if prev == Node::NO_NEXT {
                    // Removing head of chain
                    self.buckets[bucket_idx] = node.next;
                } else {
                    // Removing from middle/end
                    nodes[prev.index()].next = node.next;
                }
                // Clear the removed node's next pointer
                nodes[current.index()].next = Node::NO_NEXT;
                self.count -= 1;
                return true;
            }

            prev = current;
            current = node.next;
        }

        false
    }

    /// Get the number of nodes in this subtable.
    pub fn len(&self) -> usize {
        self.count
    }

    /// Check if the subtable is empty.
    pub fn is_empty(&self) -> bool {
        self.count == 0
    }

    /// Iterate over all node indices in this subtable.
    pub fn indices<'a>(&'a self, nodes: &'a [Node]) -> impl Iterator<Item = NodeId> + 'a {
        self.buckets.iter().flat_map(move |&head| ChainIter::new(head, nodes))
    }

    /// Clear all nodes from the subtable.
    ///
    /// **Note**: This only clears bucket heads. Caller should handle node cleanup.
    pub fn clear(&mut self) {
        for bucket in &mut self.buckets {
            *bucket = Node::NO_NEXT;
        }
        self.count = 0;
    }

    /// Rebuild the subtable from a list of node indices.
    ///
    /// This clears the existing hash table and re-inserts all given nodes.
    pub fn rebuild(&mut self, indices: impl Iterator<Item = NodeId>, nodes: &mut [Node]) {
        self.clear();
        for id in indices {
            let node = &nodes[id.index()];
            let low = node.low;
            let high = node.high;
            self.insert(low, high, id, nodes);
        }
    }

    /// Get the number of buckets.
    pub fn num_buckets(&self) -> usize {
        self.buckets.len()
    }

    /// Get the current load factor (count / num_buckets).
    pub fn load_factor(&self) -> f64 {
        self.count as f64 / self.buckets.len() as f64
    }

    /// Check if the subtable should be resized (load factor > threshold).
    pub fn should_resize(&self) -> bool {
        // Resize when average chain length exceeds ~5
        self.count > self.buckets.len() * 5
    }

    /// Resize the subtable to have more buckets, then rehash all nodes.
    ///
    /// This doubles the bucket count and rebuilds all collision chains.
    pub fn resize(&mut self, nodes: &mut [Node]) {
        log::debug!(
            "Resizing subtable for var {:?}: {} -> {} buckets",
            self.variable,
            self.buckets.len(),
            self.buckets.len() * 2
        );

        let new_bits = (self.buckets.len().trailing_zeros() + 1) as usize;
        let new_num_buckets = 1 << new_bits;
        let new_bitmask = (new_num_buckets - 1) as u64;

        // Collect all current node indices
        let indices: Vec<NodeId> = self.indices(nodes).collect();

        // Create new bucket array
        self.buckets = vec![Node::NO_NEXT; new_num_buckets];
        self.bitmask = new_bitmask;
        self.count = 0;

        // Re-insert all nodes
        for id in indices {
            let node = &nodes[id.index()];
            self.insert(node.low, node.high, id, nodes);
        }
    }
}

/// Hash function for (low, high) children pair.
#[inline]
fn hash_children(low: Ref, high: Ref) -> u64 {
    MyHash::hash(&(low, high))
}

/// Iterator over a collision chain.
struct ChainIter<'a> {
    current: NodeId,
    nodes: &'a [Node],
}

impl<'a> ChainIter<'a> {
    fn new(head: NodeId, nodes: &'a [Node]) -> Self {
        Self { current: head, nodes }
    }
}

impl Iterator for ChainIter<'_> {
    type Item = NodeId;

    fn next(&mut self) -> Option<Self::Item> {
        if self.current == Node::NO_NEXT {
            return None;
        }
        let id = self.current;
        self.current = self.nodes[id.index()].next;
        Some(id)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn make_test_nodes() -> Vec<Node> {
        // Create nodes: index 0 is terminal
        let mut nodes = vec![Node::default(); 10];
        // Node at index 1: var=1, low=~@0, high=@0
        nodes[1] = Node::new(Var::new(1), Ref::negative_from(0), Ref::positive_from(0));
        // Node at index 2: var=1, low=@1, high=@0
        nodes[2] = Node::new(Var::new(1), Ref::positive_from(1), Ref::positive_from(0));
        // Node at index 3: var=1, low=~@0, high=@2
        nodes[3] = Node::new(Var::new(1), Ref::negative_from(0), Ref::positive_from(2));
        nodes
    }

    #[test]
    fn test_subtable_basic() {
        let mut nodes = make_test_nodes();
        let mut st = Subtable::new(Var::new(1));

        let low = Ref::negative_from(0);
        let high = Ref::positive_from(0);

        // Should not find before insert
        assert!(st.find(low, high, &nodes).is_none());

        // Insert node at index 1
        st.insert(low, high, NodeId::new(1), &mut nodes);
        assert_eq!(st.find(low, high, &nodes), Some(NodeId::new(1)));
        assert_eq!(st.len(), 1);

        // Remove
        assert!(st.remove(low, high, &mut nodes));
        assert!(st.find(low, high, &nodes).is_none());
        assert!(st.is_empty());
    }

    #[test]
    fn test_subtable_multiple_nodes() {
        let mut nodes = make_test_nodes();
        let mut st = Subtable::new(Var::new(1));

        // Insert multiple nodes
        st.insert(Ref::negative_from(0), Ref::positive_from(0), NodeId::new(1), &mut nodes);
        st.insert(Ref::positive_from(1), Ref::positive_from(0), NodeId::new(2), &mut nodes);
        st.insert(Ref::negative_from(0), Ref::positive_from(2), NodeId::new(3), &mut nodes);

        assert_eq!(st.len(), 3);
        assert_eq!(st.find(Ref::negative_from(0), Ref::positive_from(0), &nodes), Some(NodeId::new(1)));
        assert_eq!(st.find(Ref::positive_from(1), Ref::positive_from(0), &nodes), Some(NodeId::new(2)));
        assert_eq!(st.find(Ref::negative_from(0), Ref::positive_from(2), &nodes), Some(NodeId::new(3)));
    }

    #[test]
    fn test_subtable_collision_chain() {
        // Force collisions by using small bucket count
        let mut nodes = make_test_nodes();
        let mut st = Subtable::with_bucket_bits(Var::new(1), 1); // Only 2 buckets!

        st.insert(Ref::negative_from(0), Ref::positive_from(0), NodeId::new(1), &mut nodes);
        st.insert(Ref::positive_from(1), Ref::positive_from(0), NodeId::new(2), &mut nodes);
        st.insert(Ref::negative_from(0), Ref::positive_from(2), NodeId::new(3), &mut nodes);

        assert_eq!(st.len(), 3);

        // All should be findable despite collisions
        assert_eq!(st.find(Ref::negative_from(0), Ref::positive_from(0), &nodes), Some(NodeId::new(1)));
        assert_eq!(st.find(Ref::positive_from(1), Ref::positive_from(0), &nodes), Some(NodeId::new(2)));
        assert_eq!(st.find(Ref::negative_from(0), Ref::positive_from(2), &nodes), Some(NodeId::new(3)));

        // Remove middle element from a chain
        assert!(st.remove(Ref::positive_from(1), Ref::positive_from(0), &mut nodes));
        assert_eq!(st.len(), 2);
        assert!(st.find(Ref::positive_from(1), Ref::positive_from(0), &nodes).is_none());

        // Others should still be there
        assert_eq!(st.find(Ref::negative_from(0), Ref::positive_from(0), &nodes), Some(NodeId::new(1)));
        assert_eq!(st.find(Ref::negative_from(0), Ref::positive_from(2), &nodes), Some(NodeId::new(3)));
    }

    #[test]
    fn test_subtable_indices_iteration() {
        let mut nodes = make_test_nodes();
        let mut st = Subtable::new(Var::new(1));

        st.insert(Ref::negative_from(0), Ref::positive_from(0), NodeId::new(1), &mut nodes);
        st.insert(Ref::positive_from(1), Ref::positive_from(0), NodeId::new(2), &mut nodes);

        let mut indices: Vec<_> = st.indices(&nodes).map(|n| n.index()).collect();
        indices.sort();
        assert_eq!(indices, vec![1, 2]);
    }

    #[test]
    fn test_subtable_rebuild() {
        let mut nodes = make_test_nodes();
        let mut st = Subtable::new(Var::new(1));

        // Initial inserts
        st.insert(Ref::negative_from(0), Ref::positive_from(0), NodeId::new(1), &mut nodes);
        st.insert(Ref::positive_from(1), Ref::positive_from(0), NodeId::new(2), &mut nodes);

        // Rebuild from indices
        st.rebuild([1u32, 2, 3].into_iter().map(|i| NodeId::new(i)), &mut nodes);

        assert_eq!(st.len(), 3);
        assert_eq!(st.find(Ref::negative_from(0), Ref::positive_from(0), &nodes), Some(NodeId::new(1)));
        assert_eq!(st.find(Ref::positive_from(1), Ref::positive_from(0), &nodes), Some(NodeId::new(2)));
        assert_eq!(st.find(Ref::negative_from(0), Ref::positive_from(2), &nodes), Some(NodeId::new(3)));
    }

    #[test]
    fn test_subtable_resize() {
        let mut nodes = make_test_nodes();
        // Start with just 2 buckets
        let mut st = Subtable::with_bucket_bits(Var::new(1), 1);
        assert_eq!(st.num_buckets(), 2);

        st.insert(Ref::negative_from(0), Ref::positive_from(0), NodeId::new(1), &mut nodes);
        st.insert(Ref::positive_from(1), Ref::positive_from(0), NodeId::new(2), &mut nodes);
        st.insert(Ref::negative_from(0), Ref::positive_from(2), NodeId::new(3), &mut nodes);

        // With 3 nodes and 2 buckets, load factor is 1.5, should_resize should be false
        // (threshold is count > buckets * 2, i.e., > 4)
        assert!(!st.should_resize());

        // Manually resize
        st.resize(&mut nodes);
        assert_eq!(st.num_buckets(), 4);
        assert_eq!(st.len(), 3);

        // All nodes should still be findable
        assert_eq!(st.find(Ref::negative_from(0), Ref::positive_from(0), &nodes), Some(NodeId::new(1)));
        assert_eq!(st.find(Ref::positive_from(1), Ref::positive_from(0), &nodes), Some(NodeId::new(2)));
        assert_eq!(st.find(Ref::negative_from(0), Ref::positive_from(2), &nodes), Some(NodeId::new(3)));
    }

    #[test]
    fn test_subtable_load_factor() {
        let mut nodes = make_test_nodes();
        let mut st = Subtable::with_bucket_bits(Var::new(1), 2); // 4 buckets

        assert_eq!(st.load_factor(), 0.0);

        st.insert(Ref::negative_from(0), Ref::positive_from(0), NodeId::new(1), &mut nodes);
        assert_eq!(st.load_factor(), 0.25);

        st.insert(Ref::positive_from(1), Ref::positive_from(0), NodeId::new(2), &mut nodes);
        assert_eq!(st.load_factor(), 0.5);
    }
}
