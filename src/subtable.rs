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
//! │   [1] ─────► ∅                                   │
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
//! - **Memory efficient**: No separate Entry<T> wrapper, just Node.next
//! - **Cache friendly**: Nodes are stored contiguously in global Vec
//! - **Efficient lookup**: O(1) average to find if a node exists
//! - **Efficient reordering**: Swapping variables just rebuilds chains

use crate::node::Node;
use crate::reference::Ref;
use crate::types::Var;
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
    /// `0` indicates an empty bucket.
    buckets: Vec<u32>,

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
        let num_buckets = 1usize << bits;
        let bitmask = (num_buckets - 1) as u64;
        Self {
            variable,
            buckets: vec![0; num_buckets],
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
    pub fn find(&self, low: Ref, high: Ref, nodes: &[Node]) -> Option<u32> {
        let bucket_idx = self.bucket_index(low, high);
        let mut current = self.buckets[bucket_idx];

        while current != 0 {
            let node = &nodes[current as usize];
            if node.low == low && node.high == high {
                return Some(current);
            }
            current = node.next;
        }

        None
    }

    /// Insert a node into the subtable (prepend to collision chain).
    ///
    /// **Important**: Caller must set `nodes[index].next` to the returned value.
    /// This is done via `insert` for convenience.
    ///
    /// # Arguments
    ///
    /// * `low` - Low child reference
    /// * `high` - High child reference
    /// * `index` - Storage index of the node
    ///
    /// # Returns
    ///
    /// The previous head of the bucket (to be stored in `nodes[index].next`).
    pub fn insert_raw(&mut self, low: Ref, high: Ref, index: u32) -> u32 {
        let bucket_idx = self.bucket_index(low, high);
        let old_head = self.buckets[bucket_idx];
        self.buckets[bucket_idx] = index;
        self.count += 1;
        old_head
    }

    /// Insert a node and update its `next` pointer in the node storage.
    pub fn insert(&mut self, low: Ref, high: Ref, index: u32, nodes: &mut [Node]) {
        let old_head = self.insert_raw(low, high, index);
        nodes[index as usize].next = old_head;
    }

    /// Remove a node from the subtable.
    ///
    /// Returns true if the node was found and removed.
    pub fn remove(&mut self, low: Ref, high: Ref, nodes: &mut [Node]) -> bool {
        let bucket_idx = self.bucket_index(low, high);
        let mut prev: u32 = 0;
        let mut current = self.buckets[bucket_idx];

        while current != 0 {
            let node = &nodes[current as usize];

            if node.low == low && node.high == high {
                // Found it - unlink from chain
                if prev == 0 {
                    // Removing head of chain
                    self.buckets[bucket_idx] = node.next;
                } else {
                    // Removing from middle/end
                    nodes[prev as usize].next = node.next;
                }
                // Clear the removed node's next pointer
                nodes[current as usize].next = 0;
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
    pub fn indices<'a>(&'a self, nodes: &'a [Node]) -> impl Iterator<Item = u32> + 'a {
        self.buckets.iter().flat_map(move |&head| ChainIter::new(head, nodes))
    }

    /// Clear all nodes from the subtable.
    ///
    /// **Note**: This only clears bucket heads. Caller should handle node cleanup.
    pub fn clear(&mut self) {
        for bucket in &mut self.buckets {
            *bucket = 0;
        }
        self.count = 0;
    }

    /// Rebuild the subtable from a list of node indices.
    ///
    /// This clears the existing hash table and re-inserts all given nodes.
    pub fn rebuild(&mut self, indices: impl Iterator<Item = u32>, nodes: &mut [Node]) {
        self.clear();
        for index in indices {
            let node = &nodes[index as usize];
            let low = node.low;
            let high = node.high;
            self.insert(low, high, index, nodes);
        }
    }

    /// Get the number of buckets.
    pub fn num_buckets(&self) -> usize {
        self.buckets.len()
    }
}

/// Hash function for (low, high) children pair.
#[inline]
fn hash_children(low: Ref, high: Ref) -> u64 {
    MyHash::hash(&(low, high))
}

/// Iterator over a collision chain.
struct ChainIter<'a> {
    current: u32,
    nodes: &'a [Node],
}

impl<'a> ChainIter<'a> {
    fn new(head: u32, nodes: &'a [Node]) -> Self {
        Self { current: head, nodes }
    }
}

impl Iterator for ChainIter<'_> {
    type Item = u32;

    fn next(&mut self) -> Option<Self::Item> {
        if self.current == 0 {
            return None;
        }
        let idx = self.current;
        self.current = self.nodes[idx as usize].next;
        Some(idx)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn make_test_nodes() -> Vec<Node> {
        // Create nodes: index 0 reserved, index 1 is terminal
        let mut nodes = vec![Node::default(); 10];
        // Node at index 2: var=1, low=~@1, high=@1
        nodes[2] = Node::new(Var::new(1), -Ref::positive(1), Ref::positive(1));
        // Node at index 3: var=1, low=@2, high=@1
        nodes[3] = Node::new(Var::new(1), Ref::positive(2), Ref::positive(1));
        // Node at index 4: var=1, low=~@1, high=@3
        nodes[4] = Node::new(Var::new(1), -Ref::positive(1), Ref::positive(3));
        nodes
    }

    #[test]
    fn test_subtable_basic() {
        let mut nodes = make_test_nodes();
        let mut st = Subtable::new(Var::new(1));

        let low = -Ref::positive(1);
        let high = Ref::positive(1);

        // Should not find before insert
        assert!(st.find(low, high, &nodes).is_none());

        // Insert node at index 2
        st.insert(low, high, 2, &mut nodes);
        assert_eq!(st.find(low, high, &nodes), Some(2));
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
        st.insert(-Ref::positive(1), Ref::positive(1), 2, &mut nodes);
        st.insert(Ref::positive(2), Ref::positive(1), 3, &mut nodes);
        st.insert(-Ref::positive(1), Ref::positive(3), 4, &mut nodes);

        assert_eq!(st.len(), 3);
        assert_eq!(st.find(-Ref::positive(1), Ref::positive(1), &nodes), Some(2));
        assert_eq!(st.find(Ref::positive(2), Ref::positive(1), &nodes), Some(3));
        assert_eq!(st.find(-Ref::positive(1), Ref::positive(3), &nodes), Some(4));
    }

    #[test]
    fn test_subtable_collision_chain() {
        // Force collisions by using small bucket count
        let mut nodes = make_test_nodes();
        let mut st = Subtable::with_bucket_bits(Var::new(1), 1); // Only 2 buckets!

        st.insert(-Ref::positive(1), Ref::positive(1), 2, &mut nodes);
        st.insert(Ref::positive(2), Ref::positive(1), 3, &mut nodes);
        st.insert(-Ref::positive(1), Ref::positive(3), 4, &mut nodes);

        assert_eq!(st.len(), 3);

        // All should be findable despite collisions
        assert_eq!(st.find(-Ref::positive(1), Ref::positive(1), &nodes), Some(2));
        assert_eq!(st.find(Ref::positive(2), Ref::positive(1), &nodes), Some(3));
        assert_eq!(st.find(-Ref::positive(1), Ref::positive(3), &nodes), Some(4));

        // Remove middle element from a chain
        assert!(st.remove(Ref::positive(2), Ref::positive(1), &mut nodes));
        assert_eq!(st.len(), 2);
        assert!(st.find(Ref::positive(2), Ref::positive(1), &nodes).is_none());

        // Others should still be there
        assert_eq!(st.find(-Ref::positive(1), Ref::positive(1), &nodes), Some(2));
        assert_eq!(st.find(-Ref::positive(1), Ref::positive(3), &nodes), Some(4));
    }

    #[test]
    fn test_subtable_indices_iteration() {
        let mut nodes = make_test_nodes();
        let mut st = Subtable::new(Var::new(1));

        st.insert(-Ref::positive(1), Ref::positive(1), 2, &mut nodes);
        st.insert(Ref::positive(2), Ref::positive(1), 3, &mut nodes);

        let mut indices: Vec<_> = st.indices(&nodes).collect();
        indices.sort();
        assert_eq!(indices, vec![2, 3]);
    }

    #[test]
    fn test_subtable_rebuild() {
        let mut nodes = make_test_nodes();
        let mut st = Subtable::new(Var::new(1));

        // Initial inserts
        st.insert(-Ref::positive(1), Ref::positive(1), 2, &mut nodes);
        st.insert(Ref::positive(2), Ref::positive(1), 3, &mut nodes);

        // Rebuild from indices
        st.rebuild([2u32, 3, 4].into_iter(), &mut nodes);

        assert_eq!(st.len(), 3);
        assert_eq!(st.find(-Ref::positive(1), Ref::positive(1), &nodes), Some(2));
        assert_eq!(st.find(Ref::positive(2), Ref::positive(1), &nodes), Some(3));
        assert_eq!(st.find(-Ref::positive(1), Ref::positive(3), &nodes), Some(4));
    }
}
