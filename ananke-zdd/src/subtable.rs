//! Per-level subtable for ZDD nodes with intrusive hashing.
//!
//! Adapted from ananke-bdd's subtable design (CUDD-style).

use crate::node::ZddNode;
use crate::reference::ZddId;
use crate::types::{NodeId, Var};

/// Default number of bucket bits (2^14 = 16384 buckets per level).
const DEFAULT_BUCKET_BITS: usize = 14;

/// A subtable storing ZDD nodes for a single variable.
///
/// Uses intrusive hashing: collision chains stored via `ZddNode.next`,
/// and `buckets` array holds head pointers to each chain.
#[derive(Debug, Clone)]
pub struct Subtable {
    /// The variable for all nodes in this subtable.
    pub variable: Var,

    /// Bucket array: each entry is a head pointer to a collision chain.
    /// `NodeId::NO_NEXT` indicates an empty bucket.
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
            buckets: vec![NodeId::NO_NEXT; num_buckets],
            bitmask,
            count: 0,
        }
    }

    /// Compute bucket index from (lo, hi) children.
    #[inline]
    fn bucket_index(&self, lo: ZddId, hi: ZddId) -> usize {
        let hash = hash_children(lo, hi);
        (hash & self.bitmask) as usize
    }

    /// Look up a node by its children.
    ///
    /// Returns the node index if a node with these children exists.
    pub fn find(&self, lo: ZddId, hi: ZddId, nodes: &[ZddNode]) -> Option<NodeId> {
        let bucket_idx = self.bucket_index(lo, hi);
        let mut current = self.buckets[bucket_idx];

        while current != NodeId::NO_NEXT {
            let node = &nodes[current.index()];
            if node.lo == lo && node.hi == hi {
                return Some(current);
            }
            current = node.next;
        }

        None
    }

    /// Insert a node into the subtable.
    ///
    /// Updates the node's `next` pointer and the bucket head.
    pub fn insert(&mut self, lo: ZddId, hi: ZddId, id: NodeId, nodes: &mut [ZddNode]) {
        let bucket_idx = self.bucket_index(lo, hi);
        let old_head = self.buckets[bucket_idx];
        self.buckets[bucket_idx] = id;
        nodes[id.index()].next = old_head;
        self.count += 1;
    }

    /// Remove a node from the subtable.
    ///
    /// Returns true if the node was found and removed.
    pub fn remove(&mut self, lo: ZddId, hi: ZddId, id: NodeId, nodes: &mut [ZddNode]) -> bool {
        let bucket_idx = self.bucket_index(lo, hi);
        let mut current = self.buckets[bucket_idx];
        let mut prev: Option<NodeId> = None;

        while current != NodeId::NO_NEXT {
            if current == id {
                // Found the node, remove it from chain
                let next = nodes[current.index()].next;
                if let Some(prev_id) = prev {
                    nodes[prev_id.index()].next = next;
                } else {
                    self.buckets[bucket_idx] = next;
                }
                nodes[current.index()].next = NodeId::NO_NEXT;
                self.count -= 1;
                return true;
            }
            prev = Some(current);
            current = nodes[current.index()].next;
        }

        false
    }

    /// Number of nodes in this subtable.
    pub fn len(&self) -> usize {
        self.count
    }

    /// Returns true if the subtable is empty.
    pub fn is_empty(&self) -> bool {
        self.count == 0
    }

    /// Clear all entries (for GC).
    pub fn clear(&mut self) {
        self.buckets.fill(NodeId::NO_NEXT);
        self.count = 0;
    }
}

/// Hash function for (lo, hi) children.
#[inline]
fn hash_children(lo: ZddId, hi: ZddId) -> u64 {
    // FNV-1a inspired mixing
    let mut h = 14695981039346656037u64;
    h ^= lo.raw() as u64;
    h = h.wrapping_mul(1099511628211);
    h ^= hi.raw() as u64;
    h = h.wrapping_mul(1099511628211);
    h
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_subtable_basic() {
        let mut nodes = vec![ZddNode::default(); 10];
        let mut subtable = Subtable::new(Var::new(1));

        // Create a node
        let lo = ZddId::ZERO;
        let hi = ZddId::ONE;
        nodes[2] = ZddNode::new(Var::new(1), lo, hi);

        // Insert
        subtable.insert(lo, hi, NodeId::new(2), &mut nodes);
        assert_eq!(subtable.len(), 1);

        // Find
        let found = subtable.find(lo, hi, &nodes);
        assert_eq!(found, Some(NodeId::new(2)));

        // Not found
        let not_found = subtable.find(ZddId::ONE, ZddId::ONE, &nodes);
        assert_eq!(not_found, None);
    }
}
