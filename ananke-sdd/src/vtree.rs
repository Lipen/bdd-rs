//! Variable Tree (Vtree) for SDD decomposition.
//!
//! A vtree is a full binary tree whose leaves correspond to Boolean variables.
//! The structure of the vtree determines how SDDs decompose Boolean functions.
//!
//! # Properties
//!
//! - Every internal node has exactly two children (left and right)
//! - Leaves are labeled with variables (1-indexed)
//! - The vtree defines a hierarchical partitioning of variables
//!
//! # Construction Strategies
//!
//! - **Right-linear**: Variables ordered left-to-right in a chain
//! - **Left-linear**: Variables ordered right-to-left in a chain
//! - **Balanced**: Balanced binary tree for minimal height
//!
//! # Example
//!
//! For variables {x₁, x₂, x₃, x₄}, a balanced vtree looks like:
//!
//! ```text
//!        (3)
//!        / \
//!       /   \
//!     (1)   (2)
//!     / \   / \
//!    x₁ x₂ x₃ x₄
//! ```

use std::fmt::{self, Display};

/// Unique identifier for a vtree node.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct VtreeId(u32);

impl VtreeId {
    /// Creates a new VtreeId from a raw value.
    #[inline]
    pub const fn new(id: u32) -> Self {
        Self(id)
    }

    /// Returns the raw value.
    #[inline]
    pub const fn raw(self) -> u32 {
        self.0
    }

    /// Returns the index (0-based) for array access.
    #[inline]
    pub const fn index(self) -> usize {
        self.0 as usize
    }
}

impl Display for VtreeId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "v{}", self.0)
    }
}

impl From<u32> for VtreeId {
    fn from(id: u32) -> Self {
        Self(id)
    }
}

impl From<usize> for VtreeId {
    fn from(id: usize) -> Self {
        Self(id as u32)
    }
}

/// A vtree node: either a leaf (variable) or internal (with left/right children).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum VtreeNode {
    /// A leaf node labeled with a variable (1-indexed).
    Leaf { var: u32 },

    /// An internal node with left and right children.
    Internal { left: VtreeId, right: VtreeId },
}

impl VtreeNode {
    /// Returns true if this is a leaf node.
    #[inline]
    pub fn is_leaf(&self) -> bool {
        matches!(self, VtreeNode::Leaf { .. })
    }

    /// Returns true if this is an internal node.
    #[inline]
    pub fn is_internal(&self) -> bool {
        matches!(self, VtreeNode::Internal { .. })
    }

    /// Returns the variable if this is a leaf, None otherwise.
    #[inline]
    pub fn var(&self) -> Option<u32> {
        match self {
            VtreeNode::Leaf { var } => Some(*var),
            VtreeNode::Internal { .. } => None,
        }
    }

    /// Returns the left child if this is an internal node, None otherwise.
    #[inline]
    pub fn left(&self) -> Option<VtreeId> {
        match self {
            VtreeNode::Internal { left, .. } => Some(*left),
            VtreeNode::Leaf { .. } => None,
        }
    }

    /// Returns the right child if this is an internal node, None otherwise.
    #[inline]
    pub fn right(&self) -> Option<VtreeId> {
        match self {
            VtreeNode::Internal { right, .. } => Some(*right),
            VtreeNode::Leaf { .. } => None,
        }
    }
}

/// A complete variable tree (vtree).
///
/// The vtree determines the decomposition structure of SDDs.
/// Nodes are stored in a flat array for efficient access.
#[derive(Debug, Clone)]
pub struct Vtree {
    /// All vtree nodes, indexed by VtreeId.
    nodes: Vec<VtreeNode>,
    /// Parent of each node (None for root).
    parents: Vec<Option<VtreeId>>,
    /// The root node ID.
    root: VtreeId,
    /// Number of variables.
    num_vars: u32,
    /// Mapping from variable to its leaf vtree node.
    var_to_vtree: Vec<VtreeId>,
    /// In-order position of each node (0-indexed).
    /// Used for comparing vtree nodes in apply.
    positions: Vec<u32>,
}

impl Vtree {
    /// Creates a balanced vtree for the given number of variables.
    ///
    /// Variables are numbered 1 to `num_vars`.
    ///
    /// # Example
    ///
    /// For 4 variables, creates:
    /// ```text
    ///        (root)
    ///        /    \
    ///       /      \
    ///     ( )      ( )
    ///     / \      / \
    ///    x₁  x₂  x₃  x₄
    /// ```
    pub fn balanced(num_vars: u32) -> Self {
        assert!(num_vars > 0, "Must have at least one variable");

        let mut nodes = Vec::new();
        let mut parents = Vec::new();
        let mut var_to_vtree = vec![VtreeId::new(0); (num_vars + 1) as usize];

        // Build vtree bottom-up
        let vars: Vec<u32> = (1..=num_vars).collect();
        let root = Self::build_balanced(&vars, &mut nodes, &mut parents, &mut var_to_vtree);

        // Set root's parent to None
        parents[root.index()] = None;

        let mut vtree = Self {
            nodes,
            parents,
            root,
            num_vars,
            var_to_vtree,
            positions: Vec::new(),
        };
        vtree.compute_positions();
        vtree
    }

    /// Creates a right-linear (chain) vtree for the given number of variables.
    ///
    /// Variables appear from left to right as: x₁, x₂, ..., xₙ
    ///
    /// # Example
    ///
    /// For 4 variables, creates:
    /// ```text
    ///            (root)
    ///            /    \
    ///           x₁    ( )
    ///                /   \
    ///               x₂   ( )
    ///                   /   \
    ///                  x₃   x₄
    /// ```
    pub fn right_linear(num_vars: u32) -> Self {
        assert!(num_vars > 0, "Must have at least one variable");

        let mut nodes = Vec::new();
        let mut parents = Vec::new();
        let mut var_to_vtree = vec![VtreeId::new(0); (num_vars + 1) as usize];

        // Build right-linear chain
        let root = Self::build_right_linear(1, num_vars, &mut nodes, &mut parents, &mut var_to_vtree);

        // Set root's parent to None
        parents[root.index()] = None;

        let mut vtree = Self {
            nodes,
            parents,
            root,
            num_vars,
            var_to_vtree,
            positions: Vec::new(),
        };
        vtree.compute_positions();
        vtree
    }

    /// Creates a left-linear (chain) vtree for the given number of variables.
    ///
    /// Variables appear from right to left as: xₙ, ..., x₂, x₁
    ///
    /// # Example
    ///
    /// For 4 variables, creates:
    /// ```text
    ///        (root)
    ///        /    \
    ///       ( )   x₄
    ///      /   \
    ///     ( )  x₃
    ///    /   \
    ///   x₁   x₂
    /// ```
    pub fn left_linear(num_vars: u32) -> Self {
        assert!(num_vars > 0, "Must have at least one variable");

        let mut nodes = Vec::new();
        let mut parents = Vec::new();
        let mut var_to_vtree = vec![VtreeId::new(0); (num_vars + 1) as usize];

        // Build left-linear chain
        let root = Self::build_left_linear(1, num_vars, &mut nodes, &mut parents, &mut var_to_vtree);

        // Set root's parent to None
        parents[root.index()] = None;

        let mut vtree = Self {
            nodes,
            parents,
            root,
            num_vars,
            var_to_vtree,
            positions: Vec::new(),
        };
        vtree.compute_positions();
        vtree
    }

    /// Recursively builds a balanced vtree.
    fn build_balanced(
        vars: &[u32],
        nodes: &mut Vec<VtreeNode>,
        parents: &mut Vec<Option<VtreeId>>,
        var_to_vtree: &mut Vec<VtreeId>,
    ) -> VtreeId {
        if vars.len() == 1 {
            // Create leaf
            let id = VtreeId::new(nodes.len() as u32);
            nodes.push(VtreeNode::Leaf { var: vars[0] });
            parents.push(None); // Will be set by parent
            var_to_vtree[vars[0] as usize] = id;
            id
        } else {
            // Split variables and recurse
            let mid = vars.len() / 2;
            let left = Self::build_balanced(&vars[..mid], nodes, parents, var_to_vtree);
            let right = Self::build_balanced(&vars[mid..], nodes, parents, var_to_vtree);

            // Create internal node
            let id = VtreeId::new(nodes.len() as u32);
            nodes.push(VtreeNode::Internal { left, right });
            parents.push(None); // Will be set by parent

            // Set parent pointers for children
            parents[left.index()] = Some(id);
            parents[right.index()] = Some(id);

            id
        }
    }

    /// Recursively builds a right-linear vtree.
    fn build_right_linear(
        first: u32,
        last: u32,
        nodes: &mut Vec<VtreeNode>,
        parents: &mut Vec<Option<VtreeId>>,
        var_to_vtree: &mut Vec<VtreeId>,
    ) -> VtreeId {
        if first == last {
            // Single variable: create leaf
            let id = VtreeId::new(nodes.len() as u32);
            nodes.push(VtreeNode::Leaf { var: first });
            parents.push(None);
            var_to_vtree[first as usize] = id;
            id
        } else {
            // Left child is a leaf, right child is the rest
            let left_id = VtreeId::new(nodes.len() as u32);
            nodes.push(VtreeNode::Leaf { var: first });
            parents.push(None);
            var_to_vtree[first as usize] = left_id;

            let right = Self::build_right_linear(first + 1, last, nodes, parents, var_to_vtree);

            // Create internal node
            let id = VtreeId::new(nodes.len() as u32);
            nodes.push(VtreeNode::Internal { left: left_id, right });
            parents.push(None);

            // Set parent pointers
            parents[left_id.index()] = Some(id);
            parents[right.index()] = Some(id);

            id
        }
    }

    /// Recursively builds a left-linear vtree.
    fn build_left_linear(
        first: u32,
        last: u32,
        nodes: &mut Vec<VtreeNode>,
        parents: &mut Vec<Option<VtreeId>>,
        var_to_vtree: &mut Vec<VtreeId>,
    ) -> VtreeId {
        if first == last {
            // Single variable: create leaf
            let id = VtreeId::new(nodes.len() as u32);
            nodes.push(VtreeNode::Leaf { var: first });
            parents.push(None);
            var_to_vtree[first as usize] = id;
            id
        } else {
            // Right child is a leaf (last var), left child is the rest
            let left = Self::build_left_linear(first, last - 1, nodes, parents, var_to_vtree);

            let right_id = VtreeId::new(nodes.len() as u32);
            nodes.push(VtreeNode::Leaf { var: last });
            parents.push(None);
            var_to_vtree[last as usize] = right_id;

            // Create internal node
            let id = VtreeId::new(nodes.len() as u32);
            nodes.push(VtreeNode::Internal { left, right: right_id });
            parents.push(None);

            // Set parent pointers
            parents[left.index()] = Some(id);
            parents[right_id.index()] = Some(id);

            id
        }
    }

    /// Creates a vtree from raw parts.
    ///
    /// This is mainly used for deserialization.
    pub(crate) fn from_parts(
        nodes: Vec<VtreeNode>,
        parents: Vec<Option<VtreeId>>,
        root: VtreeId,
        num_vars: u32,
        var_to_vtree: Vec<VtreeId>,
    ) -> Self {
        let mut vtree = Self {
            nodes,
            parents,
            root,
            num_vars,
            var_to_vtree,
            positions: Vec::new(),
        };
        vtree.compute_positions();
        vtree
    }

    /// Computes in-order positions for all nodes.
    fn compute_positions(&mut self) {
        self.positions = vec![0; self.nodes.len()];
        let mut pos = 0u32;
        self.compute_positions_rec(self.root, &mut pos);
    }

    fn compute_positions_rec(&mut self, id: VtreeId, pos: &mut u32) {
        match self.nodes[id.index()] {
            VtreeNode::Leaf { .. } => {
                self.positions[id.index()] = *pos;
                *pos += 1;
            }
            VtreeNode::Internal { left, right } => {
                self.compute_positions_rec(left, pos);
                self.positions[id.index()] = *pos;
                *pos += 1;
                self.compute_positions_rec(right, pos);
            }
        }
    }

    /// Returns the root vtree node ID.
    #[inline]
    pub fn root(&self) -> VtreeId {
        self.root
    }

    /// Returns the number of variables.
    #[inline]
    pub fn num_vars(&self) -> u32 {
        self.num_vars
    }

    /// Returns the number of nodes in the vtree.
    #[inline]
    pub fn num_nodes(&self) -> usize {
        self.nodes.len()
    }

    /// Returns the node at the given ID.
    #[inline]
    pub fn node(&self, id: VtreeId) -> &VtreeNode {
        &self.nodes[id.index()]
    }

    /// Returns the parent of a vtree node, if any.
    #[inline]
    pub fn parent(&self, id: VtreeId) -> Option<VtreeId> {
        self.parents[id.index()]
    }

    /// Returns the in-order position of a vtree node.
    ///
    /// Position is used to compare vtree nodes in the apply algorithm.
    /// Nodes earlier in in-order traversal have smaller positions.
    #[inline]
    pub fn position(&self, id: VtreeId) -> u32 {
        self.positions[id.index()]
    }

    /// Returns the vtree node ID for a variable.
    #[inline]
    pub fn var_vtree(&self, var: u32) -> VtreeId {
        self.var_to_vtree[var as usize]
    }

    /// Checks if a vtree node is a leaf.
    #[inline]
    pub fn is_leaf(&self, id: VtreeId) -> bool {
        self.node(id).is_leaf()
    }

    /// Checks if a vtree node is internal.
    #[inline]
    pub fn is_internal(&self, id: VtreeId) -> bool {
        self.node(id).is_internal()
    }

    /// Returns the left child of an internal node.
    ///
    /// # Panics
    ///
    /// Panics if the node is a leaf.
    #[inline]
    pub fn left(&self, id: VtreeId) -> VtreeId {
        self.node(id).left().expect("Node is not internal")
    }

    /// Returns the right child of an internal node.
    ///
    /// # Panics
    ///
    /// Panics if the node is a leaf.
    #[inline]
    pub fn right(&self, id: VtreeId) -> VtreeId {
        self.node(id).right().expect("Node is not internal")
    }

    /// Returns the variable of a leaf node.
    ///
    /// # Panics
    ///
    /// Panics if the node is not a leaf.
    #[inline]
    pub fn var(&self, id: VtreeId) -> u32 {
        self.node(id).var().expect("Node is not a leaf")
    }

    /// Collects all variables under a vtree node (in order).
    pub fn variables_under(&self, id: VtreeId) -> Vec<u32> {
        let mut vars = Vec::new();
        self.collect_variables(id, &mut vars);
        vars
    }

    fn collect_variables(&self, id: VtreeId, vars: &mut Vec<u32>) {
        match self.node(id) {
            VtreeNode::Leaf { var } => vars.push(*var),
            VtreeNode::Internal { left, right } => {
                self.collect_variables(*left, vars);
                self.collect_variables(*right, vars);
            }
        }
    }

    /// Finds the lowest common ancestor of two vtree nodes.
    pub fn lca(&self, a: VtreeId, b: VtreeId) -> VtreeId {
        // Collect ancestors of a
        let mut ancestors_a = std::collections::HashSet::new();
        let mut current = Some(a);
        while let Some(id) = current {
            ancestors_a.insert(id);
            current = self.parent(id);
        }

        // Find first ancestor of b that's also an ancestor of a
        let mut current = Some(b);
        while let Some(id) = current {
            if ancestors_a.contains(&id) {
                return id;
            }
            current = self.parent(id);
        }

        // Should never happen for valid vtree
        self.root
    }

    /// Checks if node `ancestor` is an ancestor of node `descendant`.
    pub fn is_ancestor(&self, ancestor: VtreeId, descendant: VtreeId) -> bool {
        if ancestor == descendant {
            return true;
        }
        let mut current = self.parent(descendant);
        while let Some(id) = current {
            if id == ancestor {
                return true;
            }
            current = self.parent(id);
        }
        false
    }

    /// Checks if node `a` is in the left subtree of `ancestor`.
    pub fn is_in_left_subtree(&self, a: VtreeId, ancestor: VtreeId) -> bool {
        if let VtreeNode::Internal { left, .. } = self.node(ancestor) {
            self.is_ancestor(*left, a)
        } else {
            false
        }
    }

    /// Checks if node `a` is in the right subtree of `ancestor`.
    pub fn is_in_right_subtree(&self, a: VtreeId, ancestor: VtreeId) -> bool {
        if let VtreeNode::Internal { right, .. } = self.node(ancestor) {
            self.is_ancestor(*right, a)
        } else {
            false
        }
    }

    /// Returns a string representation of the vtree structure.
    pub fn to_string_tree(&self) -> String {
        self.format_subtree(self.root, 0)
    }

    fn format_subtree(&self, id: VtreeId, depth: usize) -> String {
        let indent = "  ".repeat(depth);
        match self.node(id) {
            VtreeNode::Leaf { var } => format!("{}x{}\n", indent, var),
            VtreeNode::Internal { left, right } => {
                let mut s = format!("{}({}):\n", indent, id);
                s.push_str(&self.format_subtree(*left, depth + 1));
                s.push_str(&self.format_subtree(*right, depth + 1));
                s
            }
        }
    }
}

impl Display for Vtree {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Vtree({} vars, {} nodes)", self.num_vars, self.nodes.len())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_balanced_vtree_2vars() {
        let vtree = Vtree::balanced(2);
        assert_eq!(vtree.num_vars(), 2);
        assert_eq!(vtree.num_nodes(), 3); // 2 leaves + 1 internal
        assert!(vtree.is_internal(vtree.root()));
    }

    #[test]
    fn test_balanced_vtree_4vars() {
        let vtree = Vtree::balanced(4);
        assert_eq!(vtree.num_vars(), 4);
        assert_eq!(vtree.num_nodes(), 7); // 4 leaves + 3 internal
        assert!(vtree.is_internal(vtree.root()));

        // Check structure
        let root = vtree.root();
        let left = vtree.left(root);
        let right = vtree.right(root);
        assert!(vtree.is_internal(left));
        assert!(vtree.is_internal(right));
    }

    #[test]
    fn test_right_linear_vtree() {
        let vtree = Vtree::right_linear(3);
        assert_eq!(vtree.num_vars(), 3);

        // Check that x1 is the leftmost leaf
        let root = vtree.root();
        let left = vtree.left(root);
        assert!(vtree.is_leaf(left));
        assert_eq!(vtree.var(left), 1);
    }

    #[test]
    fn test_left_linear_vtree() {
        let vtree = Vtree::left_linear(3);
        assert_eq!(vtree.num_vars(), 3);

        // Check that x3 is the rightmost leaf
        let root = vtree.root();
        let right = vtree.right(root);
        assert!(vtree.is_leaf(right));
        assert_eq!(vtree.var(right), 3);
    }

    #[test]
    fn test_variables_under() {
        let vtree = Vtree::balanced(4);
        let all_vars = vtree.variables_under(vtree.root());
        assert_eq!(all_vars, vec![1, 2, 3, 4]);
    }

    #[test]
    fn test_var_vtree() {
        let vtree = Vtree::balanced(4);
        for v in 1..=4 {
            let leaf = vtree.var_vtree(v);
            assert!(vtree.is_leaf(leaf));
            assert_eq!(vtree.var(leaf), v);
        }
    }

    #[test]
    fn test_lca() {
        let vtree = Vtree::balanced(4);
        let v1 = vtree.var_vtree(1);
        let v2 = vtree.var_vtree(2);
        let v3 = vtree.var_vtree(3);

        // LCA of x1 and x2 should be their common parent
        let lca12 = vtree.lca(v1, v2);
        assert!(vtree.is_ancestor(lca12, v1));
        assert!(vtree.is_ancestor(lca12, v2));

        // LCA of x1 and x3 should be higher
        let lca13 = vtree.lca(v1, v3);
        assert!(vtree.is_ancestor(lca13, lca12));
    }

    #[test]
    fn test_parent_relationships() {
        let vtree = Vtree::balanced(2);
        let root = vtree.root();

        // Root has no parent
        assert!(vtree.parent(root).is_none());

        // Children have root as parent
        let left = vtree.left(root);
        let right = vtree.right(root);
        assert_eq!(vtree.parent(left), Some(root));
        assert_eq!(vtree.parent(right), Some(root));
    }
}
