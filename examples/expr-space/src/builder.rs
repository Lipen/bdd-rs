//! Expression Space Builder
//!
//! Constructs the BDD representing all valid expression trees up to a given depth.
//!
//! ## Algorithm
//!
//! We build the expression space recursively from leaves to root:
//!
//! ```text
//! Space[pos, depth=0] = Leaf[pos]
//! Space[pos, depth>0] = Leaf[pos] ∪ Unary[pos] ∪ Binary[pos]
//! ```
//!
//! Where:
//! - `Leaf[pos]` = one of {VarX, VarY, Const0, Const1} with empty children
//! - `Unary[pos]` = Not with valid left child, empty right
//! - `Binary[pos]` = {And, Or, Xor} with valid left and right children
//!
//! ## Constraint: Exactly-One-Tag
//!
//! For each position, exactly one tag must be true (mutual exclusion).
//! Unused positions have all tags false.

use std::collections::HashMap;

use ananke_bdd::bdd::Bdd;
use ananke_bdd::reference::Ref;

use crate::encoding::{NodeTag, Position, VariableMap};

/// Builder for the expression space BDD.
///
/// Constructs a BDD representing all syntactically valid expression trees
/// up to a given depth. The BDD encodes the constraint that each position
/// has exactly one tag (or no tag for unused subtrees).
pub struct ExpressionSpaceBuilder<'a> {
    bdd: &'a Bdd,
    vars: &'a VariableMap,
    max_depth: u32,
    /// Cache for expression space at each position
    space_cache: HashMap<(Position, u32), Ref>,
    /// Cache for "subtree empty" constraints
    empty_cache: HashMap<(Position, u32), Ref>,
}

impl<'a> ExpressionSpaceBuilder<'a> {
    /// Create a new builder.
    pub fn new(bdd: &'a Bdd, vars: &'a VariableMap, max_depth: u32) -> Self {
        ExpressionSpaceBuilder {
            bdd,
            vars,
            max_depth,
            space_cache: HashMap::new(),
            empty_cache: HashMap::new(),
        }
    }

    /// Build BDD for all valid expression trees.
    pub fn build(&mut self) -> Ref {
        self.build_at(Position::ROOT, self.max_depth)
    }

    /// Build BDD for subtrees rooted at `pos` with remaining depth budget.
    fn build_at(&mut self, pos: Position, depth: u32) -> Ref {
        let key = (pos, depth);
        if let Some(&cached) = self.space_cache.get(&key) {
            return cached;
        }

        let result = if depth == 0 {
            // Only leaves allowed at max depth
            self.build_leaves(pos)
        } else {
            // Leaves OR unary OR binary
            let leaves = self.build_leaves(pos);
            let unary = self.build_unary(pos, depth);
            let binary = self.build_binary(pos, depth);
            self.bdd.eval(leaves + unary + binary)
        };

        self.space_cache.insert(key, result);
        result
    }

    /// Build constraint: exactly this tag at position (all others false).
    fn build_only_tag(&self, pos: Position, chosen_tag: NodeTag) -> Ref {
        let chosen_var = self.bdd.mk_var(self.vars.var(pos, chosen_tag));
        let mut result = chosen_var;
        for &tag in &NodeTag::ALL {
            if tag != chosen_tag {
                let v = self.bdd.mk_var(self.vars.var(pos, tag));
                result = self.bdd.eval(result * (-v));
            }
        }
        result
    }

    /// Build constraint: all tags at position are false.
    fn build_all_tags_false(&self, pos: Position) -> Ref {
        let mut result = self.bdd.one();
        for &tag in &NodeTag::ALL {
            let v = self.bdd.mk_var(self.vars.var(pos, tag));
            result = self.bdd.eval(result * (-v));
        }
        result
    }

    /// Build constraint: entire subtree rooted at pos is empty.
    fn build_subtree_empty(&mut self, pos: Position, depth: u32) -> Ref {
        let key = (pos, depth);
        if let Some(&cached) = self.empty_cache.get(&key) {
            return cached;
        }

        let this_empty = self.build_all_tags_false(pos);
        let result = if depth == 0 {
            this_empty
        } else {
            let left_empty = self.build_subtree_empty(pos.left(), depth - 1);
            let right_empty = self.build_subtree_empty(pos.right(), depth - 1);
            self.bdd.eval(this_empty * left_empty * right_empty)
        };

        self.empty_cache.insert(key, result);
        result
    }

    /// BDD for leaf nodes at position (with empty children).
    fn build_leaves(&mut self, pos: Position) -> Ref {
        // Any of the four leaf tags
        let mut result = self.bdd.zero();
        for &tag in &NodeTag::ALL_LEAVES {
            let this_tag = self.build_only_tag(pos, tag);
            result = self.bdd.eval(result + this_tag);
        }

        // If not at bottom level, children must be empty
        let pos_depth = pos.depth();
        if pos_depth < self.max_depth {
            let remaining = self.max_depth - pos_depth - 1;
            let left_empty = self.build_subtree_empty(pos.left(), remaining);
            let right_empty = self.build_subtree_empty(pos.right(), remaining);
            result = self.bdd.eval(result * left_empty * right_empty);
        }
        result
    }

    /// BDD for unary (Not) at position.
    fn build_unary(&mut self, pos: Position, depth: u32) -> Ref {
        let not_tag = self.build_only_tag(pos, NodeTag::Not);
        let left_child = self.build_at(pos.left(), depth - 1);
        // Right subtree must be empty
        let right_empty = self.build_subtree_empty(pos.right(), depth - 1);
        self.bdd.eval(not_tag * left_child * right_empty)
    }

    /// BDD for binary ops at position.
    fn build_binary(&mut self, pos: Position, depth: u32) -> Ref {
        // One of the binary operators
        let mut op_choice = self.bdd.zero();
        for &tag in &NodeTag::ALL_BINARY {
            let tag_only = self.build_only_tag(pos, tag);
            op_choice = self.bdd.eval(op_choice + tag_only);
        }

        let left_child = self.build_at(pos.left(), depth - 1);
        let right_child = self.build_at(pos.right(), depth - 1);

        self.bdd.eval(op_choice * left_child * right_child)
    }

    /// Get statistics about the build process.
    pub fn stats(&self) -> BuilderStats {
        BuilderStats {
            space_cache_size: self.space_cache.len(),
            empty_cache_size: self.empty_cache.len(),
        }
    }
}

/// Statistics from the builder.
#[derive(Debug, Clone)]
pub struct BuilderStats {
    pub space_cache_size: usize,
    pub empty_cache_size: usize,
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    fn count_trees(bdd: &Bdd, f: Ref, num_vars: usize) -> num_bigint::BigUint {
        bdd.sat_count(f, num_vars)
    }

    #[test]
    fn test_expr_space_depth_0() {
        let bdd = Bdd::default();
        let vars = VariableMap::new(0);
        let mut builder = ExpressionSpaceBuilder::new(&bdd, &vars, 0);
        let space = builder.build();

        // At depth 0, only leaves: VarX, VarY, Const0, Const1 = 4 trees
        let count = count_trees(&bdd, space, vars.num_vars());
        assert_eq!(count, 4u32.into());
    }

    #[test]
    fn test_expr_space_depth_1() {
        let bdd = Bdd::default();
        let vars = VariableMap::new(1);
        let mut builder = ExpressionSpaceBuilder::new(&bdd, &vars, 1);
        let space = builder.build();

        // Depth 1:
        // - 4 leaves at root
        // - Not(4 leaves) = 4
        // - Binary(3 ops × 4 × 4) = 48
        // Total = 4 + 4 + 48 = 56
        let count = count_trees(&bdd, space, vars.num_vars());
        assert_eq!(count, 56u32.into());
    }

    #[test]
    fn test_expr_space_depth_2() {
        let bdd = Bdd::default();
        let vars = VariableMap::new(2);
        let mut builder = ExpressionSpaceBuilder::new(&bdd, &vars, 2);
        let space = builder.build();

        // Let T(d) = number of trees of depth exactly d
        // T(0) = 4 (leaves)
        // T(1) = 4 + 1*4 + 3*4*4 = 4 + 4 + 48 = 56
        //
        // For depth 2, we need trees where root has depth contribution:
        // Let E(d) = trees up to depth d
        // E(0) = 4
        // E(1) = 4 + 1*E(0) + 3*E(0)*E(0) = 4 + 4 + 48 = 56
        // E(2) = 4 + 1*E(1) + 3*E(1)*E(1) = 4 + 56 + 3*56*56 = 4 + 56 + 9408 = 9468
        let count = count_trees(&bdd, space, vars.num_vars());
        assert_eq!(count, 9468u32.into());
    }

    #[test]
    fn test_enumeration_depth_0() {
        let bdd = Bdd::default();
        let vars = VariableMap::new(0);
        let mut builder = ExpressionSpaceBuilder::new(&bdd, &vars, 0);
        let space = builder.build();

        let paths: Vec<_> = bdd.paths(space).collect();
        assert_eq!(paths.len(), 4);
    }

    #[test]
    fn test_enumeration_depth_1() {
        let bdd = Bdd::default();
        let vars = VariableMap::new(1);
        let mut builder = ExpressionSpaceBuilder::new(&bdd, &vars, 1);
        let space = builder.build();

        let paths: Vec<_> = bdd.paths(space).collect();
        assert_eq!(paths.len(), 56);
    }
}
