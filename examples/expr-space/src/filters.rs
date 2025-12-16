//! Symbolic Filters for Expression Space
//!
//! This module provides BDD-based filters that remove redundant expressions:
//!
//! - **Commutativity**: `And(a,b)` ≡ `And(b,a)` → keep only one
//! - **Idempotence**: `And(e,e)` ≡ `e` → exclude
//! - **Double negation**: `Not(Not(e))` ≡ `e` → exclude
//! - **Constant folding**: `And(0,e)` ≡ `0` → exclude
//!
//! Each filter is a BDD constraint that can be ANDed with the expression space.

use ananke_bdd::bdd::Bdd;
use ananke_bdd::reference::Ref;

use crate::encoding::{NodeTag, VariableMap};

/// A collection of symbolic filters for the expression space.
pub struct Filters<'a> {
    bdd: &'a Bdd,
    vars: &'a VariableMap,
    max_depth: u32,
}

impl<'a> Filters<'a> {
    /// Create a new filter collection.
    pub fn new(bdd: &'a Bdd, vars: &'a VariableMap, max_depth: u32) -> Self {
        Filters { bdd, vars, max_depth }
    }

    /// Build filter excluding double negation: Not(Not(e)).
    ///
    /// For each position with Not, its left child cannot also be Not.
    pub fn no_double_negation(&self) -> Ref {
        let mut result = self.bdd.one();

        for &pos in self.vars.positions() {
            if pos.depth() >= self.max_depth {
                continue; // No children possible
            }

            let not_at_pos = self.bdd.mk_var(self.vars.var(pos, NodeTag::Not));
            let not_at_left = self.bdd.mk_var(self.vars.var(pos.left(), NodeTag::Not));

            // Exclude: Not at pos AND Not at left child
            // Constraint: ¬(not_at_pos ∧ not_at_left)
            let excluded = self.bdd.eval(not_at_pos * not_at_left);
            result = self.bdd.eval(result * (-excluded));
        }

        result
    }

    /// Build filter excluding trivial constant expressions.
    ///
    /// - `Not(0)` → exclude (equals 1)
    /// - `Not(1)` → exclude (equals 0)
    /// - `And(0, e)` or `And(e, 0)` → exclude (equals 0)
    /// - `And(1, e)` or `And(e, 1)` → exclude (equals e)
    /// - `Or(1, e)` or `Or(e, 1)` → exclude (equals 1)
    /// - `Or(0, e)` or `Or(e, 0)` → exclude (equals e)
    /// - `Xor(0, e)` or `Xor(e, 0)` → exclude (equals e)
    /// - `Xor(1, e)` or `Xor(e, 1)` → exclude (equals Not(e))
    pub fn no_constant_ops(&self) -> Ref {
        let mut result = self.bdd.one();

        for &pos in self.vars.positions() {
            if pos.depth() >= self.max_depth {
                continue;
            }

            let left = pos.left();
            let right = pos.right();

            // Not(0) and Not(1)
            let not_var = self.bdd.mk_var(self.vars.var(pos, NodeTag::Not));
            let const0_left = self.bdd.mk_var(self.vars.var(left, NodeTag::Const0));
            let const1_left = self.bdd.mk_var(self.vars.var(left, NodeTag::Const1));

            let not_const0 = self.bdd.eval(not_var * const0_left);
            let not_const1 = self.bdd.eval(not_var * const1_left);
            result = self.bdd.eval(result * (-not_const0) * (-not_const1));

            // Binary ops with constants
            for &op in &NodeTag::ALL_BINARY {
                let op_var = self.bdd.mk_var(self.vars.var(pos, op));
                let const0_right = self.bdd.mk_var(self.vars.var(right, NodeTag::Const0));
                let const1_right = self.bdd.mk_var(self.vars.var(right, NodeTag::Const1));

                // op(0, e) and op(e, 0)
                let op_const0_left = self.bdd.eval(op_var * const0_left);
                let op_const0_right = self.bdd.eval(op_var * const0_right);

                // op(1, e) and op(e, 1)
                let op_const1_left = self.bdd.eval(op_var * const1_left);
                let op_const1_right = self.bdd.eval(op_var * const1_right);

                result = self
                    .bdd
                    .eval(result * (-op_const0_left) * (-op_const0_right) * (-op_const1_left) * (-op_const1_right));
            }
        }

        result
    }

    /// Build filter excluding idempotent expressions: `And(e,e)`, `Or(e,e)`.
    ///
    /// This requires checking structural equality of subtrees, which is expensive.
    /// For now, we use a simpler approximation: exclude cases where left and right
    /// have the same tag at corresponding positions (complete structural match).
    ///
    /// Full implementation would require comparing entire subtree structures.
    pub fn no_idempotent_simple(&self) -> Ref {
        let mut result = self.bdd.one();

        for &pos in self.vars.positions() {
            if pos.depth() >= self.max_depth {
                continue;
            }

            let left = pos.left();
            let right = pos.right();

            // For And and Or (idempotent ops), exclude if left == right at leaf level
            for &op in &[NodeTag::And, NodeTag::Or] {
                let op_var = self.bdd.mk_var(self.vars.var(pos, op));

                // Simple case: both children are the same leaf
                for &leaf_tag in &NodeTag::ALL_LEAVES {
                    let leaf_left = self.bdd.mk_var(self.vars.var(left, leaf_tag));
                    let leaf_right = self.bdd.mk_var(self.vars.var(right, leaf_tag));

                    // Exclude: op AND same_leaf_left AND same_leaf_right
                    let excluded = self.bdd.eval(op_var * leaf_left * leaf_right);
                    result = self.bdd.eval(result * (-excluded));
                }
            }
        }

        result
    }

    /// Build strict commutativity filter for binary operators.
    ///
    /// For commutative ops (And, Or, Xor), we enforce tag-based ordering:
    /// exclude when left_tag > right_tag, INCLUDING when tags are equal (keep only left_tag <= right_tag).
    pub fn commutativity_simple(&self) -> Ref {
        let mut result = self.bdd.one();

        for &pos in self.vars.positions() {
            if pos.depth() >= self.max_depth {
                continue;
            }

            let left = pos.left();
            let right = pos.right();

            for &op in &NodeTag::COMMUTATIVE {
                let op_var = self.bdd.mk_var(self.vars.var(pos, op));

                // Exclude when left_tag > right_tag (strict left <= right ordering)
                for &tag_left in &NodeTag::ALL {
                    for &tag_right in &NodeTag::ALL {
                        if (tag_left as u8) > (tag_right as u8) {
                            let left_var = self.bdd.mk_var(self.vars.var(left, tag_left));
                            let right_var = self.bdd.mk_var(self.vars.var(right, tag_right));

                            // Exclude: op AND tag_left > tag_right
                            let excluded = self.bdd.eval(op_var * left_var * right_var);
                            result = self.bdd.eval(result * (-excluded));
                        }
                    }
                }
            }
        }

        result
    }

    /// Apply all simple filters to the expression space.
    pub fn apply_all_simple(&self, space: Ref) -> Ref {
        let no_double_neg = self.no_double_negation();
        let no_const = self.no_constant_ops();
        let no_idemp = self.no_idempotent_simple();
        let comm = self.commutativity_simple();

        self.bdd.eval(space * no_double_neg * no_const * no_idemp * comm)
    }
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use crate::builder::ExpressionSpaceBuilder;

    #[test]
    fn test_no_double_negation() {
        let bdd = Bdd::default();
        let vars = VariableMap::new(2);
        let filters = Filters::new(&bdd, &vars, 2);

        let mut builder = ExpressionSpaceBuilder::new(&bdd, &vars, 2);
        let space = builder.build();

        let filtered = bdd.eval(space * filters.no_double_negation());

        // Filtered should have fewer trees
        let count_before = bdd.sat_count(space, vars.num_vars());
        let count_after = bdd.sat_count(filtered, vars.num_vars());
        assert!(count_after < count_before);
    }

    #[test]
    fn test_no_constant_ops() {
        let bdd = Bdd::default();
        let vars = VariableMap::new(1);
        let filters = Filters::new(&bdd, &vars, 1);

        let mut builder = ExpressionSpaceBuilder::new(&bdd, &vars, 1);
        let space = builder.build();

        let filtered = bdd.eval(space * filters.no_constant_ops());

        let count_before = bdd.sat_count(space, vars.num_vars());
        let count_after = bdd.sat_count(filtered, vars.num_vars());
        assert!(count_after < count_before);
    }

    #[test]
    fn test_commutativity_filter() {
        let bdd = Bdd::default();
        let vars = VariableMap::new(1);
        let filters = Filters::new(&bdd, &vars, 1);

        let mut builder = ExpressionSpaceBuilder::new(&bdd, &vars, 1);
        let space = builder.build();

        let filtered = bdd.eval(space * filters.commutativity_simple());

        let count_before = bdd.sat_count(space, vars.num_vars());
        let count_after = bdd.sat_count(filtered, vars.num_vars());

        // Should reduce by roughly half for binary ops
        assert!(count_after < count_before);
    }
}
