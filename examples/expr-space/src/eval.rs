//! Symbolic Semantic Evaluation
//!
//! This module provides tools for symbolically evaluating expressions
//! and partitioning the expression space by semantic equivalence.
//!
//! ## Key Insight
//!
//! For 2 Boolean variables, there are only 16 possible functions.
//! We can compute, for each input (x,y) ∈ {0,1}², the BDD representing
//! "which trees evaluate to 1 on this input".
//!
//! The intersection of these BDDs gives us the trees for each function.

use std::collections::HashMap;

use ananke_bdd::bdd::Bdd;
use ananke_bdd::reference::Ref;

use crate::encoding::{NodeTag, Position, VariableMap};

/// Symbolic evaluator for the expression space.
///
/// Computes BDDs representing which trees evaluate to 1 for each input.
pub struct SymbolicEvaluator<'a> {
    bdd: &'a Bdd,
    vars: &'a VariableMap,
    max_depth: u32,
    /// Cache: (position, depth, x_val, y_val) -> BDD of trees evaluating to 1
    cache: HashMap<(Position, u32, bool, bool), Ref>,
}

impl<'a> SymbolicEvaluator<'a> {
    pub fn new(bdd: &'a Bdd, vars: &'a VariableMap, max_depth: u32) -> Self {
        SymbolicEvaluator {
            bdd,
            vars,
            max_depth,
            cache: HashMap::new(),
        }
    }

    /// Compute BDD of trees that evaluate to 1 on input (x, y).
    ///
    /// This is restricted to trees in the given expression space.
    pub fn eval_to_true(&mut self, space: Ref, x: bool, y: bool) -> Ref {
        let eval_bdd = self.compute_eval(Position::ROOT, self.max_depth, x, y);
        self.bdd.eval(space * eval_bdd)
    }

    /// Compute BDD of trees that evaluate to 0 on input (x, y).
    pub fn eval_to_false(&mut self, space: Ref, x: bool, y: bool) -> Ref {
        let eval_true = self.eval_to_true(space, x, y);
        self.bdd.eval(space * (-eval_true))
    }

    /// Compute the evaluation BDD for a position.
    ///
    /// Returns BDD representing: "if this position is used, the subtree evaluates to 1".
    fn compute_eval(&mut self, pos: Position, depth: u32, x: bool, y: bool) -> Ref {
        let key = (pos, depth, x, y);
        if let Some(&cached) = self.cache.get(&key) {
            return cached;
        }

        let result = self.compute_eval_uncached(pos, depth, x, y);
        self.cache.insert(key, result);
        result
    }

    fn compute_eval_uncached(&mut self, pos: Position, depth: u32, x: bool, y: bool) -> Ref {
        // Leaf cases: check which leaf tag evaluates to 1
        let var_x = self.bdd.mk_var(self.vars.var(pos, NodeTag::VarX));
        let var_y = self.bdd.mk_var(self.vars.var(pos, NodeTag::VarY));
        let const1 = self.bdd.mk_var(self.vars.var(pos, NodeTag::Const1));
        // Note: Const0 always evaluates to 0, so we don't include it

        // VarX evaluates to 1 iff x is true AND position has VarX tag
        let var_x_eval = if x { var_x } else { self.bdd.zero() };
        let var_y_eval = if y { var_y } else { self.bdd.zero() };
        let const1_eval = const1; // 1 always evaluates to 1

        let leaf_eval = self.bdd.eval(var_x_eval + var_y_eval + const1_eval);

        // Also need to handle when VarX is present but x=false (evaluates to 0, not 1)
        // This is already handled: if x=false, var_x_eval = zero, so VarX tag doesn't contribute

        // Similarly for VarY
        // And we need the "evaluates to 0" case for the negations

        if depth == 0 {
            return leaf_eval;
        }

        // Unary: Not
        let not_tag = self.bdd.mk_var(self.vars.var(pos, NodeTag::Not));
        let left_eval_true = self.compute_eval(pos.left(), depth - 1, x, y);
        // Not evaluates to 1 iff child evaluates to 0
        // We need BDD for "child evaluates to 0" = all valid subtrees minus those evaluating to 1
        // But we don't have the space constraint here... we need to be more careful

        // Actually, for Not to evaluate to 1:
        // - We have Not tag at this position
        // - The left child evaluates to 0

        // "Left child evaluates to 0" means: the left subtree (whatever it is) gives 0
        // This is tricky because we need to know which trees are valid at left

        // Let's use a different approach: define eval_bdd as
        // "IF this position has tag T, THEN the subtree evaluates to V(T)"
        // where V(T) depends on the tag and children

        // For Not: V(Not) = NOT V(left_child)
        // We have left_eval_true = BDD of trees where left child evaluates to 1
        // So Not evaluates to 1 when left child evaluates to 0
        // But "evaluates to 0" is position-specific...

        // Let me reconsider. The key insight:
        // compute_eval(pos, depth, x, y) returns a BDD where:
        // - Variables are our (pos, tag) encoding
        // - The BDD is TRUE iff: given the tags at pos and descendants,
        //   the expression rooted at pos evaluates to 1 on input (x, y)

        // For leaves:
        // - VarX tag: true iff x
        // - VarY tag: true iff y
        // - Const0 tag: false
        // - Const1 tag: true

        // For Not:
        // - Not tag AND child evaluates to 0 (i.e., NOT child evaluates to 1)

        // The issue is: compute_eval gives us "evaluates to 1"
        // To get "evaluates to 0", we need the complement relative to "is a valid tree"

        // Simpler approach: compute both eval_to_1 and eval_to_0

        // Let's compute: for Not, it evaluates to 1 when child evaluates to 0
        // child_eval_false = (child is valid) AND NOT (child eval to 1)
        // But we don't have "child is valid" easily here

        // Alternative: assume all assignments are valid trees (filter separately)
        // Then: Not evaluates to 1 iff child does NOT evaluate to 1

        let not_eval = self.bdd.eval(not_tag * (-left_eval_true));

        // Binary ops
        let and_tag = self.bdd.mk_var(self.vars.var(pos, NodeTag::And));
        let or_tag = self.bdd.mk_var(self.vars.var(pos, NodeTag::Or));
        let xor_tag = self.bdd.mk_var(self.vars.var(pos, NodeTag::Xor));

        let right_eval_true = self.compute_eval(pos.right(), depth - 1, x, y);

        // And: 1 iff both children are 1
        let and_eval = self.bdd.eval(and_tag * left_eval_true * right_eval_true);

        // Or: 1 iff at least one child is 1
        let or_eval = self.bdd.eval(or_tag * (left_eval_true + right_eval_true));

        // Xor: 1 iff exactly one child is 1
        // XOR(a,b) = (a AND NOT b) OR (NOT a AND b)
        let xor_case1 = self.bdd.eval(left_eval_true * (-right_eval_true));
        let xor_case2 = self.bdd.eval((-left_eval_true) * right_eval_true);
        let xor_eval = self.bdd.eval(xor_tag * (xor_case1 + xor_case2));

        // Combine all cases
        self.bdd.eval(leaf_eval + not_eval + and_eval + or_eval + xor_eval)
    }

    /// Partition the expression space by truth table.
    ///
    /// Returns a map from 4-bit truth table to BDD of trees with that semantics.
    pub fn partition_by_semantics(&mut self, space: Ref) -> HashMap<u8, Ref> {
        let mut partitions = HashMap::new();

        // Compute eval BDDs for each input
        let eval_00 = self.eval_to_true(space, false, false);
        let eval_01 = self.eval_to_true(space, false, true);
        let eval_10 = self.eval_to_true(space, true, false);
        let eval_11 = self.eval_to_true(space, true, true);

        // For each of 16 truth tables
        for tt in 0u8..16 {
            let bit0 = (tt & 1) != 0; // f(0,0)
            let bit1 = (tt & 2) != 0; // f(0,1)
            let bit2 = (tt & 4) != 0; // f(1,0)
            let bit3 = (tt & 8) != 0; // f(1,1)

            let cond_00 = if bit0 { eval_00 } else { self.bdd.eval(space * (-eval_00)) };
            let cond_01 = if bit1 { eval_01 } else { self.bdd.eval(space * (-eval_01)) };
            let cond_10 = if bit2 { eval_10 } else { self.bdd.eval(space * (-eval_10)) };
            let cond_11 = if bit3 { eval_11 } else { self.bdd.eval(space * (-eval_11)) };

            let partition = self.bdd.eval(cond_00 * cond_01 * cond_10 * cond_11);
            partitions.insert(tt, partition);
        }

        partitions
    }
}

/// Human-readable name for a truth table.
///
/// Truth table encoding: bit i = f(x, y) where i = 2*x + y
/// - bit 0: f(0,0)
/// - bit 1: f(0,1)
/// - bit 2: f(1,0)
/// - bit 3: f(1,1)
pub fn truth_table_name(tt: u8) -> &'static str {
    match tt {
        0b0000 => "FALSE",  // 0000: [0,0,0,0]
        0b0001 => "AND",    // 0001: [0,0,0,1] - true only for (1,1)
        0b0010 => "x ∧ ¬y", // 0010: [0,0,1,0]
        0b0011 => "x",      // 0011: [0,0,1,1] - true for x=1
        0b0100 => "¬x ∧ y", // 0100: [0,1,0,0]
        0b0101 => "y",      // 0101: [0,1,0,1] - true for y=1
        0b0110 => "XOR",    // 0110: [0,1,1,0]
        0b0111 => "OR",     // 0111: [0,1,1,1]
        0b1000 => "NOR",    // 1000: [1,0,0,0]
        0b1001 => "XNOR",   // 1001: [1,0,0,1]
        0b1010 => "¬y",     // 1010: [1,0,1,0]
        0b1011 => "x ∨ ¬y", // 1011: [1,0,1,1]
        0b1100 => "¬x",     // 1100: [1,1,0,0]
        0b1101 => "¬x ∨ y", // 1101: [1,1,0,1]
        0b1110 => "NAND",   // 1110: [1,1,1,0]
        0b1111 => "TRUE",   // 1111: [1,1,1,1]
        _ => "???",
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
    fn test_partition_covers_all() {
        let bdd = Bdd::default();
        let vars = VariableMap::new(1);
        let mut builder = ExpressionSpaceBuilder::new(&bdd, &vars, 1);
        let space = builder.build();

        let mut eval = SymbolicEvaluator::new(&bdd, &vars, 1);
        let partitions = eval.partition_by_semantics(space);

        // Sum of all partition sizes should equal total space size
        let total: num_bigint::BigUint = partitions.values().map(|&p| bdd.sat_count(p, vars.num_vars())).sum();

        let space_size = bdd.sat_count(space, vars.num_vars());
        assert_eq!(total, space_size);
    }

    #[test]
    fn test_partitions_disjoint() {
        let bdd = Bdd::default();
        let vars = VariableMap::new(1);
        let mut builder = ExpressionSpaceBuilder::new(&bdd, &vars, 1);
        let space = builder.build();

        let mut eval = SymbolicEvaluator::new(&bdd, &vars, 1);
        let partitions = eval.partition_by_semantics(space);

        // Each pair of partitions should be disjoint
        for (&tt1, &p1) in &partitions {
            for (&tt2, &p2) in &partitions {
                if tt1 < tt2 {
                    let intersection = bdd.eval(p1 * p2);
                    assert!(bdd.is_zero(intersection), "Partitions {} and {} overlap", tt1, tt2);
                }
            }
        }
    }
}
