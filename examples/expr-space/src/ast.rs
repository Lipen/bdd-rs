//! AST Representation and Reconstruction
//!
//! This module provides the `Expr` type representing Boolean expressions,
//! and functions to reconstruct ASTs from BDD satisfying assignments.

use std::collections::HashMap;
use std::fmt;

use ananke_bdd::types::Lit;

use crate::encoding::{NodeTag, Position, VariableMap};

/// A Boolean expression tree.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Expr {
    /// Variable x
    VarX,
    /// Variable y
    VarY,
    /// Constant false
    Const0,
    /// Constant true
    Const1,
    /// Negation
    Not(Box<Expr>),
    /// Conjunction
    And(Box<Expr>, Box<Expr>),
    /// Disjunction
    Or(Box<Expr>, Box<Expr>),
    /// Exclusive or
    Xor(Box<Expr>, Box<Expr>),
}

impl Expr {
    /// Depth of the expression tree (0 for leaves).
    pub fn depth(&self) -> usize {
        match self {
            Expr::VarX | Expr::VarY | Expr::Const0 | Expr::Const1 => 0,
            Expr::Not(e) => 1 + e.depth(),
            Expr::And(l, r) | Expr::Or(l, r) | Expr::Xor(l, r) => 1 + l.depth().max(r.depth()),
        }
    }

    /// Size of the expression tree (number of nodes).
    pub fn size(&self) -> usize {
        match self {
            Expr::VarX | Expr::VarY | Expr::Const0 | Expr::Const1 => 1,
            Expr::Not(e) => 1 + e.size(),
            Expr::And(l, r) | Expr::Or(l, r) | Expr::Xor(l, r) => 1 + l.size() + r.size(),
        }
    }

    /// Evaluate the expression on given inputs.
    pub fn eval(&self, x: bool, y: bool) -> bool {
        match self {
            Expr::VarX => x,
            Expr::VarY => y,
            Expr::Const0 => false,
            Expr::Const1 => true,
            Expr::Not(e) => !e.eval(x, y),
            Expr::And(l, r) => l.eval(x, y) && r.eval(x, y),
            Expr::Or(l, r) => l.eval(x, y) || r.eval(x, y),
            Expr::Xor(l, r) => l.eval(x, y) ^ r.eval(x, y),
        }
    }

    /// Compute the 4-bit truth table for this expression.
    ///
    /// Returns a u8 where bit i represents the output for input i:
    /// - bit 0: f(1,1)
    /// - bit 1: f(1,0)
    /// - bit 2: f(0,1)
    /// - bit 3: f(0,0)
    ///
    /// This gives natural ordering where valuations [0,0], [0,1], [1,0], [1,1]
    /// correspond to bits in the string representation [3,2,1,0]
    /// e.g., AND has truth table 0001 (only true for [1,1])
    pub fn truth_table(&self) -> u8 {
        let mut tt = 0u8;
        if self.eval(true, true) {
            tt |= 1; // bit 0
        }
        if self.eval(true, false) {
            tt |= 2; // bit 1
        }
        if self.eval(false, true) {
            tt |= 4; // bit 2
        }
        if self.eval(false, false) {
            tt |= 8; // bit 3
        }
        tt
    }
}

impl fmt::Display for Expr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Expr::VarX => write!(f, "x"),
            Expr::VarY => write!(f, "y"),
            Expr::Const0 => write!(f, "0"),
            Expr::Const1 => write!(f, "1"),
            Expr::Not(e) => write!(f, "¬{}", e),
            Expr::And(l, r) => write!(f, "({} ∧ {})", l, r),
            Expr::Or(l, r) => write!(f, "({} ∨ {})", l, r),
            Expr::Xor(l, r) => write!(f, "({} ⊕ {})", l, r),
        }
    }
}

/// Reconstruct an AST from a BDD path (satisfying assignment).
///
/// The path is a list of literals indicating which (position, tag) variables are true/false.
pub fn reconstruct_ast(path: &[Lit], vars: &VariableMap) -> Option<Expr> {
    // Build a map from position to active tag
    let mut pos_to_tag: HashMap<Position, NodeTag> = HashMap::new();

    for lit in path {
        if lit.is_positive() {
            let (pos, tag) = vars.decode(lit.var().id());
            pos_to_tag.insert(pos, tag);
        }
    }

    reconstruct_at(Position::ROOT, &pos_to_tag)
}

fn reconstruct_at(pos: Position, pos_to_tag: &HashMap<Position, NodeTag>) -> Option<Expr> {
    let tag = pos_to_tag.get(&pos)?;

    match tag {
        NodeTag::VarX => Some(Expr::VarX),
        NodeTag::VarY => Some(Expr::VarY),
        NodeTag::Const0 => Some(Expr::Const0),
        NodeTag::Const1 => Some(Expr::Const1),
        NodeTag::Not => {
            let child = reconstruct_at(pos.left(), pos_to_tag)?;
            Some(Expr::Not(Box::new(child)))
        }
        NodeTag::And => {
            let left = reconstruct_at(pos.left(), pos_to_tag)?;
            let right = reconstruct_at(pos.right(), pos_to_tag)?;
            Some(Expr::And(Box::new(left), Box::new(right)))
        }
        NodeTag::Or => {
            let left = reconstruct_at(pos.left(), pos_to_tag)?;
            let right = reconstruct_at(pos.right(), pos_to_tag)?;
            Some(Expr::Or(Box::new(left), Box::new(right)))
        }
        NodeTag::Xor => {
            let left = reconstruct_at(pos.left(), pos_to_tag)?;
            let right = reconstruct_at(pos.right(), pos_to_tag)?;
            Some(Expr::Xor(Box::new(left), Box::new(right)))
        }
    }
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_expr_depth() {
        assert_eq!(Expr::VarX.depth(), 0);
        assert_eq!(Expr::Not(Box::new(Expr::VarX)).depth(), 1);
        assert_eq!(Expr::And(Box::new(Expr::VarX), Box::new(Expr::VarY)).depth(), 1);
        assert_eq!(
            Expr::And(Box::new(Expr::Not(Box::new(Expr::VarX))), Box::new(Expr::VarY)).depth(),
            2
        );
    }

    #[test]
    fn test_expr_size() {
        assert_eq!(Expr::VarX.size(), 1);
        assert_eq!(Expr::Not(Box::new(Expr::VarX)).size(), 2);
        assert_eq!(Expr::And(Box::new(Expr::VarX), Box::new(Expr::VarY)).size(), 3);
    }

    #[test]
    fn test_expr_eval() {
        let and_xy = Expr::And(Box::new(Expr::VarX), Box::new(Expr::VarY));
        assert!(!and_xy.eval(false, false));
        assert!(!and_xy.eval(false, true));
        assert!(!and_xy.eval(true, false));
        assert!(and_xy.eval(true, true));

        let or_xy = Expr::Or(Box::new(Expr::VarX), Box::new(Expr::VarY));
        assert!(!or_xy.eval(false, false));
        assert!(or_xy.eval(false, true));
        assert!(or_xy.eval(true, false));
        assert!(or_xy.eval(true, true));

        let xor_xy = Expr::Xor(Box::new(Expr::VarX), Box::new(Expr::VarY));
        assert!(!xor_xy.eval(false, false));
        assert!(xor_xy.eval(false, true));
        assert!(xor_xy.eval(true, false));
        assert!(!xor_xy.eval(true, true));
    }

    #[test]
    fn test_truth_table() {
        assert_eq!(Expr::Const0.truth_table(), 0b0000);
        assert_eq!(Expr::Const1.truth_table(), 0b1111);
        assert_eq!(Expr::VarX.truth_table(), 0b0011);
        assert_eq!(Expr::VarY.truth_table(), 0b0101);

        let and_xy = Expr::And(Box::new(Expr::VarX), Box::new(Expr::VarY));
        assert_eq!(and_xy.truth_table(), 0b0001);

        let or_xy = Expr::Or(Box::new(Expr::VarX), Box::new(Expr::VarY));
        assert_eq!(or_xy.truth_table(), 0b0111);

        let xor_xy = Expr::Xor(Box::new(Expr::VarX), Box::new(Expr::VarY));
        assert_eq!(xor_xy.truth_table(), 0b0110);
    }
}
