//! AST Encoding Types for BDD Representation
//!
//! This module defines the encoding scheme that maps expression trees to BDD variables.
//!
//! ## Encoding Strategy
//!
//! We use a **positional skeleton** — a full binary tree up to depth d.
//! Each position can hold one of several node tags.
//!
//! For each `(position, tag)` pair, we allocate a BDD variable.
//! A valid AST satisfies: exactly one tag is true per used position,
//! and unused subtrees have all tags false.

use std::collections::HashMap;
use std::fmt;

// ============================================================================
// Position
// ============================================================================

/// A position in the AST skeleton (path from root).
///
/// Encoded as a u8 with a sentinel bit marking the end of the path.
/// - ROOT = 0b1
/// - L = 0b10 (left child of root)
/// - R = 0b11 (right child of root)
/// - LL = 0b100, LR = 0b101, RL = 0b110, RR = 0b111
///
/// This encoding supports trees up to depth 7 (2^7 = 128 positions).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Position(u8);

impl Position {
    /// The root position (empty path).
    pub const ROOT: Position = Position(0b1);

    /// Go to left child (append 0 to path).
    #[inline]
    pub fn left(self) -> Position {
        Position((self.0 << 1) | 0)
    }

    /// Go to right child (append 1 to path).
    #[inline]
    pub fn right(self) -> Position {
        Position((self.0 << 1) | 1)
    }

    /// Depth of this position (root = 0).
    #[inline]
    pub fn depth(self) -> u32 {
        (u8::BITS - self.0.leading_zeros()).saturating_sub(1)
    }

    /// Check if this is the root position.
    #[inline]
    pub fn is_root(self) -> bool {
        self == Self::ROOT
    }

    /// Generate all positions up to given depth (BFS order).
    pub fn all_up_to_depth(max_depth: u32) -> Vec<Position> {
        let mut positions = vec![Position::ROOT];
        let mut i = 0;
        while i < positions.len() {
            let pos = positions[i];
            if pos.depth() < max_depth {
                positions.push(pos.left());
                positions.push(pos.right());
            }
            i += 1;
        }
        positions
    }

    /// Get the raw encoding value.
    #[inline]
    pub fn raw(self) -> u8 {
        self.0
    }
}

impl fmt::Display for Position {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if *self == Position::ROOT {
            return write!(f, "ε");
        }
        let mut path = String::new();
        let mut val = self.0;
        while val > 1 {
            if val & 1 == 0 {
                path.insert(0, 'L');
            } else {
                path.insert(0, 'R');
            }
            val >>= 1;
        }
        write!(f, "{}", path)
    }
}

// ============================================================================
// NodeTag
// ============================================================================

/// Node types in our expression language.
///
/// The language consists of:
/// - **Leaves**: Variables (x, y) and constants (0, 1)
/// - **Unary**: Negation (Not)
/// - **Binary**: Conjunction (And), Disjunction (Or), Exclusive-Or (Xor)
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[repr(u8)]
pub enum NodeTag {
    // Leaves (arity 0)
    VarX = 0,
    VarY = 1,
    Const0 = 2,
    Const1 = 3,
    // Unary (arity 1)
    Not = 4,
    // Binary (arity 2)
    And = 5,
    Or = 6,
    Xor = 7,
}

impl NodeTag {
    /// All leaf node types.
    pub const ALL_LEAVES: [NodeTag; 4] = [NodeTag::VarX, NodeTag::VarY, NodeTag::Const0, NodeTag::Const1];

    /// All unary operators.
    pub const ALL_UNARY: [NodeTag; 1] = [NodeTag::Not];

    /// All binary operators.
    pub const ALL_BINARY: [NodeTag; 3] = [NodeTag::And, NodeTag::Or, NodeTag::Xor];

    /// All commutative binary operators.
    pub const COMMUTATIVE: [NodeTag; 3] = [NodeTag::And, NodeTag::Or, NodeTag::Xor];

    /// All node types.
    pub const ALL: [NodeTag; 8] = [
        NodeTag::VarX,
        NodeTag::VarY,
        NodeTag::Const0,
        NodeTag::Const1,
        NodeTag::Not,
        NodeTag::And,
        NodeTag::Or,
        NodeTag::Xor,
    ];

    /// Number of node types.
    pub const COUNT: usize = 8;

    /// Check if this is a leaf node.
    #[inline]
    pub fn is_leaf(self) -> bool {
        matches!(self, NodeTag::VarX | NodeTag::VarY | NodeTag::Const0 | NodeTag::Const1)
    }

    /// Check if this is a unary operator.
    #[inline]
    pub fn is_unary(self) -> bool {
        matches!(self, NodeTag::Not)
    }

    /// Check if this is a binary operator.
    #[inline]
    pub fn is_binary(self) -> bool {
        matches!(self, NodeTag::And | NodeTag::Or | NodeTag::Xor)
    }

    /// Check if this operator is commutative.
    #[inline]
    pub fn is_commutative(self) -> bool {
        matches!(self, NodeTag::And | NodeTag::Or | NodeTag::Xor)
    }

    /// Check if this operator is idempotent (op(x,x) = x).
    #[inline]
    pub fn is_idempotent(self) -> bool {
        matches!(self, NodeTag::And | NodeTag::Or)
    }

    /// Arity of this node type.
    #[inline]
    pub fn arity(self) -> usize {
        if self.is_leaf() {
            0
        } else if self.is_unary() {
            1
        } else {
            2
        }
    }
}

impl fmt::Display for NodeTag {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            NodeTag::VarX => write!(f, "x"),
            NodeTag::VarY => write!(f, "y"),
            NodeTag::Const0 => write!(f, "0"),
            NodeTag::Const1 => write!(f, "1"),
            NodeTag::Not => write!(f, "¬"),
            NodeTag::And => write!(f, "∧"),
            NodeTag::Or => write!(f, "∨"),
            NodeTag::Xor => write!(f, "⊕"),
        }
    }
}

// ============================================================================
// VariableMap
// ============================================================================

/// Maps (Position, NodeTag) pairs to BDD variable IDs.
///
/// Variable ordering: positions are ordered by depth (BFS), then by path.
/// Within a position, tags are ordered by their discriminant.
///
/// This ordering tends to keep related decisions close in the BDD,
/// which can improve compression.
pub struct VariableMap {
    max_depth: u32,
    positions: Vec<Position>,
    pos_to_vars: HashMap<Position, [u32; NodeTag::COUNT]>,
    var_to_atom: Vec<(Position, NodeTag)>,
}

impl VariableMap {
    /// Create a new variable map for trees up to the given depth.
    pub fn new(max_depth: u32) -> Self {
        let positions = Position::all_up_to_depth(max_depth);
        let mut pos_to_vars = HashMap::new();
        // var 0 is unused in BDD (reserved), so we start from 1
        let mut var_to_atom = vec![(Position::ROOT, NodeTag::VarX)];

        let mut next_var = 1u32;

        for &pos in &positions {
            let mut vars = [0u32; NodeTag::COUNT];
            for &tag in &NodeTag::ALL {
                vars[tag as usize] = next_var;
                var_to_atom.push((pos, tag));
                next_var += 1;
            }
            pos_to_vars.insert(pos, vars);
        }

        VariableMap {
            max_depth,
            positions,
            pos_to_vars,
            var_to_atom,
        }
    }

    /// Get BDD variable ID for (position, tag).
    #[inline]
    pub fn var(&self, pos: Position, tag: NodeTag) -> u32 {
        self.pos_to_vars[&pos][tag as usize]
    }

    /// Decode variable ID back to (position, tag).
    #[inline]
    pub fn decode(&self, var: u32) -> (Position, NodeTag) {
        self.var_to_atom[var as usize]
    }

    /// All positions in BFS order.
    pub fn positions(&self) -> &[Position] {
        &self.positions
    }

    /// Maximum tree depth.
    pub fn max_depth(&self) -> u32 {
        self.max_depth
    }

    /// Total number of BDD variables allocated.
    pub fn num_vars(&self) -> usize {
        self.var_to_atom.len() - 1 // exclude var 0
    }

    /// Number of positions.
    pub fn num_positions(&self) -> usize {
        self.positions.len()
    }
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_position_root() {
        let root = Position::ROOT;
        assert_eq!(root.depth(), 0);
        assert!(root.is_root());
        assert_eq!(root.to_string(), "ε");
    }

    #[test]
    fn test_position_children() {
        let root = Position::ROOT;

        let left = root.left();
        assert_eq!(left.depth(), 1);
        assert_eq!(left.to_string(), "L");

        let right = root.right();
        assert_eq!(right.depth(), 1);
        assert_eq!(right.to_string(), "R");

        let ll = left.left();
        assert_eq!(ll.depth(), 2);
        assert_eq!(ll.to_string(), "LL");

        let lr = left.right();
        assert_eq!(lr.depth(), 2);
        assert_eq!(lr.to_string(), "LR");

        let rl = right.left();
        assert_eq!(rl.depth(), 2);
        assert_eq!(rl.to_string(), "RL");

        let rr = right.right();
        assert_eq!(rr.depth(), 2);
        assert_eq!(rr.to_string(), "RR");
    }

    #[test]
    fn test_all_positions_depth_0() {
        let positions = Position::all_up_to_depth(0);
        assert_eq!(positions.len(), 1);
        assert_eq!(positions[0], Position::ROOT);
    }

    #[test]
    fn test_all_positions_depth_1() {
        let positions = Position::all_up_to_depth(1);
        assert_eq!(positions.len(), 3); // root, L, R
    }

    #[test]
    fn test_all_positions_depth_2() {
        let positions = Position::all_up_to_depth(2);
        assert_eq!(positions.len(), 7); // 1 + 2 + 4
    }

    #[test]
    fn test_all_positions_depth_3() {
        let positions = Position::all_up_to_depth(3);
        assert_eq!(positions.len(), 15); // 1 + 2 + 4 + 8
    }

    #[test]
    fn test_node_tag_properties() {
        assert!(NodeTag::VarX.is_leaf());
        assert!(NodeTag::Const0.is_leaf());
        assert!(!NodeTag::Not.is_leaf());
        assert!(!NodeTag::And.is_leaf());

        assert!(NodeTag::Not.is_unary());
        assert!(!NodeTag::And.is_unary());

        assert!(NodeTag::And.is_binary());
        assert!(NodeTag::Or.is_binary());
        assert!(NodeTag::Xor.is_binary());
        assert!(!NodeTag::Not.is_binary());

        assert!(NodeTag::And.is_commutative());
        assert!(NodeTag::Or.is_commutative());
        assert!(NodeTag::Xor.is_commutative());
        assert!(!NodeTag::Not.is_commutative());

        assert!(NodeTag::And.is_idempotent());
        assert!(NodeTag::Or.is_idempotent());
        assert!(!NodeTag::Xor.is_idempotent()); // x XOR x = 0, not x
    }

    #[test]
    fn test_variable_map_depth_0() {
        let vars = VariableMap::new(0);
        assert_eq!(vars.num_positions(), 1);
        assert_eq!(vars.num_vars(), 8); // 1 position × 8 tags
    }

    #[test]
    fn test_variable_map_depth_1() {
        let vars = VariableMap::new(1);
        assert_eq!(vars.num_positions(), 3);
        assert_eq!(vars.num_vars(), 24); // 3 positions × 8 tags
    }

    #[test]
    fn test_variable_map_roundtrip() {
        let vars = VariableMap::new(2);
        for &pos in vars.positions() {
            for &tag in &NodeTag::ALL {
                let var = vars.var(pos, tag);
                let (decoded_pos, decoded_tag) = vars.decode(var);
                assert_eq!(pos, decoded_pos);
                assert_eq!(tag, decoded_tag);
            }
        }
    }
}
