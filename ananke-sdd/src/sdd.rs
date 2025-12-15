//! SDD node representation.
//!
//! # Node Types
//!
//! An SDD node is one of:
//! - **Terminal**: ⊤ (true) or ⊥ (false) — two distinct nodes
//! - **Literal**: a variable or its negation — stored separately per variable
//! - **Decision**: a disjunction of (prime, sub) pairs
//!
//! # Canonical Form
//!
//! SDDs maintain canonicity through:
//! 1. **Compression**: No two elements share the same sub
//! 2. **Trimming**: Elements with sub = ⊥ are removed
//! 3. **Uniqueness**: Each semantic function has exactly one representation

use std::fmt::{self, Display};

use crate::literal::Literal;
use crate::vtree::VtreeId;

/// Unique identifier for an SDD node.
///
/// Unlike BDDs, SDD nodes do NOT use complement edges.
/// Each node has a unique ID, and negations are stored as separate nodes.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct SddId(u32);

impl SddId {
    /// The ID for the FALSE terminal.
    pub const FALSE: Self = Self(0);

    /// The ID for the TRUE terminal.
    pub const TRUE: Self = Self(1);

    /// Creates a new SddId from a raw value.
    #[inline]
    pub const fn new(id: u32) -> Self {
        Self(id)
    }

    /// Returns the raw value.
    #[inline]
    pub const fn raw(self) -> u32 {
        self.0
    }

    /// Returns the index for array access.
    #[inline]
    pub const fn index(self) -> usize {
        self.0 as usize
    }

    /// Returns true if this is the FALSE terminal.
    #[inline]
    pub const fn is_false(self) -> bool {
        self.0 == 0
    }

    /// Returns true if this is the TRUE terminal.
    #[inline]
    pub const fn is_true(self) -> bool {
        self.0 == 1
    }

    /// Returns true if this is a constant (TRUE or FALSE).
    #[inline]
    pub const fn is_constant(self) -> bool {
        self.0 <= 1
    }
}

impl Display for SddId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if *self == Self::FALSE {
            write!(f, "⊥")
        } else if *self == Self::TRUE {
            write!(f, "⊤")
        } else {
            write!(f, "n{}", self.0)
        }
    }
}

impl From<u32> for SddId {
    fn from(id: u32) -> Self {
        Self(id)
    }
}

impl From<usize> for SddId {
    fn from(id: usize) -> Self {
        Self(id as u32)
    }
}

impl Default for SddId {
    fn default() -> Self {
        Self::FALSE
    }
}

/// A prime-sub element in an SDD decision node.
///
/// Represents `(prime, sub)` where:
/// - `prime` is a function over left variables
/// - `sub` is a function over right variables
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Element {
    /// The prime (condition) — an SDD over left variables.
    pub prime: SddId,
    /// The sub (value) — an SDD over right variables.
    pub sub: SddId,
}

impl Element {
    /// Creates a new element.
    #[inline]
    pub const fn new(prime: SddId, sub: SddId) -> Self {
        Self { prime, sub }
    }
}

impl Display for Element {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "({}, {})", self.prime, self.sub)
    }
}

/// Type of an SDD node.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum SddNodeType {
    /// The FALSE terminal (⊥).
    False,
    /// The TRUE terminal (⊤).
    True,
    /// A literal (variable or its negation).
    Literal,
    /// A decision node (decomposition).
    Decision,
}

/// An SDD node.
///
/// Nodes are either:
/// - Terminals: ⊤ (true) or ⊥ (false) — distinct nodes
/// - Literals: a positive or negative literal — stored separately
/// - Decisions: a disjunction of (prime, sub) elements
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Sdd {
    /// The FALSE terminal (⊥).
    False,

    /// The TRUE terminal (⊤).
    True,

    /// A literal (variable or its negation).
    Literal(Literal),

    /// A decision node: disjunction of (prime, sub) pairs.
    ///
    /// The elements represent: (p₁ ∧ s₁) ∨ (p₂ ∧ s₂) ∨ ... ∨ (pₖ ∧ sₖ)
    ///
    /// Invariants:
    /// - Elements are compressed (no two share the same sub)
    /// - Elements are trimmed (no sub is ⊥)
    /// - Primes form a partition of ⊤ (mutually exclusive and exhaustive)
    Decision {
        /// The vtree node this decision is normalized for.
        vtree: VtreeId,
        /// The elements (prime, sub) pairs.
        elements: Vec<Element>,
    },
}

impl Sdd {
    /// Returns the type of this node.
    #[inline]
    pub fn node_type(&self) -> SddNodeType {
        match self {
            Sdd::False => SddNodeType::False,
            Sdd::True => SddNodeType::True,
            Sdd::Literal(_) => SddNodeType::Literal,
            Sdd::Decision { .. } => SddNodeType::Decision,
        }
    }

    /// Returns true if this is the FALSE terminal.
    #[inline]
    pub fn is_false(&self) -> bool {
        matches!(self, Sdd::False)
    }

    /// Returns true if this is the TRUE terminal.
    #[inline]
    pub fn is_true(&self) -> bool {
        matches!(self, Sdd::True)
    }

    /// Returns true if this is a constant (TRUE or FALSE).
    #[inline]
    pub fn is_constant(&self) -> bool {
        matches!(self, Sdd::False | Sdd::True)
    }

    /// Returns true if this is a literal.
    #[inline]
    pub fn is_literal(&self) -> bool {
        matches!(self, Sdd::Literal(_))
    }

    /// Returns true if this is a decision node.
    #[inline]
    pub fn is_decision(&self) -> bool {
        matches!(self, Sdd::Decision { .. })
    }

    /// Returns the literal if this is a literal node.
    #[inline]
    pub fn literal(&self) -> Option<Literal> {
        match self {
            Sdd::Literal(lit) => Some(*lit),
            _ => None,
        }
    }

    /// Returns the vtree node if this is a decision node.
    #[inline]
    pub fn vtree(&self) -> Option<VtreeId> {
        match self {
            Sdd::Decision { vtree, .. } => Some(*vtree),
            _ => None,
        }
    }

    /// Returns the elements if this is a decision node.
    #[inline]
    pub fn elements(&self) -> Option<&[Element]> {
        match self {
            Sdd::Decision { elements, .. } => Some(elements),
            _ => None,
        }
    }

    /// Returns the number of elements (size) of this node.
    ///
    /// Terminal and literal nodes have size 0.
    /// Decision nodes have size equal to the number of elements.
    #[inline]
    pub fn size(&self) -> usize {
        match self {
            Sdd::Decision { elements, .. } => elements.len(),
            _ => 0,
        }
    }
}

impl Display for Sdd {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Sdd::False => write!(f, "⊥"),
            Sdd::True => write!(f, "⊤"),
            Sdd::Literal(lit) => write!(f, "{}", lit),
            Sdd::Decision { vtree, elements } => {
                write!(f, "[{}]{{", vtree)?;
                for (i, elem) in elements.iter().enumerate() {
                    if i > 0 {
                        write!(f, " ∨ ")?;
                    }
                    write!(f, "{}", elem)?;
                }
                write!(f, "}}")
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_sdd_id_constants() {
        assert_eq!(SddId::FALSE.raw(), 0);
        assert_eq!(SddId::TRUE.raw(), 1);
        assert!(SddId::FALSE.is_false());
        assert!(!SddId::FALSE.is_true());
        assert!(SddId::TRUE.is_true());
        assert!(!SddId::TRUE.is_false());
        assert!(SddId::FALSE.is_constant());
        assert!(SddId::TRUE.is_constant());
        assert!(!SddId::new(2).is_constant());
    }

    #[test]
    fn test_element() {
        let elem = Element::new(SddId::TRUE, SddId::FALSE);
        assert_eq!(elem.prime, SddId::TRUE);
        assert_eq!(elem.sub, SddId::FALSE);
    }

    #[test]
    fn test_sdd_variants() {
        assert!(Sdd::False.is_false());
        assert!(Sdd::True.is_true());
        assert!(Sdd::Literal(Literal::positive(1)).is_literal());

        let decision = Sdd::Decision {
            vtree: VtreeId::new(0),
            elements: vec![Element::new(SddId::TRUE, SddId::TRUE)],
        };
        assert!(decision.is_decision());
        assert_eq!(decision.size(), 1);
    }

    #[test]
    fn test_sdd_display() {
        assert_eq!(format!("{}", Sdd::False), "⊥");
        assert_eq!(format!("{}", Sdd::True), "⊤");
        assert_eq!(format!("{}", Sdd::Literal(Literal::positive(1))), "x1");
        assert_eq!(format!("{}", Sdd::Literal(Literal::negative(2))), "¬x2");
    }

    #[test]
    fn test_node_type() {
        assert_eq!(Sdd::False.node_type(), SddNodeType::False);
        assert_eq!(Sdd::True.node_type(), SddNodeType::True);
        assert_eq!(Sdd::Literal(Literal::positive(1)).node_type(), SddNodeType::Literal);
        assert_eq!(
            Sdd::Decision {
                vtree: VtreeId::new(0),
                elements: vec![]
            }
            .node_type(),
            SddNodeType::Decision
        );
    }
}
