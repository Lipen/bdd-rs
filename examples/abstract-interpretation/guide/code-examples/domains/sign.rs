//! Sign Domain Implementation
//!
//! **Guide Reference:** Part I, Chapter 1 - "Abstract Domains and Lattice Theory"
//!
//! This example demonstrates the fundamental concepts of abstract interpretation:
//!
//! - **Abstract Domain**: Representing sets of concrete values with abstract elements
//! - **Lattice Operations**: Join (⊔) for merging paths, Meet (⊓) for refining
//! - **Abstract Transformers**: Operations that soundly overapproximate concrete semantics
//! - **Precision Trade-offs**: How abstraction loses information but enables analysis
//!
//! The sign domain abstracts integers into five values: {⊥, -, 0, +, ⊤}.
//! This is one of the simplest non-trivial abstract domains, making it perfect
//! for understanding core abstract interpretation concepts.
//!
//! ## Key Concepts Demonstrated
//!
//! 1. **Lattice Structure**: The sign values form a complete lattice with ⊥ at bottom
//!    and ⊤ at top, allowing systematic reasoning about information flow.
//!
//! 2. **Soundness**: Every abstract operation overapproximates concrete behavior.
//!    For example, `+ + - = ⊤` because the concrete result could be any sign.
//!
//! 3. **Path Merging**: When control flow joins (if-then-else), we use join (⊔)
//!    to combine information from both branches.
//!
//! ## Expected Output
//!
//! Run with: `cargo run --example sign_domain`
//!
//! The output demonstrates lattice operations, abstract arithmetic, and how
//! abstraction affects precision when analyzing simple programs.

use std::fmt;

/// Sign domain elements representing the abstract sign of an integer value.
///
/// The lattice structure:
/// ```text
///        ⊤ (Top/Unknown)
///       /  |  \
///    Neg Zero Pos
///       \  |  /
///        ⊥ (Bot/Unreachable)
/// ```
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Sign {
    /// Bottom: unreachable/empty set of values
    Bot,
    /// Negative values: {..., -2, -1}
    Neg,
    /// Zero: {0}
    Zero,
    /// Positive values: {1, 2, ...}
    Pos,
    /// Top: all values (unknown)
    Top,
}

impl Sign {
    /// Join operation: least upper bound in the lattice
    ///
    /// Combines information from two program paths.
    /// Returns the least precise element that contains both inputs.
    pub fn join(&self, other: &Self) -> Self {
        use Sign::*;
        match (self, other) {
            (Bot, x) | (x, Bot) => *x,
            (x, y) if x == y => *x,
            _ => Top,
        }
    }

    /// Meet operation: greatest lower bound in the lattice
    ///
    /// Refines information by combining constraints.
    /// Returns the most precise element contained in both inputs.
    pub fn meet(&self, other: &Self) -> Self {
        use Sign::*;
        match (self, other) {
            (Top, x) | (x, Top) => *x,
            (x, y) if x == y => *x,
            _ => Bot,
        }
    }

    /// Abstract addition: x + y
    pub fn add(&self, other: &Self) -> Self {
        use Sign::*;
        match (self, other) {
            (Bot, _) | (_, Bot) => Bot,
            (Top, _) | (_, Top) => Top,
            (Zero, x) | (x, Zero) => *x,
            (Pos, Pos) => Pos,
            (Neg, Neg) => Neg,
            (Pos, Neg) | (Neg, Pos) => Top, // Could be any sign
        }
    }

    /// Abstract subtraction: x - y
    pub fn sub(&self, other: &Self) -> Self {
        self.add(&other.neg())
    }

    /// Abstract negation: -x
    pub fn neg(&self) -> Self {
        use Sign::*;
        match self {
            Bot => Bot,
            Neg => Pos,
            Zero => Zero,
            Pos => Neg,
            Top => Top,
        }
    }

    /// Abstract multiplication: x * y
    pub fn mul(&self, other: &Self) -> Self {
        use Sign::*;
        match (self, other) {
            (Bot, _) | (_, Bot) => Bot,
            (Top, _) | (_, Top) => Top,
            (Zero, _) | (_, Zero) => Zero,
            (Pos, Pos) | (Neg, Neg) => Pos,
            (Pos, Neg) | (Neg, Pos) => Neg,
        }
    }

    /// Check if this element is less than or equal to another in the lattice order
    pub fn leq(&self, other: &Self) -> bool {
        use Sign::*;
        match (self, other) {
            (Bot, _) => true,
            (_, Top) => true,
            (x, y) if x == y => true,
            _ => false,
        }
    }
}

impl fmt::Display for Sign {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Sign::Bot => write!(f, "⊥"),
            Sign::Neg => write!(f, "Neg"),
            Sign::Zero => write!(f, "Zero"),
            Sign::Pos => write!(f, "Pos"),
            Sign::Top => write!(f, "⊤"),
        }
    }
}

fn main() {
    use Sign::*;

    println!("=== Sign Domain Example ===\n");

    // Basic operations
    println!("Join operations:");
    println!("  Pos ⊔ Neg = {}", Pos.join(&Neg));
    println!("  Pos ⊔ Pos = {}", Pos.join(&Pos));
    println!("  Pos ⊔ Bot = {}", Pos.join(&Bot));
    println!();

    // Arithmetic
    println!("Abstract arithmetic:");
    println!("  Pos + Pos = {}", Pos.add(&Pos));
    println!("  Pos + Neg = {}", Pos.add(&Neg));
    println!("  Neg + Neg = {}", Neg.add(&Neg));
    println!("  Pos * Neg = {}", Pos.mul(&Neg));
    println!();

    // Analyzing a simple program
    println!("Analyzing: let mut x = 5; x = x + 1;");
    let mut x = Pos; // x = 5 (positive)
    println!("  After x = 5: x = {}", x);
    x = x.add(&Pos); // x = x + 1 (positive + positive = positive)
    println!("  After x = x + 1: x = {}", x);
    println!();

    // Path merging
    println!("Analyzing branching:");
    println!("  if condition {{ x = 5 }} else {{ x = -3 }}");
    let x_then = Pos; // x = 5
    let x_else = Neg; // x = -3
    let x_after = x_then.join(&x_else);
    println!("  After merge: x = {} (lost precision)", x_after);
    println!();

    // Lattice properties
    println!("Lattice properties:");
    println!("  Bot ≤ Pos: {}", Bot.leq(&Pos));
    println!("  Pos ≤ Top: {}", Pos.leq(&Top));
    println!("  Pos ≤ Neg: {}", Pos.leq(&Neg));
}
