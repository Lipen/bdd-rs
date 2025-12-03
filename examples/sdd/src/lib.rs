//! # Sentential Decision Diagrams (SDDs)
//!
//! This crate provides a complete implementation of **Sentential Decision Diagrams**,
//! a tractable representation for propositional knowledge bases.
//!
//! ## What is an SDD?
//!
//! An SDD is a canonical representation of Boolean functions based on **vtree decomposition**.
//! Unlike BDDs which use a fixed linear variable ordering, SDDs use a binary tree structure
//! (the vtree) to recursively decompose functions, providing:
//!
//! - **Canonicity**: For a fixed vtree, each Boolean function has exactly one SDD
//! - **Tractability**: Supports polytime conjunction, disjunction, negation, and conditioning
//! - **Succinctness**: Can be exponentially more compact than BDDs for some functions
//! - **Flexibility**: Vtree structure can be optimized for specific functions
//!
//! ## Key Concepts
//!
//! ### Vtree (Variable Tree)
//!
//! A vtree is a full binary tree whose leaves are the Boolean variables.
//! Each internal node partitions variables into left and right subtrees.
//! The vtree structure determines the SDD's decomposition.
//!
//! ```text
//!        (root)
//!        /    \
//!       /      \
//!     (L)      (R)
//!     / \      / \
//!    x₁  x₂  x₃  x₄
//! ```
//!
//! ### SDD Structure
//!
//! An SDD node is either:
//! - A **terminal**: ⊤ (true) or ⊥ (false)
//! - A **literal**: a variable or its negation
//! - A **decision node**: a disjunction of (prime, sub) pairs
//!
//! A decision node at vtree node `v` is written as:
//!
//! ```text
//! (p₁, s₁) ∨ (p₂, s₂) ∨ ... ∨ (pₖ, sₖ)
//! ```
//!
//! where each `pᵢ` (prime) is an SDD over left variables and
//! each `sᵢ` (sub) is an SDD over right variables.
//!
//! ### Compression and Canonicity
//!
//! SDDs maintain canonicity through:
//! 1. **Compression**: No two elements have the same sub
//! 2. **Trimming**: Remove elements where sub = ⊥
//! 3. **Normalization**: Elements are sorted by prime
//!
//! ## Quick Start
//!
//! ```rust
//! use sdd::manager::SddManager;
//!
//! // Create an SDD manager with 4 variables
//! let mgr = SddManager::new(4);
//!
//! // Create variables (1-indexed)
//! let x1 = mgr.var(1);
//! let x2 = mgr.var(2);
//!
//! // Build formulas
//! let f = mgr.and(x1, x2);          // x₁ ∧ x₂
//! let g = mgr.or(x1, mgr.negate(x2)); // x₁ ∨ ¬x₂
//!
//! // Check properties
//! assert!(!mgr.is_false(f));
//! assert!(!mgr.is_true(f));
//!
//! // Count satisfying assignments
//! let count = mgr.model_count(f);
//! assert_eq!(count, 4u32.into()); // x₁=1, x₂=1, x₃=any, x₄=any → 4 models
//! ```
//!
//! ## Module Overview
//!
//! - [`vtree`] — Variable tree (vtree) data structure
//! - [`sdd`] — SDD node representation
//! - [`manager`] — SDD manager with core algorithms
//! - [`literal`] — Boolean literal type
//! - [`dot`] — Graphviz visualization
//! - [`io`] — File I/O in libsdd format
//!
//! ## References
//!
//! - Darwiche, A. (2011). SDD: A New Canonical Representation of Propositional Knowledge Bases.
//!   In IJCAI-11, pp. 819-826.
//! - Darwiche, A. & Marquis, P. (2002). A Knowledge Compilation Map. JAIR, 17, 229-264.
//! - Choi, A. & Darwiche, A. (2013). Dynamic Minimization of Sentential Decision Diagrams.
//!   In AAAI-13, pp. 187-194.

pub mod dot;
pub mod io;
pub mod literal;
pub mod manager;
pub mod sdd;
pub mod vtree;

// Re-export main types for convenience
pub use io::IoError;
pub use literal::Literal;
pub use manager::SddManager;
pub use sdd::{Element, Sdd, SddId};
pub use vtree::{Vtree, VtreeId};
