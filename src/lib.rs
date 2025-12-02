//! # bdd-rs: Binary Decision Diagrams in Rust
//!
//! A high-performance library for **Binary Decision Diagrams (BDDs)** with complement edges.
//!
//! ## What is a BDD?
//!
//! A BDD is a canonical data structure representing boolean functions as directed acyclic graphs.
//! For a fixed variable ordering, every boolean function has exactly one unique representation,
//! making BDDs ideal for equivalence checking, satisfiability, and validity testing.
//!
//! ## Key Features
//!
//! - **Manager-Centric**: All operations go through the [`Bdd`] manager ensuring structural sharing
//! - **Complement Edges**: Negation is O(1) — just flip a bit, no new nodes created
//! - **Operation Caching**: Redundant computations are automatically avoided
//! - **Rich API**: Boolean ops, quantification (∃, ∀), substitution, and dynamic reordering
//!
//! ## Quick Start
//!
//! ```rust
//! use bdd_rs::bdd::Bdd;
//!
//! let bdd = Bdd::default();
//!
//! // Create variables (1-indexed)
//! let x = bdd.mk_var(1);
//! let y = bdd.mk_var(2);
//!
//! // Build formulas
//! let f = bdd.apply_and(x, -y);  // x ∧ ¬y
//!
//! // Check properties
//! assert!(!bdd.is_zero(f));  // satisfiable
//! assert!(!bdd.is_one(f));   // not a tautology
//! ```
//!
//! ## Modules
//!
//! - [`mod@bdd`] — The BDD manager and core algorithms
//! - [`mod@reference`] — The [`Ref`] type: a 32-bit handle to BDD nodes
//! - [`mod@dot`] — Graphviz visualization
//! - [`mod@sat`] — SAT solving and model counting
//! - [`mod@reorder`] — Dynamic variable reordering
//!
//! [`Bdd`]: crate::bdd::Bdd
//! [`Ref`]: crate::reference::Ref

pub mod bdd;
pub mod bitset;
pub mod cache;
pub mod debug;
pub mod dot;
pub mod eval;
pub mod node;
pub mod paths;
pub mod raw;
pub mod reference;
pub mod reorder;
pub mod sat;
pub mod subtable;
pub mod types;
pub mod utils;
