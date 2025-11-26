//! # bdd-rs: Binary Decision Diagrams in Rust
//!
//! **`bdd-rs`** is a high-performance, safe, and manager-centric library for working with **Binary Decision Diagrams (BDDs)**.
//! It is designed for formal verification, static analysis, and combinatorial optimization.
//!
//! ## What is a BDD?
//!
//! A Binary Decision Diagram is a data structure that represents a boolean function as a directed acyclic graph.
//! It is **canonical** --- meaning that for a fixed variable ordering, every boolean function has exactly one unique representation.
//! This property makes BDDs incredibly powerful for checking equivalence, satisfiability, and validity.
//!
//! ## Key Features
//!
//! - **Manager-Centric Architecture**: All operations go through the [`Bdd`][crate::bdd::Bdd] manager. This ensures structural sharing (hash consing) and maintains the canonical form invariant.
//! - **Safe & Efficient**: We use lightweight [`Ref`][crate::reference::Ref] handles to reference nodes. This prevents invalid access while keeping memory overhead minimal.
//! - **Performance First**: Built-in operation caching (computed table) ensures that redundant computations are avoided.
//! - **1-Based Indexing**: Variables are 1-indexed (reserving 0 for internal use), simplifying integration with standard formats like DIMACS.
//! - **Rich API**: Full support for boolean operators (AND, OR, XOR, ITE), quantification (∃, ∀), and variable substitution.
//!
//! ## Quick Start
//!
//! Add `bdd-rs` to your `Cargo.toml` and start building boolean functions:
//!
//! ```toml
//! [dependencies]
//! bdd-rs = "0.1"
//! ```
//!
//! ## Basic Usage
//!
//! ```rust
//! use bdd_rs::bdd::Bdd;
//!
//! // 1. Initialize the manager
//! let bdd = Bdd::default();
//!
//! // 2. Create variables (1-indexed)
//! let x1 = bdd.mk_var(1);
//! let x2 = bdd.mk_var(2);
//!
//! // 3. Build a formula: f = x1 AND (NOT x2)
//! // Note: We use the manager to perform operations!
//! let not_x2 = bdd.apply_not(x2);
//! let f = bdd.apply_and(x1, not_x2);
//!
//! // 4. Check properties
//! assert!(!bdd.is_zero(f)); // It is satisfiable
//! assert!(!bdd.is_one(f));  // It is not a tautology
//!
//! // 5. Evaluate (x1=true, x2=false) -> should be true
//! let res = bdd.cofactor_cube(f, [1, -2]);
//! assert!(bdd.is_one(res));
//! ```
//!
//! ## Core Components
//!
//! - **[`bdd`]**: The heart of the library. Contains the [`Bdd`][crate::bdd::Bdd] manager and core algorithms.
//! - **[`dot`]**: Utilities for visualizing BDDs using Graphviz.
//! - **[`sat`]**: Satisfiability solving and model counting.
//!
//! For a deep dive into the implementation details, check the [`bdd`] module documentation.

pub mod bdd;
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
pub mod storage;
pub mod subtable;
pub mod table;
pub mod types;
pub mod utils;
