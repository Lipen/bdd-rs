//! # Symbolic Expression Space Exploration
//!
//! This library provides tools for symbolically representing and manipulating
//! the entire space of Boolean expression trees using BDDs.
//!
//! ## Key Idea
//!
//! Instead of enumerating expressions one-by-one, we encode all possible ASTs
//! as a single BDD and perform bulk operations:
//!
//! - **Filtering**: Remove redundant forms (commutativity, idempotence)
//! - **Partitioning**: Group trees by semantic equivalence (truth table)
//! - **Canonicalization**: Extract minimal representatives per function
//!
//! ## Modules
//!
//! - [`encoding`] — Position, NodeTag, and variable allocation
//! - [`builder`] — Expression space BDD construction
//! - [`filters`] — Symbolic constraint filters
//! - [`eval`] — Semantic evaluation and truth table extraction
//! - [`ast`] — AST reconstruction from BDD paths
//!
//! ## Example
//!
//! ```rust
//! use expr_space::{encoding::VariableMap, builder::ExpressionSpaceBuilder};
//! use ananke_bdd::bdd::Bdd;
//!
//! let bdd = Bdd::default();
//! let vars = VariableMap::new(2); // depth 2
//! let mut builder = ExpressionSpaceBuilder::new(&bdd, &vars, 2);
//! let space = builder.build();
//!
//! println!("Expression space has {} BDD nodes", bdd.size(space));
//! ```

pub mod ast;
pub mod builder;
pub mod encoding;
pub mod eval;
pub mod filters;

pub use ast::Expr;
pub use builder::ExpressionSpaceBuilder;
pub use encoding::{NodeTag, Position, VariableMap};
