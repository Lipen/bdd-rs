//! BDD-Guided Abstract Interpretation Framework
//!
//! This library implements abstract interpretation with BDD-based control state
//! representation combined with numeric abstract domains.
//!
//! # Core Concepts
//!
//! - **Abstract Domain**: Lattice structure for representing sets of program states
//! - **Product Domain**: Combines BDD (control) × Numeric (data) domains
//! - **Transfer Functions**: Abstract semantics for program statements
//! - **Fixpoint Engine**: Computes invariants with widening/narrowing
//!
//! # Example
//!
//! ```rust,no_run
//! use abstract_interpretation::*;
//! use std::rc::Rc;
//! use bdd_rs::bdd::Bdd;
//!
//! // Create BDD manager and interval domain
//! let bdd = Rc::new(Bdd::default());
//! let interval = IntervalDomain;
//!
//! // Analyze a simple loop
//! // let x = 0;
//! // while x < 10 { x = x + 1; }
//! ```

pub mod constant;
pub mod domain;
pub mod expr;
pub mod fixpoint;
pub mod interval;
pub mod numeric;
pub mod pointsto;
pub mod product;
pub mod sign;
pub mod transfer;

// Re-exports for convenience
pub use constant::{ConstValue, ConstantDomain, ConstantElement};
pub use domain::AbstractDomain;
pub use expr::{NumExpr, NumPred, Stmt};
pub use fixpoint::FixpointEngine;
pub use interval::{Bound, Interval, IntervalDomain, IntervalElement};
pub use numeric::NumericDomain;
pub use pointsto::{Location, LocationMap, PointsToDomain, PointsToElement};
pub use product::{ProductDomain, ProductElement};
pub use sign::{Sign, SignDomain, SignElement};
pub use transfer::{NumericTransferFunction, TransferFunction};
