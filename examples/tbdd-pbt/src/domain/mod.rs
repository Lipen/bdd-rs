//! Abstract domains for value abstraction.
//!
//! This module provides abstract domains for approximating program values
//! during analysis. Each domain trades precision for efficiency differently.
//!
//! # Available Domains
//!
//! | Domain       | Precision | Cost   | Use Case                    |
//! |--------------|-----------|--------|-----------------------------|
//! | [`Interval`] | Medium    | O(1)   | Bounds checking, overflow   |
//! | [`Sign`]     | Low       | O(1)   | Division by zero, signs     |
//! | [`Parity`]   | Low       | O(1)   | Even/odd, off-by-one errors |
//! | [`Congruence`] | Medium  | O(1)   | Alignment, modular arith    |
//! | [`ReducedProduct`] | High | O(1)  | Combining domains           |
//!
//! # Core Traits
//!
//! - [`AbstractDomain`]: Lattice operations (join, meet, widen, narrow)
//! - [`PredicateTransfer`]: Refine domains from predicate constraints
//! - [`Concretizable`]: Generate concrete values from abstract states
//! - [`Reducible`]: Cross-domain constraint propagation
//!
//! # Example
//!
//! ```rust
//! use tbdd_pbt::domain::{AbstractDomain, PredicateTransfer, Interval, Bound};
//! use tbdd_pbt::predicate::CompareOp;
//!
//! // Start with top (all values)
//! let interval = Interval::top();
//!
//! // Apply constraint: x >= 0
//! let non_negative = interval.transfer(CompareOp::Ge, 0, true);
//! assert_eq!(non_negative.low(), Bound::Finite(0));
//!
//! // Apply constraint: x < 100
//! let bounded = non_negative.transfer(CompareOp::Lt, 100, true);
//! assert_eq!(bounded.high(), Bound::Finite(99));
//!
//! // Values in [0, 99]
//! assert!(bounded.contains(50));
//! assert!(!bounded.contains(100));
//! ```

mod bound;
mod congruence;
mod interval;
mod parity;
mod product;
mod sign;
mod state;
mod traits;

// Re-exports
pub use bound::Bound;
pub use congruence::Congruence;
pub use interval::Interval;
pub use parity::Parity;
pub use product::ReducedProduct;
pub use product::Reducible;
pub use sign::Sign;
pub use state::DomainState;
pub use traits::{AbstractDomain, Concretizable, PredicateTransfer};
