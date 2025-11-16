//! Symbolic model checking using BDDs.
//!
//! This library provides infrastructure for BDD-based symbolic model checking,
//! including transition systems, CTL/LTL temporal logic, and counterexample generation.
//!
//! # Overview
//!
//! The library implements classic symbolic model checking algorithms from
//! "Symbolic Model Checking: 10^20 States and Beyond" (Burch et al., 1990).
//!
//! ## Key Components
//!
//! - **Transition Systems**: Symbolic representation of Kripke structures
//! - **CTL Model Checking**: Computation Tree Logic verification
//! - **Counterexamples**: Witness traces and looping counterexamples
//! - **Algorithms**: Reachability, fixpoint computation, image/preimage
//!
//! # Example
//!
//! ```
//! use model_checking::*;
//! use bdd_rs::bdd::Bdd;
//!
//! // Create a simple toggle system
//! let bdd = Bdd::default();
//! let mut ts = TransitionSystem::new(bdd);
//!
//! let x = Var::new("x");
//! ts.declare_var(x.clone());
//!
//! // Set initial state and transition relation
//! // ... (setup code)
//!
//! // Check a CTL property
//! let checker = CtlChecker::new(&ts);
//! let property = CtlFormula::atom("safe").ag(); // AG safe
//! let holds = checker.holds_initially(&property);
//! ```

pub mod ctl;
pub mod transition;

// Re-export key types
pub use ctl::{CtlChecker, CtlFormula};
pub use transition::{TransitionSystem, Var, VarManager};
