//! Symbolic model checking using BDDs.
//!
//! This library provides infrastructure for BDD-based symbolic model checking,
//! including transition systems, CTL/LTL temporal logic, fairness constraints,
//! and counterexample generation.
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
//! - **LTL Model Checking**: Linear Temporal Logic via automata-theoretic approach
//! - **Fairness**: Strong and weak fairness constraints
//! - **Counterexamples**: Witness traces and looping counterexamples
//! - **Algorithms**: Reachability, fixpoint computation, image/preimage
//!
//! # Example
//!
//! ```
//! use model_checking::*;
//! use ananke_bdd::bdd::Bdd;
//! use std::rc::Rc;
//!
//! // Create a simple toggle system
//! let bdd = Rc::new(Bdd::default());
//! let mut ts = TransitionSystem::new(bdd.clone());
//!
//! let x = Var::new("x");
//! ts.declare_var(x.clone());
//!
//! // Initial state: x = false
//! let x_pres = ts.var_manager().get_present(&x).unwrap();
//! let initial = ts.bdd().apply_not(ts.bdd().mk_var(x_pres));
//! ts.set_initial(initial);
//!
//! // Transition: x' = !x (toggle)
//! let x_next = ts.var_manager().get_next(&x).unwrap();
//! let x_pres_bdd = ts.bdd().mk_var(x_pres);
//! let x_next_bdd = ts.bdd().mk_var(x_next);
//! let transition = ts.bdd().apply_xor(x_pres_bdd, x_next_bdd);
//! ts.set_transition(transition);
//!
//! // Add labels
//! ts.add_label("safe".to_string(), ts.bdd().one());
//!
//! // Check a CTL property
//! let ts = Rc::new(ts);
//! let checker = CtlChecker::new(ts.clone());
//! let property = CtlFormula::atom("safe").ag(); // AG safe
//! let holds = checker.holds_initially(&property);
//! assert!(holds);
//! ```

pub mod counterexample;
pub mod ctl;
pub mod fairness;
pub mod ltl;
pub mod transition;

// Re-export key types
pub use counterexample::{
    Counterexample, CounterexampleGenerator, ExplanationBuilder, ExplanationStep, PropertyExplanation, State, TraceVisualization,
};
pub use ctl::{CtlChecker, CtlFormula};
pub use fairness::{FairnessConstraint, FairnessManager};
pub use ltl::{LtlChecker, LtlFormula};
pub use transition::{TransitionSystem, Var, VarManager};
