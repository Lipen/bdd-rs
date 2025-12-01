//! Theory solvers for constraint satisfaction.
//!
//! This module provides theory solvers that determine whether a set of
//! predicate assignments is satisfiable and generate concrete witnesses.
//!
//! # Architecture
//!
//! ```text
//! BDD Path → Predicate Assignments → Theory Solver → Witness/Unsat
//! ```
//!
//! The BDD encodes boolean combinations of predicates. Each path through
//! the BDD corresponds to an assignment of predicates to true/false.
//! Theory solvers check if such an assignment has a concrete solution.
//!
//! # Available Solvers
//!
//! | Solver               | Handles                        | Complexity |
//! |----------------------|--------------------------------|------------|
//! | [`IntervalSolver`]   | `x op constant`                | O(n)       |
//! | [`RelationalSolver`] | `x op y` (variable comparisons)| O(n²)      |
//! | [`ModularSolver`]    | `x % d == r`                   | O(n)       |
//! | [`ArrayBoundsSolver`]| Array index bounds             | O(n)       |
//! | [`BitwiseSolver`]    | Bit-level properties           | O(n)       |
//! | [`CombinedSolver`]   | Chains multiple solvers        | Σ costs    |
//!
//! # Example
//!
//! ```rust
//! use std::collections::HashMap;
//! use bdd_rs::bdd::Bdd;
//! use tbdd_pbt::predicate::{Predicate, PredicateUniverse};
//! use tbdd_pbt::theory::{ConstraintSolver, IntervalSolver, SolveResult};
//!
//! let bdd = Bdd::default();
//! let mut universe = PredicateUniverse::new();
//!
//! // Register predicates
//! let v1 = universe.register(Predicate::ge("x", 0), &bdd);
//! let v2 = universe.register(Predicate::lt("x", 100), &bdd);
//!
//! // Solve
//! let solver = IntervalSolver::new();
//! let mut assignments = HashMap::new();
//! assignments.insert(v1, true);
//! assignments.insert(v2, true);
//!
//! match solver.solve(&assignments, &universe) {
//!     SolveResult::Sat(witness) => {
//!         let x = witness.get("x").unwrap();
//!         assert!(x >= 0 && x < 100);
//!     }
//!     _ => panic!("Expected Sat"),
//! }
//! ```

mod array;
mod bitwise;
mod boundary;
mod combined;
mod core;
mod interval;
mod modular;
mod relational;

// Re-export core types
// Re-export solvers
pub use array::{ArrayBoundsSolver, ArrayConstraint, ArrayLength};
pub use bitwise::{BitwiseConstraint, BitwiseSolver};
pub use boundary::BoundaryValueGenerator;
pub use combined::{CombinedSolver, IntervalRelationalSolver};
// Re-export internal Interval for boundary module (pub(crate) won't work across modules)
pub use interval::Interval;
pub use interval::IntervalSolver;
pub use modular::{ModularConstraint, ModularSolver};
pub use relational::RelationalSolver;

pub use self::core::{ConstraintSolver, SolveResult, Witness};
