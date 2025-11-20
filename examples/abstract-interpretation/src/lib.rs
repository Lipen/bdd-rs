//! BDD-Guided Abstract Interpretation Framework
//!
//! A comprehensive implementation of abstract interpretation with multiple abstract domains
//! for static program analysis. This library demonstrates how different domains can be
//! composed and used to analyze various program properties.
//!
//! # Overview
//!
//! This framework provides:
//! - **4 Abstract Domains**: Sign, Constant Propagation, Interval, and Points-to Analysis
//! - **Lattice Theory**: Complete implementations with join, meet, widening, and narrowing
//! - **BDD Integration**: Efficient pointer analysis using Binary Decision Diagrams
//! - **Product Domains**: Compositional analysis combining multiple domains
//! - **Transfer Functions**: Abstract semantics for program statements
//! - **Fixpoint Engine**: Computes program invariants with termination guarantees
//!
//! # Available Domains
//!
//! ## 1. Sign Domain ([`SignDomain`])
//!
//! Tracks the sign of numeric variables: Negative, Zero, Positive, etc.
//!
//! **Use Cases**:
//! - Detecting division by zero
//! - Sign error detection (overflow/underflow)
//! - Array index sign validation
//!
//! ```
//! use abstract_interpretation::*;
//!
//! let domain = SignDomain;
//! let state = domain.constant(&"x".to_string(), -5);
//! assert_eq!(state.get("x"), Sign::Neg);
//!
//! // After: y = x + 10
//! let expr = NumExpr::Add(
//!     Box::new(NumExpr::Var("x".to_string())),
//!     Box::new(NumExpr::Const(10))
//! );
//! let state = domain.assign(&state, &"y".to_string(), &expr);
//! assert_eq!(state.get("y"), Sign::Top); // Neg + Pos = uncertain
//! ```
//!
//! ## 2. Constant Propagation Domain ([`ConstantDomain`])
//!
//! Tracks exact constant values when known, enabling constant folding and dead code elimination.
//!
//! **Use Cases**:
//! - Constant folding optimization
//! - Dead code detection
//! - Compile-time expression evaluation
//!
//! ```
//! use abstract_interpretation::*;
//!
//! let domain = ConstantDomain;
//! let mut state = domain.constant(&"x".to_string(), 7);
//!
//! // y = x + 3
//! let expr = NumExpr::Add(
//!     Box::new(NumExpr::Var("x".to_string())),
//!     Box::new(NumExpr::Const(3))
//! );
//! state = domain.assign(&state, &"y".to_string(), &expr);
//! assert_eq!(state.get("y"), ConstValue::Const(10)); // Exactly 10!
//!
//! // z = y * 2
//! let expr = NumExpr::Mul(
//!     Box::new(NumExpr::Var("y".to_string())),
//!     Box::new(NumExpr::Const(2))
//! );
//! state = domain.assign(&state, &"z".to_string(), &expr);
//! assert_eq!(state.get("z"), ConstValue::Const(20)); // Constant propagated
//! ```
//!
//! ## 3. Interval Domain ([`IntervalDomain`])
//!
//! Tracks numeric ranges `[low, high]` for variables, supporting arithmetic with ±∞.
//!
//! **Use Cases**:
//! - Array bounds checking
//! - Buffer overflow detection
//! - Loop bound analysis
//!
//! ```
//! use abstract_interpretation::*;
//!
//! let domain = IntervalDomain;
//!
//! // x in [0, 10]
//! let state = domain.interval(&"x".to_string(), 0, 10);
//!
//! // Check bounds
//! if let Some((low, high)) = domain.get_bounds(&state, &"x".to_string()) {
//!     assert_eq!(low, 0);
//!     assert_eq!(high, 10);
//!     println!("Array access arr[x] is safe if array size > {}", high);
//! }
//! ```
//!
//! ## 4. Points-to Analysis Domain ([`PointsToDomain`])
//!
//! BDD-based pointer analysis tracking which memory locations pointers may reference.
//!
//! **Use Cases**:
//! - Alias analysis (do two pointers point to the same location?)
//! - Memory safety verification
//! - Null pointer detection
//! - Use-after-free detection
//!
//! ```
//! use abstract_interpretation::*;
//! use std::rc::Rc;
//!
//! let domain = PointsToDomain::new();
//! let mut state = PointsToElement::new(Rc::clone(domain.bdd()));
//!
//! // p = &x; q = &y;
//! state = domain.assign_address(&state, "p", &Location::Stack("x".to_string()));
//! state = domain.assign_address(&state, "q", &Location::Stack("y".to_string()));
//!
//! // Check aliasing
//! assert!(!state.must_alias(&domain, "p", "q")); // Different targets
//!
//! // p = q;
//! state = domain.assign_copy(&state, "p", "q");
//! assert!(state.must_alias(&domain, "p", "q")); // Now they alias!
//! ```
//!
//! # Multi-Domain Analysis
//!
//! Domains can be combined for more powerful analysis:
//!
//! ```
//! use abstract_interpretation::*;
//! use std::rc::Rc;
//!
//! // Combine Sign + Interval + Points-to for comprehensive analysis
//! let sign_domain = SignDomain;
//! let interval_domain = IntervalDomain;
//! let pointsto_domain = PointsToDomain::new();
//!
//! // Array access: arr[i] where i in [0, 9]
//! let sign_state = sign_domain.interval(&"i".to_string(), 0, 9);
//! let interval_state = interval_domain.interval(&"i".to_string(), 0, 9);
//! let pointsto_state = PointsToElement::new(Rc::clone(pointsto_domain.bdd()));
//!
//! // Sign: i is non-negative (safe from negative index)
//! assert_eq!(sign_state.get("i"), Sign::NonNeg);
//!
//! // Interval: i in [0,9] (safe for array of size 10)
//! if let Some((low, high)) = interval_domain.get_bounds(&interval_state, &"i".to_string()) {
//!     assert!(low >= 0 && high < 10);
//! }
//! ```
//!
//! # Lattice Theory
//!
//! All domains implement the [`AbstractDomain`] trait, providing:
//!
//! - **Bottom** (⊥): Unreachable state / empty set
//! - **Top** (⊤): Unknown state / all possibilities
//! - **Join** (⊔): Over-approximation (union/least upper bound)
//! - **Meet** (⊓): Refinement (intersection/greatest lower bound)
//! - **Widening** (∇): Accelerates fixpoint computation
//! - **Narrowing** (∆): Refines over-approximations
//!
//! Example:
//! ```
//! use abstract_interpretation::*;
//!
//! let domain = SignDomain;
//!
//! let state1 = domain.constant(&"x".to_string(), 5);   // x = 5 → Pos
//! let state2 = domain.constant(&"x".to_string(), -3);  // x = -3 → Neg
//!
//! // Join: x could be positive OR negative
//! let joined = domain.join(&state1, &state2);
//! assert_eq!(joined.get("x"), Sign::NonZero); // Pos ⊔ Neg = NonZero
//!
//! // Meet: x must be both positive AND negative (impossible!)
//! let meet = domain.meet(&state1, &state2);
//! assert!(domain.is_bottom(&meet)); // Contradiction → ⊥
//! ```
//!
//! # Fixpoint Computation
//!
//! The [`FixpointEngine`] computes loop invariants using widening for termination:
//!
//! ```
//! use abstract_interpretation::*;
//!
//! let domain = IntervalDomain;
//! let engine = FixpointEngine {
//!     domain: domain.clone(),
//!     widening_threshold: 3,
//!     narrowing_iterations: 2,
//!     max_iterations: 100,
//! };
//!
//! // Analyze: x = 0; while (x < 10) { x = x + 1; }
//! let init = domain.constant(&"x".to_string(), 0);
//!
//! let transfer = |state: &IntervalElement| {
//!     // x < 10
//!     let guarded = domain.assume(&state, &NumPred::Lt(
//!         NumExpr::Var("x".to_string()),
//!         NumExpr::Const(10)
//!     ));
//!     // x = x + 1
//!     domain.assign(&guarded, &"x".to_string(), &NumExpr::Add(
//!         Box::new(NumExpr::Var("x".to_string())),
//!         Box::new(NumExpr::Const(1))
//!     ))
//! };
//!
//! let result = engine.lfp(init, transfer);
//! // After widening/narrowing: x in [0, 10]
//! ```
//!
//! # Examples
//!
//! The library includes comprehensive examples:
//!
//! - **`pointsto_example.rs`**: Step-by-step pointer analysis
//! - **`realistic_programs.rs`**: Real-world scenarios:
//!   - Array bounds checking
//!   - Constant propagation optimization
//!   - Pointer alias analysis
//!   - Combined multi-domain analysis
//! - **`sign_analysis.rs`**: Sign domain demonstration
//! - **`constant_propagation.rs`**: Dead code detection
//! - **`simple_loops.rs`**: Fixpoint computation
//!
//! Run examples:
//! ```bash
//! cargo run --example realistic_programs
//! cargo run --example pointsto_example
//! ```
//!
//! # Testing
//!
//! The framework includes 91+ tests covering:
//! - Individual domain operations (79 unit tests)
//! - Multi-domain integration (10 tests)
//! - Documentation examples (2 tests)
//!
//! ```bash
//! cargo test                         # All tests
//! cargo test sign::tests             # Sign domain tests
//! cargo test pointsto::tests         # Pointer analysis tests
//! cargo test --test domain_integration  # Integration tests
//! ```
//!
//! # Architecture
//!
//! The framework follows these design principles:
//!
//! 1. **Modularity**: Each domain is independent and self-contained
//! 2. **Composability**: Domains can be combined via product construction
//! 3. **Extensibility**: New domains can be added by implementing [`AbstractDomain`]
//! 4. **Soundness**: All operations over-approximate (conservative analysis)
//! 5. **Efficiency**: BDDs provide compact representation for pointer sets
//!
//! # References
//!
//! - **Abstract Interpretation**: Cousot & Cousot (1977)
//! - **Pointer Analysis**: Andersen (1994), Steensgaard (1996)
//! - **BDD-based Analysis**: Bryant (1986), Whaley & Lam (2004)
//! - **Interval Analysis**: Cousot & Cousot (1976)
//!
//! For detailed documentation, see individual module pages.

pub mod automata;
pub mod bdd_control;
pub mod congruence;
pub mod constant;
pub mod domain;
pub mod expr;
pub mod fixpoint;
pub mod generic_product;
pub mod interval;
pub mod numeric;
pub mod pointsto;
pub mod product;
pub mod sign;
pub mod string_domain;
pub mod transfer;
pub mod type_domain;

// Re-exports for convenience
pub use automata::{AutomataDomain, CharClass, Predicate, SymbolicDFA, SymbolicNFA};
pub use bdd_control::{BddControlDomain, ControlSensitiveElement, ControlSensitiveProduct, ControlState};
pub use constant::{ConstValue, ConstantDomain, ConstantElement};
pub use domain::AbstractDomain;
pub use expr::{NumExpr, NumPred, Stmt};
pub use fixpoint::FixpointEngine;
pub use interval::{Bound, Interval, IntervalDomain, IntervalElement};
pub use numeric::NumericDomain;
pub use pointsto::{Location, LocationMap, PointsToDomain, PointsToElement};
pub use product::{ProductDomain, ProductElement};
pub use sign::{Sign, SignDomain, SignElement};
pub use string_domain::{
    CharacterSet, CharacterSetDomain, StringConst, StringConstantDomain, StringInclusionDomain, StringLengthDomain, StringPrefixDomain,
    StringSuffixDomain,
};
pub use transfer::{NumericTransferFunction, TransferFunction};
pub use type_domain::{Type, TypeDomain, TypeSet};
