//! SDD-based Abstract Interpretation for Program Analysis
//!
//! This crate demonstrates how Sentential Decision Diagrams (SDDs) can be used
//! as a formal representation of abstract states in program analysis.
//!
//! # Key Ideas
//!
//! 1. **Abstract State Representation**: An abstract state (set of possible bit configurations)
//!    is represented as an SDD Boolean function.
//!
//! 2. **Small Integer Domain**: Variables have domains 0-7, encoded as 3-bit integers,
//!    allowing efficient SDD representation.
//!
//! 3. **Operations**:
//!    - `assign(x := e)` - Transform SDD by variable assignment
//!    - `assume(pred)` - Intersect SDD with predicate representation
//!    - `join(s1, s2)` - Merge abstract states via disjunction
//!    - `widen()` - Generalize states for convergence
//!
//! 4. **VTree Strategies**: Compare different variable decompositions:
//!    - Balanced: Symmetric, general-purpose
//!    - Right-linear: Variable order matters
//!    - Left-linear: Opposite ordering
//!    - Syntactic: Based on program structure
//!    - Semantic: Based on predicate dependencies
//!
//! # Example
//!
//! ```ignore
//! use sdd_abstract_interpretation::*;
//!
//! // Create a simple program
//! let prog = vec![
//!     Stmt::Assign(Var::new(1), Expr::Const(0)),
//!     Stmt::Assign(Var::new(2), Expr::Const(0)),
//! ];
//!
//! // Analyze with SDD
//! let analyzer = SddAbstractInterpreter::new(&prog, VtreeStrategy::Balanced);
//! let result = analyzer.analyze();
//! println!("Initial state size: {}", result.initial_state_size);
//! ```

pub mod analysis;
pub mod bit_encoding;
pub mod cfg;
pub mod domains;
pub mod interpreter;
pub mod language;
pub mod sdd_domain;
pub mod vtree_strategy;

pub use analysis::{AnalysisResult, Analyzer};
pub use bit_encoding::{BitEncoding, BitVector};
pub use cfg::{CfgBuilder, CfgEdgeLabel, CfgNode};
pub use domains::{BitsetDomain, IntervalDomain};
pub use interpreter::SddAbstractInterpreter;
pub use language::{program_vars, Expr, Predicate, Program, Stmt, Var};
pub use sdd_domain::SddAbstractState;
pub use vtree_strategy::VtreeStrategy;
