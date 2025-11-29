//! # T-BDD: Theory-Aware BDD-Guided Property-Based Testing
//!
//! This crate implements a novel approach to property-based testing that combines:
//!
//! 1. **BDD Path Exploration**: Use BDDs to symbolically represent program paths
//! 2. **Theory Integration**: Use theory solvers to prune infeasible paths
//! 3. **Guided Generation**: Generate tests that maximize coverage
//!
//! ## Core Concepts
//!
//! - **Predicate**: A boolean condition in the program (e.g., `x < 10`)
//! - **Path**: A sequence of predicate valuations leading to a program point
//! - **Path Constraint**: BDD encoding of reachable paths
//! - **Theory Solver**: Checks feasibility and generates witnesses
//!
//! ## Architecture
//!
//! ```text
//! ┌─────────────────────────────────────────────────────────────────┐
//! │                        T-BDD Framework                          │
//! ├─────────────────────────────────────────────────────────────────┤
//! │                                                                 │
//! │  ┌─────────────┐    ┌─────────────┐    ┌─────────────────────┐  │
//! │  │   Program   │───▶│ Predicate   │───▶│   BDD Path Space    │  │
//! │  │ Predicates  │    │  Universe   │    │  (boolean combos)   │  │
//! │  └─────────────┘    └─────────────┘    └──────────┬──────────┘  │
//! │                                                   │             │
//! │                                                   ▼             │
//! │                     ┌─────────────────────────────────────────┐ │
//! │                     │         Path Explorer                   │ │
//! │                     │  • Enumerate BDD satisfying paths       │ │
//! │                     │  • Query theory checker for pruning     │ │
//! │                     │  • Track coverage via BDD operations    │ │
//! │                     └──────────┬──────────────────────────────┘ │
//! │                                │                                │
//! │              ┌─────────────────┴─────────────────┐              │
//! │              ▼                                   ▼              │
//! │  ┌─────────────────────┐           ┌─────────────────────────┐  │
//! │  │   Theory Checker    │           │    Test Generator       │  │
//! │  │  (Interval Domain)  │           │  (concrete witnesses)   │  │
//! │  └─────────────────────┘           └─────────────────────────┘  │
//! │                                                                 │
//! └─────────────────────────────────────────────────────────────────┘
//! ```
//!
//! ## Modules
//!
//! - [`predicate`]: Predicate abstraction and universe
//! - [`theory`]: Theory solver integration (interval, relational, modular)
//! - [`generator`]: Test input generation from BDD paths
//! - [`coverage`]: Coverage tracking using BDD operations
//! - [`property`]: Property-based testing API with counterexample search

pub mod coverage;
pub mod generator;
pub mod predicate;
pub mod property;
pub mod theory;

// Re-exports
pub use coverage::{CoverageSummary, CoverageTracker};
pub use generator::{
    ExecutionResult, GeneratorConfig, PathPriority, PrioritizedGenerator, PrioritizedPath, SymbolicExecutor, SymbolicState, TestCase,
    TestGenerator,
};
pub use predicate::{CompareOp, Operand, Predicate, PredicateUniverse, ProgramVar};
pub use property::{CheckResult, CheckerConfig, Property, PropertyChecker};
pub use theory::{
    ArrayBoundsSolver, ArrayConstraint, ArrayLength, BitwiseConstraint, BitwiseSolver, BoundaryValueGenerator, CombinedSolver,
    ConstraintSolver, Interval, IntervalRelationalSolver, IntervalSolver, ModularSolver, RelationalSolver, SolveResult, Witness,
};
