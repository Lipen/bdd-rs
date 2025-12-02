//! # Boolean Function Landscape
//!
//! A library for exploring the space of Boolean functions via BDD size distribution.
//!
//! ## Motivation
//!
//! For `n` variables, there are `2^(2^n)` distinct Boolean functions — a double-exponential
//! growth that makes exhaustive enumeration infeasible beyond very small `n`.
//!
//! This library provides tools for:
//! - **Random sampling** of Boolean functions
//! - **BDD construction** and size measurement
//! - **Statistical analysis** with confidence intervals
//! - **Distribution characterization** using various methods
//!
//! ## Core Concepts
//!
//! ### Boolean Functions
//!
//! A Boolean function `f: {0,1}^n → {0,1}` is uniquely determined by its truth table,
//! a `2^n`-bit vector. We represent this as a `BigUint` for arbitrary precision.
//!
//! ### BDD Size
//!
//! The BDD size of a function is the number of nodes in its reduced ordered BDD
//! for a fixed variable ordering. This is a key complexity measure.
//!
//! ### Statistical Methods
//!
//! Since exhaustive enumeration is infeasible, we use Monte Carlo sampling with:
//! - **Chernoff bounds** for tail probability estimates
//! - **Chebyshev inequality** for variance-based bounds
//! - **Central Limit Theorem** for approximate confidence intervals
//! - **Bootstrap resampling** for distribution-free inference
//!
//! ## Architecture
//!
//! ```text
//! ┌─────────────────────────────────────────────────────────────────────┐
//! │                 Boolean Function Landscape Explorer                 │
//! ├─────────────────────────────────────────────────────────────────────┤
//! │                                                                     │
//! │  ┌──────────────┐    ┌──────────────┐    ┌────────────────────────┐ │
//! │  │   Function   │───▶│    BDD       │───▶│    Size Vector         │ │
//! │  │   Generator  │    │  Constructor │    │   [s₁, s₂, ..., sₖ]    │ │
//! │  └──────────────┘    └──────────────┘    └───────────┬────────────┘ │
//! │                                                      │              │
//! │                                                      ▼              │
//! │  ┌────────────────────────────────────────────────────────────────┐ │
//! │  │                    Statistical Analysis                        │ │
//! │  │  • Mean, Variance, Standard Deviation                          │ │
//! │  │  • Confidence Intervals (CLT, Bootstrap)                       │ │
//! │  │  • Tail Bounds (Chernoff, Chebyshev)                           │ │
//! │  │  • Distribution Visualization                                  │ │
//! │  └────────────────────────────────────────────────────────────────┘ │
//! │                                                                     │
//! └─────────────────────────────────────────────────────────────────────┘
//! ```
//!
//! ## Modules
//!
//! - [`mod@function`]: Boolean function representation and random generation
//! - [`mod@stats`]: Statistical analysis tools
//! - [`mod@sampling`]: Monte Carlo sampling strategies
//! - [`mod@analysis`]: BDD size distribution analysis
//! - [`mod@viz`]: Visualization utilities

pub mod analysis;
pub mod function;
pub mod sampling;
pub mod stats;
pub mod viz;

// Re-exports
pub use analysis::{SizeDistribution, SizeHistogram};
pub use function::{BooleanFunction, TruthTable};
pub use sampling::{MonteCarloSampler, SamplingConfig, SamplingResult};
pub use stats::{BootstrapResult, ConfidenceInterval, Statistics, TailBound};
