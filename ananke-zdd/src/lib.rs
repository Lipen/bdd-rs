//! # ananke-zdd: Zero-Suppressed Decision Diagrams in Rust
//!
//! A library for **Zero-Suppressed Decision Diagrams (ZDDs)**, optimized for
//! representing families of sets (combinatorial sets).
//!
//! ## What is a ZDD?
//!
//! A ZDD is a variant of Binary Decision Diagrams specifically designed for
//! **sparse set families** where most elements are absent from most sets.
//! Unlike BDDs which eliminate nodes where `low = high`, ZDDs eliminate nodes
//! where `high = ⊥` (zero-suppression rule).
//!
//! ## Key Features
//!
//! - **Manager-Centric**: All operations go through the [`ZddManager`] ensuring structural sharing
//! - **Set-Theoretic API**: Primary operations use set terminology (`union`, `intersection`)
//! - **Efficient for Sparse Sets**: Zero-suppression makes representation compact
//! - **Operation Caching**: Redundant computations are automatically avoided
//!
//! ## Quick Start
//!
//! ```rust
//! use ananke_zdd::zdd::ZddManager;
//!
//! let mut mgr = ZddManager::new();
//!
//! // Create singleton sets: {{1}}, {{2}}, {{3}}
//! let s1 = mgr.base(1);  // Family containing only {1}
//! let s2 = mgr.base(2);  // Family containing only {2}
//!
//! // Union: {{1}} ∪ {{2}} = {{1}, {2}}
//! let union = mgr.union(s1, s2);
//! assert_eq!(mgr.count(union), 2);
//!
//! // Join (cross product): {{1}} ⊗ {{2}} = {{1, 2}}
//! let joined = mgr.join(s1, s2);
//! assert_eq!(mgr.count(joined), 1);
//! ```
//!
//! ## Modules
//!
//! - [`mod@zdd`] — The ZDD manager and core algorithms
//! - [`mod@reference`] — The [`ZddId`] type: a 32-bit handle to ZDD nodes
//! - [`mod@dot`] — Graphviz visualization
//!
//! ## Comparison with BDDs
//!
//! | Aspect | BDD | ZDD |
//! |--------|-----|-----|
//! | Reduction rule | `lo = hi → lo` | `hi = ⊥ → lo` |
//! | Optimized for | Boolean functions | Set families |
//! | Negation | O(1) with complement edges | O(n) or cached |
//! | Terminal ⊤ | Function always true | Family = {∅} |
//!
//! [`ZddManager`]: crate::zdd::ZddManager
//! [`ZddId`]: crate::reference::ZddId

pub mod cache;
pub mod dot;
pub mod iter;
pub mod node;
pub mod reference;
pub mod subtable;
pub mod types;
pub mod zdd;
