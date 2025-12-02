//! Cache implementations for BDD operation memoization.
//!
//! This module provides several cache implementations with different trade-offs:
//!
//! | Implementation | Complexity | Collision Rate | Memory | Clear | Use Case |
//! |----------------|------------|----------------|--------|-------|----------|
//! | [`HashMapCache`] | Simplest | None | Highest | O(n) | Production (default) |
//! | [`BasicCache`] | Simple | High | Low | O(n) | Minimal overhead |
//! | [`DirectMappedCache`] | Medium | High | Medium | O(1) | When O(1) clear matters |
//! | [`SetAssociativeCache`] | Complex | Low | Medium | O(1) | Memory-constrained |
//!
//! # Choosing a Cache
//!
//! - **Need best performance?** Use [`HashMapCache`] (default) - zero collisions, dynamic sizing
//! - **Need O(1) clear?** Use [`SetAssociativeCache`] or [`DirectMappedCache`]
//! - **Need fixed memory?** Use [`SetAssociativeCache`] with large `bits` (18+)
//! - **Need minimal overhead?** Use [`BasicCache`]
//!
//! # Default
//!
//! The type alias [`Cache`] points to [`HashMapCache`], which provides
//! the best performance for typical BDD workloads. It has zero collisions
//! and dynamically grows as needed.
//!
//! [`SetAssociativeCache`] is useful when you need O(1) `clear()` or fixed memory,
//! but requires larger cache sizes (18+ bits) to match HashMap's hit rate.
//!
//! # Example
//!
//! ```ignore
//! use bdd_rs::cache::{Cache, DirectMappedCache, SetAssociativeCache};
//!
//! // Use the default (HashMap) cache
//! let mut cache = Cache::<(u64, u64), i32>::new(14);
//! cache.insert((1, 2), 42);
//! assert_eq!(cache.get(&(1, 2)), Some(&42));
//!
//! // Or use set-associative for O(1) clear
//! let mut fixed = SetAssociativeCache::<(u64, u64), i32>::new(18);
//!
//! // Or use direct-mapped for simplest fixed-size cache
//! let mut simple = DirectMappedCache::<(u64, u64), i32>::new(14);
//! ```

mod basic;
mod direct_mapped;
mod hashmap;
mod set_associative;

pub use basic::BasicCache;
pub use direct_mapped::DirectMappedCache;
pub use hashmap::HashMapCache;
pub use set_associative::SetAssociativeCache;

/// Default cache implementation.
pub type Cache<K, V> = HashMapCache<K, V>;
