//! Cache implementations for BDD operation memoization.
//!
//! This module provides several cache implementations with different trade-offs:
//!
//! | Implementation | Complexity | Collision Rate | Memory | Clear | Use Case |
//! |----------------|------------|----------------|--------|-------|----------|
//! | [`HashMapCache`] | Simplest | None | Highest | O(n) | Debugging, small problems |
//! | [`BasicCache`] | Simple | High | Low | O(n) | Minimal overhead |
//! | [`DirectMappedCache`] | Medium | High | Medium | O(1) | When O(1) clear matters |
//! | [`SetAssociativeCache`] | Complex | Low | Medium | O(1) | Production workloads |
//!
//! # Choosing a Cache
//!
//! - **Need highest hit rate?** Use [`SetAssociativeCache`] (default)
//! - **Need simplest code?** Use [`HashMapCache`]
//! - **Need O(1) clear but simple?** Use [`DirectMappedCache`]
//! - **Need minimal overhead?** Use [`BasicCache`]
//!
//! # Default
//!
//! The type alias [`Cache`] points to [`SetAssociativeCache`], which provides
//! the best performance for typical BDD workloads with high collision rates.
//!
//! # Example
//!
//! ```ignore
//! use bdd_rs::cache::{Cache, DirectMappedCache, HashMapCache};
//!
//! // Use the default (set-associative) cache
//! let mut cache = Cache::<(u64, u64), i32>::new(14);
//! cache.insert((1, 2), 42);
//! assert_eq!(cache.get(&(1, 2)), Some(&42));
//!
//! // Or explicitly choose a simpler implementation
//! let mut simple = DirectMappedCache::<(u64, u64), i32>::new(14);
//!
//! // Or use HashMap for debugging
//! let mut debug_cache = HashMapCache::<(u64, u64), i32>::new(14);
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
///
/// Currently uses [`SetAssociativeCache`] which provides:
/// - 4-way set-associativity (~90% fewer collisions than direct-mapped)
/// - LRU replacement within each set
/// - O(1) clearing via generation counters
///
/// For simpler implementations, use [`DirectMappedCache`] or [`BasicCache`].
pub type Cache<K, V> = SetAssociativeCache<K, V>;
