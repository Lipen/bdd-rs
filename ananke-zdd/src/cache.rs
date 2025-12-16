//! Operation cache for ZDD computations.
//!
//! Caches results of binary operations to avoid redundant computation.

use std::collections::HashMap;

use crate::reference::ZddId;

/// Cache key for binary operations.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct CacheKey {
    pub op: OpType,
    pub f: ZddId,
    pub g: ZddId,
}

/// Operation types for caching.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum OpType {
    Union,
    Intersection,
    Difference,
    SymDiff,
    Join,
    Meet,
}

impl CacheKey {
    /// Create a key for a commutative operation, normalizing operand order.
    pub fn commutative(op: OpType, f: ZddId, g: ZddId) -> Self {
        let (f, g) = if f.raw() <= g.raw() { (f, g) } else { (g, f) };
        Self { op, f, g }
    }

    /// Create a key for a non-commutative operation.
    pub fn non_commutative(op: OpType, f: ZddId, g: ZddId) -> Self {
        Self { op, f, g }
    }
}

/// Operation cache using HashMap.
#[derive(Debug, Clone)]
pub struct Cache {
    map: HashMap<CacheKey, ZddId>,
}

impl Default for Cache {
    fn default() -> Self {
        Self::new()
    }
}

impl Cache {
    /// Create a new empty cache.
    pub fn new() -> Self {
        Self { map: HashMap::new() }
    }

    /// Create a cache with specified initial capacity.
    pub fn with_capacity(capacity: usize) -> Self {
        Self {
            map: HashMap::with_capacity(capacity),
        }
    }

    /// Look up a cached result.
    pub fn get(&self, key: &CacheKey) -> Option<ZddId> {
        self.map.get(key).copied()
    }

    /// Insert a result into the cache.
    pub fn insert(&mut self, key: CacheKey, value: ZddId) {
        self.map.insert(key, value);
    }

    /// Clear the cache.
    pub fn clear(&mut self) {
        self.map.clear();
    }

    /// Number of cached entries.
    pub fn len(&self) -> usize {
        self.map.len()
    }

    /// Returns true if the cache is empty.
    pub fn is_empty(&self) -> bool {
        self.map.is_empty()
    }
}

/// Cache for counting operations.
#[derive(Debug, Clone, Default)]
pub struct CountCache {
    map: HashMap<ZddId, u64>,
}

impl CountCache {
    /// Create a new count cache.
    pub fn new() -> Self {
        Self { map: HashMap::new() }
    }

    /// Look up a cached count.
    pub fn get(&self, id: ZddId) -> Option<u64> {
        self.map.get(&id).copied()
    }

    /// Insert a count into the cache.
    pub fn insert(&mut self, id: ZddId, count: u64) {
        self.map.insert(id, count);
    }

    /// Clear the cache.
    pub fn clear(&mut self) {
        self.map.clear();
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_commutative_key() {
        let k1 = CacheKey::commutative(OpType::Union, ZddId::new(1), ZddId::new(2));
        let k2 = CacheKey::commutative(OpType::Union, ZddId::new(2), ZddId::new(1));
        assert_eq!(k1, k2);
    }

    #[test]
    fn test_cache_operations() {
        let mut cache = Cache::new();
        let key = CacheKey::commutative(OpType::Union, ZddId::new(1), ZddId::new(2));

        assert!(cache.get(&key).is_none());

        cache.insert(key, ZddId::new(3));
        assert_eq!(cache.get(&key), Some(ZddId::new(3)));

        cache.clear();
        assert!(cache.is_empty());
    }
}
