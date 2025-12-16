//! Iterator for enumerating sets in a ZDD.

use crate::reference::ZddId;
use crate::types::Var;
use crate::zdd::ZddManager;

/// Iterator that yields all sets in a ZDD family.
pub struct SetIterator<'a> {
    mgr: &'a ZddManager,
    /// Stack of (ZddId, current_set, visited_hi)
    stack: Vec<(ZddId, Vec<Var>, bool)>,
}

impl<'a> SetIterator<'a> {
    /// Creates a new iterator over sets in the given ZDD.
    pub fn new(mgr: &'a ZddManager, root: ZddId) -> Self {
        let mut iter = Self { mgr, stack: Vec::new() };
        if !root.is_zero() {
            iter.stack.push((root, Vec::new(), false));
        }
        iter
    }
}

impl<'a> Iterator for SetIterator<'a> {
    type Item = Vec<Var>;

    fn next(&mut self) -> Option<Self::Item> {
        while let Some((id, current_set, visited_hi)) = self.stack.pop() {
            if id.is_zero() {
                continue;
            }

            if id.is_one() {
                // Reached terminal, yield current set
                return Some(current_set);
            }

            let node = self.mgr.node(id);

            if !visited_hi {
                // First visit: push hi branch, then lo branch
                // Push current state back to explore hi later
                self.stack.push((id, current_set.clone(), true));
                // Explore lo branch (sets without this variable)
                self.stack.push((node.lo, current_set, false));
            } else {
                // Already explored lo, now explore hi
                let mut hi_set = current_set;
                hi_set.push(node.var);
                self.stack.push((node.hi, hi_set, false));
            }
        }
        None
    }
}

impl ZddManager {
    /// Returns an iterator over all sets in the family.
    ///
    /// # Example
    ///
    /// ```
    /// use ananke_zdd::zdd::ZddManager;
    ///
    /// let mgr = ZddManager::new();
    /// let ps = mgr.powerset([1u32, 2]);
    ///
    /// let sets: Vec<_> = mgr.iter_sets(ps).collect();
    /// assert_eq!(sets.len(), 4);
    /// ```
    pub fn iter_sets(&self, f: ZddId) -> SetIterator<'_> {
        SetIterator::new(self, f)
    }

    /// Collects all sets into a vector of vectors.
    pub fn collect_sets(&self, f: ZddId) -> Vec<Vec<Var>> {
        self.iter_sets(f).collect()
    }

    /// Returns one arbitrary set from the family, if non-empty.
    pub fn pick_one(&self, f: ZddId) -> Option<Vec<Var>> {
        if f.is_zero() {
            return None;
        }
        if f.is_one() {
            return Some(Vec::new());
        }

        let mut result = Vec::new();
        let mut current = f;

        while !current.is_terminal() {
            let node = self.node(current);
            // Prefer hi branch to get a non-empty set
            result.push(node.var);
            current = node.hi;
        }

        Some(result)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_iter_empty() {
        let mgr = ZddManager::new();
        let sets: Vec<_> = mgr.iter_sets(ZddId::ZERO).collect();
        assert!(sets.is_empty());
    }

    #[test]
    fn test_iter_one() {
        let mgr = ZddManager::new();
        let sets: Vec<_> = mgr.iter_sets(ZddId::ONE).collect();
        assert_eq!(sets.len(), 1);
        assert!(sets[0].is_empty());
    }

    #[test]
    fn test_iter_base() {
        let mgr = ZddManager::new();
        let x1 = mgr.base(1);
        let sets: Vec<_> = mgr.iter_sets(x1).collect();
        assert_eq!(sets.len(), 1);
        assert_eq!(sets[0], vec![Var::new(1)]);
    }

    #[test]
    fn test_iter_powerset() {
        let mgr = ZddManager::new();
        let ps = mgr.powerset([1u32, 2]);
        let sets: Vec<_> = mgr.iter_sets(ps).collect();
        assert_eq!(sets.len(), 4);
    }

    #[test]
    fn test_pick_one() {
        let mgr = ZddManager::new();

        assert!(mgr.pick_one(ZddId::ZERO).is_none());

        let one = mgr.pick_one(ZddId::ONE);
        assert_eq!(one, Some(vec![]));

        let x1 = mgr.base(1);
        let picked = mgr.pick_one(x1);
        assert_eq!(picked, Some(vec![Var::new(1)]));
    }
}
