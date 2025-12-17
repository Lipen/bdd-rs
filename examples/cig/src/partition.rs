//! Partition representation for variable sets.
//!
//! A partition of a set S is a collection of non-empty, pairwise disjoint
//! subsets (blocks) whose union is S.

use std::fmt;

use crate::variable::{Var, VarSet};

/// A partition of a variable set into blocks.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Partition {
    /// The blocks of the partition, sorted for canonicity.
    blocks: Vec<VarSet>,
}

impl Partition {
    /// Create the discrete partition (each variable in its own block).
    pub fn discrete(vars: &VarSet) -> Self {
        let blocks: Vec<VarSet> = vars.iter().map(VarSet::singleton).collect();
        Partition { blocks }
    }

    /// Create the indiscrete partition (all variables in one block).
    pub fn indiscrete(vars: VarSet) -> Self {
        if vars.is_empty() {
            Partition { blocks: Vec::new() }
        } else {
            Partition { blocks: vec![vars] }
        }
    }

    /// Create a partition from blocks.
    ///
    /// # Panics
    ///
    /// Panics if blocks are not pairwise disjoint.
    pub fn from_blocks(mut blocks: Vec<VarSet>) -> Self {
        // Sort blocks for canonicity (by first element)
        blocks.sort_by(|a, b| a.iter().next().map(|v| v.index()).cmp(&b.iter().next().map(|v| v.index())));

        // Verify disjointness
        for i in 0..blocks.len() {
            for j in (i + 1)..blocks.len() {
                assert!(blocks[i].is_disjoint(&blocks[j]), "Partition blocks must be disjoint");
            }
        }

        Partition { blocks }
    }

    /// Create a two-block partition.
    pub fn two_blocks(a: VarSet, b: VarSet) -> Self {
        assert!(a.is_disjoint(&b), "Partition blocks must be disjoint");
        Partition::from_blocks(vec![a, b])
    }

    /// Get the number of blocks.
    pub fn num_blocks(&self) -> usize {
        self.blocks.len()
    }

    /// Check if this is the discrete partition.
    pub fn is_discrete(&self) -> bool {
        self.blocks.iter().all(|b| b.len() == 1)
    }

    /// Check if this is the indiscrete partition.
    pub fn is_indiscrete(&self) -> bool {
        self.blocks.len() == 1
    }

    /// Check if this is a non-trivial partition.
    pub fn is_nontrivial(&self) -> bool {
        self.num_blocks() > 1 && !self.is_discrete()
    }

    /// Get the blocks.
    pub fn blocks(&self) -> &[VarSet] {
        &self.blocks
    }

    /// Get the total set of variables.
    pub fn variables(&self) -> VarSet {
        self.blocks.iter().fold(VarSet::empty(), |acc, b| acc.union(b))
    }

    /// Find which block contains a variable.
    pub fn block_of(&self, var: Var) -> Option<usize> {
        self.blocks.iter().position(|b| b.contains(var))
    }

    /// Merge two blocks (by index).
    pub fn merge(&mut self, i: usize, j: usize) {
        assert!(i < self.blocks.len() && j < self.blocks.len());
        if i == j {
            return;
        }
        let (i, j) = if i < j { (i, j) } else { (j, i) };
        let removed = self.blocks.remove(j);
        self.blocks[i] = self.blocks[i].union(&removed);
    }

    /// Check if this partition refines another.
    ///
    /// π₁ refines π₂ if every block of π₁ is contained in some block of π₂.
    pub fn refines(&self, other: &Self) -> bool {
        self.blocks.iter().all(|b1| other.blocks.iter().any(|b2| b1.is_subset(b2)))
    }

    /// Iterate over all non-trivial two-block partitions of the given variables.
    pub fn two_partitions(vars: &VarSet) -> TwoPartitionIter {
        TwoPartitionIter::new(vars.clone())
    }
}

impl fmt::Display for Partition {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{{")?;
        for (i, block) in self.blocks.iter().enumerate() {
            if i > 0 {
                write!(f, ", ")?;
            }
            write!(f, "{}", block)?;
        }
        write!(f, "}}")
    }
}

/// Iterator over all non-trivial two-block partitions.
///
/// For a set of n elements, iterates over all (A, B) where:
/// - A ∪ B = S
/// - A ∩ B = ∅
/// - A, B ≠ ∅
/// - We only emit each partition once (A before B lexicographically).
pub struct TwoPartitionIter {
    vars: Vec<Var>,
    /// Current subset mask for block A.
    /// We iterate masks from 1 to 2^(n-1) - 1 to avoid duplicates.
    current: usize,
    max: usize,
}

impl TwoPartitionIter {
    fn new(vars: VarSet) -> Self {
        let vars: Vec<Var> = vars.iter().collect();
        let n = vars.len();
        if n < 2 {
            // No non-trivial partitions possible
            TwoPartitionIter { vars, current: 0, max: 0 }
        } else {
            // We use masks from 1 to 2^(n-1) - 1
            // This gives us all partitions without duplicates
            TwoPartitionIter {
                vars,
                current: 1,
                max: 1 << (n - 1),
            }
        }
    }
}

impl Iterator for TwoPartitionIter {
    type Item = (VarSet, VarSet);

    fn next(&mut self) -> Option<Self::Item> {
        if self.current >= self.max {
            return None;
        }

        let mask = self.current;
        self.current += 1;

        let mut a = VarSet::empty();
        let mut b = VarSet::empty();

        for (i, &var) in self.vars.iter().enumerate() {
            if (mask >> i) & 1 == 1 {
                a.insert(var);
            } else {
                b.insert(var);
            }
        }

        Some((a, b))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_discrete_partition() {
        let vars = VarSet::from_iter([Var(1), Var(2), Var(3)]);
        let p = Partition::discrete(&vars);

        assert_eq!(p.num_blocks(), 3);
        assert!(p.is_discrete());
        assert!(!p.is_indiscrete());
    }

    #[test]
    fn test_indiscrete_partition() {
        let vars = VarSet::from_iter([Var(1), Var(2), Var(3)]);
        let p = Partition::indiscrete(vars);

        assert_eq!(p.num_blocks(), 1);
        assert!(!p.is_discrete());
        assert!(p.is_indiscrete());
    }

    #[test]
    fn test_two_partitions() {
        let vars = VarSet::from_iter([Var(1), Var(2), Var(3)]);
        let partitions: Vec<_> = Partition::two_partitions(&vars).collect();

        // For 3 elements, there are 2^(3-1) - 1 = 3 non-trivial partitions
        assert_eq!(partitions.len(), 3);

        // Each partition should cover all variables
        for (a, b) in &partitions {
            assert!(!a.is_empty());
            assert!(!b.is_empty());
            assert!(a.is_disjoint(b));
            assert_eq!(a.union(b), vars);
        }
    }

    #[test]
    fn test_merge() {
        let vars = VarSet::from_iter([Var(1), Var(2), Var(3)]);
        let mut p = Partition::discrete(&vars);

        p.merge(0, 1);
        assert_eq!(p.num_blocks(), 2);
    }

    #[test]
    fn test_refines() {
        let vars = VarSet::from_iter([Var(1), Var(2), Var(3)]);
        let discrete = Partition::discrete(&vars);
        let indiscrete = Partition::indiscrete(vars);

        assert!(discrete.refines(&indiscrete));
        assert!(!indiscrete.refines(&discrete));
    }
}
