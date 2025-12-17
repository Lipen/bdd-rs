//! Variable representation for CIG.
//!
//! Variables are 1-indexed positive integers, following the convention
//! used in BDD literature and the ananke-bdd crate.

use std::fmt;

/// A Boolean variable identifier.
///
/// Variables are 1-indexed: x₁, x₂, x₃, ...
/// Variable 0 is reserved and should not be used.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Var(pub u32);

impl Var {
    /// Create a new variable with the given index.
    ///
    /// # Panics
    ///
    /// Panics if `index` is 0 (reserved).
    pub fn new(index: u32) -> Self {
        assert!(index > 0, "Variable index must be positive (1-indexed)");
        Var(index)
    }

    /// Get the variable index (1-indexed).
    #[inline]
    pub fn index(self) -> u32 {
        self.0
    }

    /// Get the 0-based position for array indexing.
    #[inline]
    pub fn position(self) -> usize {
        (self.0 - 1) as usize
    }
}

impl fmt::Display for Var {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "x{}", self.0)
    }
}

impl From<u32> for Var {
    fn from(index: u32) -> Self {
        Var::new(index)
    }
}

impl From<usize> for Var {
    fn from(index: usize) -> Self {
        Var::new(index as u32)
    }
}

/// A set of variables, represented efficiently.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct VarSet {
    /// Sorted list of variables.
    vars: Vec<Var>,
}

impl VarSet {
    /// Create an empty variable set.
    pub fn empty() -> Self {
        VarSet { vars: Vec::new() }
    }

    /// Create a variable set from an iterator.
    pub fn from_iter(iter: impl IntoIterator<Item = Var>) -> Self {
        let mut vars: Vec<Var> = iter.into_iter().collect();
        vars.sort();
        vars.dedup();
        VarSet { vars }
    }

    /// Create a variable set containing variables 1..=n.
    pub fn all(n: u32) -> Self {
        VarSet {
            vars: (1..=n).map(Var).collect(),
        }
    }

    /// Create a singleton set.
    pub fn singleton(var: Var) -> Self {
        VarSet { vars: vec![var] }
    }

    /// Check if the set is empty.
    pub fn is_empty(&self) -> bool {
        self.vars.is_empty()
    }

    /// Get the number of variables.
    pub fn len(&self) -> usize {
        self.vars.len()
    }

    /// Check if the set contains a variable.
    pub fn contains(&self, var: Var) -> bool {
        self.vars.binary_search(&var).is_ok()
    }

    /// Insert a variable into the set.
    pub fn insert(&mut self, var: Var) {
        if let Err(pos) = self.vars.binary_search(&var) {
            self.vars.insert(pos, var);
        }
    }

    /// Remove a variable from the set.
    pub fn remove(&mut self, var: Var) {
        if let Ok(pos) = self.vars.binary_search(&var) {
            self.vars.remove(pos);
        }
    }

    /// Compute the union of two sets.
    pub fn union(&self, other: &Self) -> Self {
        let mut result = self.clone();
        for &var in &other.vars {
            result.insert(var);
        }
        result
    }

    /// Compute the intersection of two sets.
    pub fn intersection(&self, other: &Self) -> Self {
        VarSet {
            vars: self.vars.iter().filter(|v| other.contains(**v)).copied().collect(),
        }
    }

    /// Compute the difference: self \ other.
    pub fn difference(&self, other: &Self) -> Self {
        VarSet {
            vars: self.vars.iter().filter(|v| !other.contains(**v)).copied().collect(),
        }
    }

    /// Check if two sets are disjoint.
    pub fn is_disjoint(&self, other: &Self) -> bool {
        self.intersection(other).is_empty()
    }

    /// Check if self is a subset of other.
    pub fn is_subset(&self, other: &Self) -> bool {
        self.vars.iter().all(|v| other.contains(*v))
    }

    /// Iterate over variables.
    pub fn iter(&self) -> impl Iterator<Item = Var> + '_ {
        self.vars.iter().copied()
    }

    /// Get variables as a slice.
    pub fn as_slice(&self) -> &[Var] {
        &self.vars
    }
}

impl fmt::Display for VarSet {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{{")?;
        for (i, var) in self.vars.iter().enumerate() {
            if i > 0 {
                write!(f, ", ")?;
            }
            write!(f, "{}", var)?;
        }
        write!(f, "}}")
    }
}

impl FromIterator<Var> for VarSet {
    fn from_iter<T: IntoIterator<Item = Var>>(iter: T) -> Self {
        VarSet::from_iter(iter)
    }
}

impl<'a> IntoIterator for &'a VarSet {
    type Item = Var;
    type IntoIter = std::iter::Copied<std::slice::Iter<'a, Var>>;

    fn into_iter(self) -> Self::IntoIter {
        self.vars.iter().copied()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_var_creation() {
        let x1 = Var::new(1);
        let x2 = Var::new(2);
        assert_eq!(x1.index(), 1);
        assert_eq!(x2.index(), 2);
        assert_eq!(x1.position(), 0);
        assert_eq!(x2.position(), 1);
    }

    #[test]
    #[should_panic(expected = "must be positive")]
    fn test_var_zero_panics() {
        Var::new(0);
    }

    #[test]
    fn test_varset_operations() {
        let a = VarSet::from_iter([Var(1), Var(2)]);
        let b = VarSet::from_iter([Var(2), Var(3)]);

        let union = a.union(&b);
        assert_eq!(union.len(), 3);
        assert!(union.contains(Var(1)));
        assert!(union.contains(Var(2)));
        assert!(union.contains(Var(3)));

        let inter = a.intersection(&b);
        assert_eq!(inter.len(), 1);
        assert!(inter.contains(Var(2)));

        let diff = a.difference(&b);
        assert_eq!(diff.len(), 1);
        assert!(diff.contains(Var(1)));
    }
}
