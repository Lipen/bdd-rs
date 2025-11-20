//! Type Domain.
//!
//! Tracks the runtime type of variables.
//! Essential for analyzing dynamically typed languages or polymorphic code.

use std::collections::BTreeSet;
use std::fmt::Debug;

use crate::domain::AbstractDomain;

/// Represents a concrete runtime type.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum Type {
    Integer,
    Float,
    Boolean,
    String,
    Object,
    Null,
}

/// Represents a set of possible types.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TypeSet {
    Bottom,
    Set(BTreeSet<Type>),
    Top,
}

/// Type Domain.
///
/// Lattice:
/// Bottom <= Set(types) <= Top
/// Set(A) <= Set(B) iff A is subset of B.
#[derive(Clone, Debug)]
pub struct TypeDomain;

impl TypeDomain {
    /// Create a singleton type set.
    pub fn from_type(&self, t: Type) -> TypeSet {
        let mut set = BTreeSet::new();
        set.insert(t);
        TypeSet::Set(set)
    }

    /// Check if a variable definitely has a specific type.
    pub fn is_exactly(&self, elem: &TypeSet, t: Type) -> bool {
        match elem {
            TypeSet::Set(s) => s.len() == 1 && s.contains(&t),
            _ => false,
        }
    }

    /// Check if a variable *may* have a specific type.
    pub fn may_be(&self, elem: &TypeSet, t: Type) -> bool {
        match elem {
            TypeSet::Bottom => false,
            TypeSet::Top => true,
            TypeSet::Set(s) => s.contains(&t),
        }
    }
}

impl AbstractDomain for TypeDomain {
    type Element = TypeSet;

    fn bottom(&self) -> Self::Element {
        TypeSet::Bottom
    }

    fn top(&self) -> Self::Element {
        TypeSet::Top
    }

    fn is_bottom(&self, elem: &Self::Element) -> bool {
        matches!(elem, TypeSet::Bottom)
    }

    fn is_top(&self, elem: &Self::Element) -> bool {
        matches!(elem, TypeSet::Top)
    }

    fn le(&self, elem1: &Self::Element, elem2: &Self::Element) -> bool {
        match (elem1, elem2) {
            (TypeSet::Bottom, _) => true,
            (_, TypeSet::Top) => true,
            (TypeSet::Set(s1), TypeSet::Set(s2)) => s1.is_subset(s2),
            _ => false,
        }
    }

    fn join(&self, elem1: &Self::Element, elem2: &Self::Element) -> Self::Element {
        match (elem1, elem2) {
            (TypeSet::Bottom, e) | (e, TypeSet::Bottom) => e.clone(),
            (TypeSet::Top, _) | (_, TypeSet::Top) => TypeSet::Top,
            (TypeSet::Set(s1), TypeSet::Set(s2)) => {
                let mut res = s1.clone();
                res.extend(s2.iter().cloned());
                TypeSet::Set(res)
            }
        }
    }

    fn meet(&self, elem1: &Self::Element, elem2: &Self::Element) -> Self::Element {
        match (elem1, elem2) {
            (TypeSet::Bottom, _) | (_, TypeSet::Bottom) => TypeSet::Bottom,
            (TypeSet::Top, e) | (e, TypeSet::Top) => e.clone(),
            (TypeSet::Set(s1), TypeSet::Set(s2)) => {
                let res: BTreeSet<Type> = s1.intersection(s2).cloned().collect();
                if res.is_empty() {
                    TypeSet::Bottom
                } else {
                    TypeSet::Set(res)
                }
            }
        }
    }

    fn widen(&self, elem1: &Self::Element, elem2: &Self::Element) -> Self::Element {
        // Finite lattice (set of types is small), so join is sufficient.
        self.join(elem1, elem2)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_type_domain_lattice() {
        let domain = TypeDomain;
        let t_int = domain.from_type(Type::Integer);
        let t_str = domain.from_type(Type::String);
        let bottom = TypeSet::Bottom;
        let top = TypeSet::Top;

        // Order
        assert!(domain.le(&bottom, &t_int));
        assert!(domain.le(&t_int, &top));
        assert!(!domain.le(&t_int, &t_str));

        // Join
        let joined = domain.join(&t_int, &t_str);
        assert!(domain.le(&t_int, &joined));
        assert!(domain.le(&t_str, &joined));
        assert!(domain.may_be(&joined, Type::Integer));
        assert!(domain.may_be(&joined, Type::String));

        // Meet
        let meet = domain.meet(&t_int, &t_str);
        assert!(domain.is_bottom(&meet));
    }
}
