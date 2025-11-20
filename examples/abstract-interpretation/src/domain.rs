//! Core abstract domain trait and utilities.

use std::fmt::Debug;

/// Abstract domain interface.
///
/// An abstract domain represents a lattice structure used for
/// approximating program states in static analysis.
///
/// # Lattice Properties
///
/// An abstract domain must satisfy:
/// - Reflexivity: `∀a. a ⊑ a`
/// - Transitivity: `∀a,b,c. a ⊑ b ∧ b ⊑ c ⇒ a ⊑ c`
/// - Antisymmetry: `∀a,b. a ⊑ b ∧ b ⊑ a ⇒ a = b`
/// - Join/Meet properties: See lattice theory
pub trait AbstractDomain: Clone + Debug + Sized {
    /// The type representing abstract elements.
    type Element: Clone + Debug + PartialEq;

    /// Create the bottom element (⊥): represents the empty set.
    fn bottom(&self) -> Self::Element;

    /// Create the top element (⊤): represents all possible states.
    fn top(&self) -> Self::Element;

    /// Check if an element is bottom.
    fn is_bottom(&self, elem: &Self::Element) -> bool;

    /// Check if an element is top.
    fn is_top(&self, elem: &Self::Element) -> bool;

    /// Partial order: `elem1 ⊑ elem2` (elem1 is more precise than elem2).
    ///
    /// Returns true if elem1 represents a subset of states represented by elem2.
    fn le(&self, elem1: &Self::Element, elem2: &Self::Element) -> bool;

    /// Join (`⊔`): least upper bound, over-approximation.
    ///
    /// Returns the smallest element that contains both inputs.
    /// Represents union of state sets.
    fn join(&self, elem1: &Self::Element, elem2: &Self::Element) -> Self::Element;

    /// Meet (`⊓`): greatest lower bound, refinement.
    ///
    /// Returns the largest element contained in both inputs.
    /// Represents intersection of state sets.
    fn meet(&self, elem1: &Self::Element, elem2: &Self::Element) -> Self::Element;

    /// Widening (`∇`): accelerates convergence in fixpoint computation.
    ///
    /// Returns an over-approximation that ensures termination.
    /// Must satisfy: `elem1 ⊑ elem1 ∇ elem2`
    ///
    /// **Why no default?** Widening must extrapolate (e.g., to ±∞) to force
    /// termination on ascending chains. Using join would not guarantee this.
    /// Each domain needs domain-specific widening logic.
    fn widen(&self, elem1: &Self::Element, elem2: &Self::Element) -> Self::Element;

    /// Narrowing (`∆`): refines over-approximation after widening.
    ///
    /// Returns a more precise element without losing convergence guarantees.
    /// Default implementation uses meet, which is safe and often sufficient.
    ///
    /// **Why meet as default?** After widening converges, narrowing refines
    /// by intersecting with more precise approximations. Meet provides
    /// a safe conservative default, and narrowing is limited to few iterations.
    /// Domains can override for better precision (e.g., dual widening).
    fn narrow(&self, elem1: &Self::Element, elem2: &Self::Element) -> Self::Element {
        self.meet(elem1, elem2)
    }

    /// Check equality of abstract elements.
    fn eq(&self, elem1: &Self::Element, elem2: &Self::Element) -> bool {
        self.le(elem1, elem2) && self.le(elem2, elem1)
    }

    /// Join multiple elements.
    fn join_many<I>(&self, elems: I) -> Self::Element
    where
        I: IntoIterator<Item = Self::Element>,
    {
        elems.into_iter().fold(self.bottom(), |acc, e| self.join(&acc, &e))
    }
}

#[cfg(test)]
pub mod tests {
    use super::*;

    /// Test helper: validate basic lattice axioms
    pub fn test_lattice_axioms<D: AbstractDomain>(domain: &D, samples: &[D::Element]) {
        for a in samples {
            // Reflexivity: a ⊑ a
            assert!(domain.le(a, a), "Reflexivity failed");

            // Identity: a ⊔ ⊥ = a
            let joined = domain.join(a, &domain.bottom());
            assert!(domain.eq(a, &joined), "Join with bottom failed");

            // Identity: a ⊓ ⊤ = a
            let met = domain.meet(a, &domain.top());
            assert!(domain.eq(a, &met), "Meet with top failed");

            // Widening preserves order: a ⊑ (a ∇ b)
            for b in samples {
                let widened = domain.widen(a, b);
                assert!(domain.le(a, &widened), "Widening does not preserve order");
            }
        }

        for a in samples {
            for b in samples {
                // Commutativity: a ⊔ b = b ⊔ a
                let ab = domain.join(a, b);
                let ba = domain.join(b, a);
                assert!(domain.eq(&ab, &ba), "Join commutativity failed");

                // Commutativity: a ⊓ b = b ⊓ a
                let ab = domain.meet(a, b);
                let ba = domain.meet(b, a);
                assert!(domain.eq(&ab, &ba), "Meet commutativity failed");

                // Join upper bound: a ⊑ (a ⊔ b)
                let joined = domain.join(a, b);
                assert!(domain.le(a, &joined), "Join is not upper bound for a");
                assert!(domain.le(b, &joined), "Join is not upper bound for b");

                // Meet lower bound: (a ⊓ b) ⊑ a
                let met = domain.meet(a, b);
                assert!(domain.le(&met, a), "Meet is not lower bound of a");
                assert!(domain.le(&met, b), "Meet is not lower bound of b");
            }
        }
    }
}
