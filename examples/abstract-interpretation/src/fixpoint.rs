//! Fixpoint computation engine with widening and narrowing.

use super::domain::AbstractDomain;

/// Fixpoint computation engine.
///
/// Computes least/greatest fixpoints of monotone functions over
/// abstract domains, using widening to ensure termination.
#[derive(Debug, Clone)]
pub struct FixpointEngine<D: AbstractDomain> {
    pub domain: D,
    pub widening_threshold: usize,
    pub narrowing_iterations: usize,
    pub max_iterations: usize,
}

impl<D: AbstractDomain> FixpointEngine<D> {
    pub fn new(domain: D) -> Self {
        Self {
            domain,
            widening_threshold: 3,
            narrowing_iterations: 2,
            max_iterations: 1000,
        }
    }

    /// Compute least fixpoint: µX. F(X) ⊔ init
    ///
    /// Uses widening after threshold to ensure termination.
    pub fn lfp<F>(&self, init: D::Element, f: F) -> D::Element
    where
        F: Fn(&D::Element) -> D::Element,
    {
        let mut x = init.clone();
        let mut iterations = 0;

        loop {
            let fx = f(&x);
            let next = self.domain.join(&init, &fx);

            if self.domain.le(&next, &x) {
                // Fixpoint reached
                break;
            }

            iterations += 1;

            if iterations >= self.widening_threshold {
                // Apply widening
                x = self.domain.widen(&x, &next);
            } else {
                x = next;
            }

            // Safety: prevent infinite loops
            if iterations > self.max_iterations {
                log::warn!(
                    "Fixpoint computation did not converge after {} iterations",
                    self.max_iterations
                );
                break;
            }
        }

        log::debug!("Fixpoint converged after {} iterations", iterations);

        // Optional: narrowing phase for precision
        if self.narrowing_iterations > 0 {
            self.narrow(x, f)
        } else {
            x
        }
    }

    /// Narrowing phase to refine over-approximation.
    fn narrow<F>(&self, mut x: D::Element, f: F) -> D::Element
    where
        F: Fn(&D::Element) -> D::Element,
    {
        for i in 0..self.narrowing_iterations {
            let fx = f(&x);
            let next = self.domain.narrow(&x, &fx);

            if self.domain.le(&x, &next) {
                log::debug!("Narrowing converged after {} iterations", i + 1);
                break;
            }

            x = next;
        }

        x
    }

    /// Compute greatest fixpoint: νX. F(X) ⊓ init
    ///
    /// For safety properties and backward analysis.
    pub fn gfp<F>(&self, init: D::Element, f: F) -> D::Element
    where
        F: Fn(&D::Element) -> D::Element,
    {
        let mut x = init.clone();
        let mut iterations = 0;

        loop {
            let fx = f(&x);
            let next = self.domain.meet(&init, &fx);

            if self.domain.le(&x, &next) {
                break;
            }

            x = next;
            iterations += 1;

            if iterations > self.max_iterations {
                log::warn!(
                    "GFP computation did not converge after {} iterations",
                    self.max_iterations
                );
                break;
            }
        }

        log::debug!("Greatest fixpoint converged after {} iterations", iterations);
        x
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::interval::{Bound, Interval, IntervalDomain, IntervalElement};

    #[test]
    fn test_simple_fixpoint() {
        let domain = IntervalDomain;
        let engine = FixpointEngine::new(domain.clone());

        // Initial: x = 0
        let init = {
            let mut elem = IntervalElement::new();
            elem.set("x".to_string(), Interval::constant(0));
            elem
        };

        // Function: x := x + 1 (approximated as x ∪ {x+1})
        let f = |elem: &IntervalElement| {
            let x_int = elem.get("x");
            let incremented = Interval::new(
                x_int.low.add(&Bound::Finite(1)),
                x_int.high.add(&Bound::Finite(1)),
            );
            let joined = x_int.join(&incremented);

            let mut result = elem.clone();
            result.set("x".to_string(), joined);
            result
        };

        let result = engine.lfp(init, f);

        // After widening, should be [0, +∞]
        let x_result = result.get("x");
        assert_eq!(x_result.low, Bound::Finite(0));
        assert_eq!(x_result.high, Bound::PosInf);
    }
}
