//! Product domain: combines two abstract domains component-wise.

use super::domain::AbstractDomain;
use std::fmt::Debug;

/// Product of two abstract domains.
///
/// The product domain combines a control domain (typically BDD) with
/// a data domain (typically numeric) to enable path-sensitive analysis.
#[derive(Debug, Clone)]
pub struct ProductDomain<C, N>
where
    C: AbstractDomain,
    N: AbstractDomain,
{
    pub control: C,
    pub numeric: N,
}

/// Element of the product domain.
#[derive(Debug, Clone, PartialEq)]
pub struct ProductElement<C, N> {
    pub control: C,
    pub numeric: N,
}

impl<C, N> ProductDomain<C, N>
where
    C: AbstractDomain,
    N: AbstractDomain,
{
    pub fn new(control: C, numeric: N) -> Self {
        Self { control, numeric }
    }
}

impl<C, N> AbstractDomain for ProductDomain<C, N>
where
    C: AbstractDomain,
    N: AbstractDomain,
    C::Element: Debug + Clone + PartialEq,
    N::Element: Debug + Clone + PartialEq,
{
    type Element = ProductElement<C::Element, N::Element>;

    fn bottom(&self) -> Self::Element {
        ProductElement {
            control: self.control.bottom(),
            numeric: self.numeric.bottom(),
        }
    }

    fn top(&self) -> Self::Element {
        ProductElement {
            control: self.control.top(),
            numeric: self.numeric.top(),
        }
    }

    fn is_bottom(&self, elem: &Self::Element) -> bool {
        self.control.is_bottom(&elem.control) || self.numeric.is_bottom(&elem.numeric)
    }

    fn is_top(&self, elem: &Self::Element) -> bool {
        self.control.is_top(&elem.control) && self.numeric.is_top(&elem.numeric)
    }

    fn le(&self, elem1: &Self::Element, elem2: &Self::Element) -> bool {
        self.control.le(&elem1.control, &elem2.control)
            && self.numeric.le(&elem1.numeric, &elem2.numeric)
    }

    fn join(&self, elem1: &Self::Element, elem2: &Self::Element) -> Self::Element {
        ProductElement {
            control: self.control.join(&elem1.control, &elem2.control),
            numeric: self.numeric.join(&elem1.numeric, &elem2.numeric),
        }
    }

    fn meet(&self, elem1: &Self::Element, elem2: &Self::Element) -> Self::Element {
        ProductElement {
            control: self.control.meet(&elem1.control, &elem2.control),
            numeric: self.numeric.meet(&elem1.numeric, &elem2.numeric),
        }
    }

    fn widen(&self, elem1: &Self::Element, elem2: &Self::Element) -> Self::Element {
        ProductElement {
            control: self.control.widen(&elem1.control, &elem2.control),
            numeric: self.numeric.widen(&elem1.numeric, &elem2.numeric),
        }
    }

    fn narrow(&self, elem1: &Self::Element, elem2: &Self::Element) -> Self::Element {
        ProductElement {
            control: self.control.narrow(&elem1.control, &elem2.control),
            numeric: self.numeric.narrow(&elem1.numeric, &elem2.numeric),
        }
    }
}
