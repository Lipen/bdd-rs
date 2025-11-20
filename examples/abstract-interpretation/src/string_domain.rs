//! String abstract domains.
//!
//! This module provides abstract domains for analyzing string values.
//!
//! # Domains
//!
//! - [`StringConstantDomain`]: Tracks exact string values (flat lattice).
//! - [`StringLengthDomain`]: Tracks string lengths using intervals.

use std::fmt::Debug;

use crate::domain::AbstractDomain;
use crate::expr::{NumExpr, NumPred};
use crate::interval::{Interval, IntervalDomain, IntervalElement};
use crate::numeric::NumericDomain;

/// Represents a string value in the constant domain.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum StringConst {
    /// Bottom: Unreachable / Empty set
    Bottom,
    /// Top: Any string
    Top,
    /// Constant: A specific string value
    Constant(String),
}

/// String Constant Domain.
///
/// A flat lattice where elements are ordered as:
/// Bottom <= Constant(s) <= Top
/// Constant(s1) <= Constant(s2) iff s1 == s2
#[derive(Clone, Debug)]
pub struct StringConstantDomain;

impl StringConstantDomain {
    /// Concatenate two abstract string values.
    /// "hello" + "world" = "helloworld"
    pub fn concat(&self, elem1: &StringConst, elem2: &StringConst) -> StringConst {
        match (elem1, elem2) {
            // If either input is Bottom (unreachable), result is Bottom
            (StringConst::Bottom, _) | (_, StringConst::Bottom) => StringConst::Bottom,
            // If both are known constants, we can compute the result
            (StringConst::Constant(s1), StringConst::Constant(s2)) => StringConst::Constant(format!("{}{}", s1, s2)),
            // If either is Top (unknown), the result is unknown
            _ => StringConst::Top,
        }
    }
}

impl AbstractDomain for StringConstantDomain {
    type Element = StringConst;

    fn bottom(&self) -> Self::Element {
        StringConst::Bottom
    }

    fn top(&self) -> Self::Element {
        StringConst::Top
    }

    fn is_bottom(&self, elem: &Self::Element) -> bool {
        matches!(elem, StringConst::Bottom)
    }

    fn is_top(&self, elem: &Self::Element) -> bool {
        matches!(elem, StringConst::Top)
    }

    fn le(&self, elem1: &Self::Element, elem2: &Self::Element) -> bool {
        match (elem1, elem2) {
            (StringConst::Bottom, _) => true,
            (_, StringConst::Top) => true,
            (StringConst::Constant(s1), StringConst::Constant(s2)) => s1 == s2,
            _ => false,
        }
    }

    fn join(&self, elem1: &Self::Element, elem2: &Self::Element) -> Self::Element {
        match (elem1, elem2) {
            (StringConst::Bottom, e) | (e, StringConst::Bottom) => e.clone(),
            (StringConst::Top, _) | (_, StringConst::Top) => StringConst::Top,
            (StringConst::Constant(s1), StringConst::Constant(s2)) => {
                if s1 == s2 {
                    StringConst::Constant(s1.clone())
                } else {
                    StringConst::Top
                }
            }
        }
    }

    fn meet(&self, elem1: &Self::Element, elem2: &Self::Element) -> Self::Element {
        match (elem1, elem2) {
            (StringConst::Bottom, _) | (_, StringConst::Bottom) => StringConst::Bottom,
            (StringConst::Top, e) | (e, StringConst::Top) => e.clone(),
            (StringConst::Constant(s1), StringConst::Constant(s2)) => {
                if s1 == s2 {
                    StringConst::Constant(s1.clone())
                } else {
                    StringConst::Bottom
                }
            }
        }
    }

    fn widen(&self, elem1: &Self::Element, elem2: &Self::Element) -> Self::Element {
        // For flat lattice, widening is same as join
        self.join(elem1, elem2)
    }
}

/// String Length Domain.
///
/// Abstracts strings by their length using the Interval Domain.
/// Maps string variables to intervals representing their possible lengths.
#[derive(Clone, Debug)]
pub struct StringLengthDomain {
    interval_domain: IntervalDomain,
}

impl StringLengthDomain {
    pub fn new() -> Self {
        Self {
            interval_domain: IntervalDomain,
        }
    }

    /// Get the length interval for a variable.
    pub fn get_length(&self, elem: &IntervalElement, var: &str) -> Interval {
        elem.get(var)
    }

    /// Assign a string constant: s = "abc" => len(s) = 3
    pub fn assign_const(&self, elem: &IntervalElement, var: &str, value: &str) -> IntervalElement {
        let len = value.len() as i64;
        self.interval_domain.assign(elem, &var.to_string(), &NumExpr::Const(len))
    }

    /// Assign concatenation: s = s1 + s2 => len(s) = len(s1) + len(s2)
    pub fn assign_concat(&self, elem: &IntervalElement, var: &str, s1: &str, s2: &str) -> IntervalElement {
        let expr = NumExpr::Add(Box::new(NumExpr::Var(s1.to_string())), Box::new(NumExpr::Var(s2.to_string())));
        self.interval_domain.assign(elem, &var.to_string(), &expr)
    }

    /// Assume a constraint on the length of a string variable.
    pub fn assume_length(&self, elem: &IntervalElement, pred: &NumPred<String, i64>) -> IntervalElement {
        self.interval_domain.assume(elem, pred)
    }
}

impl Default for StringLengthDomain {
    fn default() -> Self {
        Self::new()
    }
}

impl AbstractDomain for StringLengthDomain {
    type Element = IntervalElement;

    fn bottom(&self) -> Self::Element {
        self.interval_domain.bottom()
    }

    fn top(&self) -> Self::Element {
        self.interval_domain.top()
    }

    fn is_bottom(&self, elem: &Self::Element) -> bool {
        self.interval_domain.is_bottom(elem)
    }

    fn is_top(&self, elem: &Self::Element) -> bool {
        self.interval_domain.is_top(elem)
    }

    fn le(&self, elem1: &Self::Element, elem2: &Self::Element) -> bool {
        self.interval_domain.le(elem1, elem2)
    }

    fn join(&self, elem1: &Self::Element, elem2: &Self::Element) -> Self::Element {
        self.interval_domain.join(elem1, elem2)
    }

    fn meet(&self, elem1: &Self::Element, elem2: &Self::Element) -> Self::Element {
        self.interval_domain.meet(elem1, elem2)
    }

    fn widen(&self, elem1: &Self::Element, elem2: &Self::Element) -> Self::Element {
        self.interval_domain.widen(elem1, elem2)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::domain::tests::test_lattice_axioms;

    #[test]
    fn test_string_constant_lattice() {
        let domain = StringConstantDomain;
        let samples = vec![
            StringConst::Bottom,
            StringConst::Top,
            StringConst::Constant("hello".to_string()),
            StringConst::Constant("world".to_string()),
        ];
        test_lattice_axioms(&domain, &samples);
    }

    #[test]
    fn test_string_constant_ops() {
        let domain = StringConstantDomain;
        let s1 = StringConst::Constant("foo".to_string());
        let s2 = StringConst::Constant("foo".to_string());
        let s3 = StringConst::Constant("bar".to_string());

        assert!(domain.le(&s1, &s2));
        assert!(!domain.le(&s1, &s3));
        assert_eq!(domain.join(&s1, &s3), StringConst::Top);
        assert_eq!(domain.meet(&s1, &s3), StringConst::Bottom);
    }

    #[test]
    fn test_string_length_domain() {
        let domain = StringLengthDomain::new();
        let mut state = domain.top();

        // s1 = "hello" (len 5)
        state = domain.assign_const(&state, "s1", "hello");
        let len_s1 = domain.get_length(&state, "s1");
        assert_eq!(len_s1, Interval::constant(5));

        // s2 = "world" (len 5)
        state = domain.assign_const(&state, "s2", "world");

        // s3 = s1 + s2 (len 10)
        state = domain.assign_concat(&state, "s3", "s1", "s2");
        let len_s3 = domain.get_length(&state, "s3");
        assert_eq!(len_s3, Interval::constant(10));
    }
}
