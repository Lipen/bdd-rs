//! Interval abstract domain implementation.
//!
//! The interval domain tracks lower and upper bounds for numeric variables.
//! It's simple, efficient, but loses relational information between variables.

use std::cmp::{max, min};
use std::collections::HashMap;
use std::fmt;

use super::domain::AbstractDomain;
use super::expr::{NumExpr, NumPred};
use super::numeric::NumericDomain;

/// Bound of an interval: -∞, finite value, or +∞.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Bound {
    NegInf,
    Finite(i64),
    PosInf,
}

impl Bound {
    pub fn as_finite(&self) -> Option<i64> {
        match self {
            Bound::Finite(n) => Some(*n),
            _ => None,
        }
    }

    pub fn add(&self, other: &Bound) -> Bound {
        match (self, other) {
            (Bound::Finite(a), Bound::Finite(b)) => Bound::Finite(a.saturating_add(*b)),
            (Bound::NegInf, Bound::PosInf) | (Bound::PosInf, Bound::NegInf) => {
                // Undefined: use top
                Bound::PosInf
            }
            (Bound::NegInf, _) | (_, Bound::NegInf) => Bound::NegInf,
            (Bound::PosInf, _) | (_, Bound::PosInf) => Bound::PosInf,
        }
    }

    pub fn sub(&self, other: &Bound) -> Bound {
        match (self, other) {
            (Bound::Finite(a), Bound::Finite(b)) => Bound::Finite(a.saturating_sub(*b)),
            (Bound::PosInf, Bound::NegInf) => Bound::PosInf,
            (Bound::NegInf, Bound::PosInf) => Bound::NegInf,
            (Bound::PosInf, _) => Bound::PosInf,
            (Bound::NegInf, _) => Bound::NegInf,
            (_, Bound::PosInf) => Bound::NegInf,
            (_, Bound::NegInf) => Bound::PosInf,
        }
    }

    pub fn mul(&self, other: &Bound) -> Bound {
        match (self, other) {
            (Bound::Finite(a), Bound::Finite(b)) => Bound::Finite(a.saturating_mul(*b)),
            (Bound::Finite(0), _) | (_, Bound::Finite(0)) => Bound::Finite(0),
            (Bound::NegInf, Bound::PosInf) | (Bound::PosInf, Bound::NegInf) => Bound::NegInf,
            (Bound::NegInf, Bound::NegInf) | (Bound::PosInf, Bound::PosInf) => Bound::PosInf,
            _ => Bound::PosInf, // Simplified
        }
    }

    pub fn neg(&self) -> Bound {
        match self {
            Bound::NegInf => Bound::PosInf,
            Bound::Finite(n) => Bound::Finite(-n),
            Bound::PosInf => Bound::NegInf,
        }
    }
}

impl fmt::Display for Bound {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Bound::NegInf => write!(f, "-∞"),
            Bound::Finite(n) => write!(f, "{}", n),
            Bound::PosInf => write!(f, "+∞"),
        }
    }
}

/// Interval: [low, high].
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Interval {
    pub low: Bound,
    pub high: Bound,
}

impl Interval {
    pub fn new(low: Bound, high: Bound) -> Self {
        if low > high {
            // Empty interval
            Self {
                low: Bound::PosInf,
                high: Bound::NegInf,
            }
        } else {
            Self { low, high }
        }
    }

    pub fn constant(value: i64) -> Self {
        Self {
            low: Bound::Finite(value),
            high: Bound::Finite(value),
        }
    }

    pub fn top() -> Self {
        Self {
            low: Bound::NegInf,
            high: Bound::PosInf,
        }
    }

    pub fn bottom() -> Self {
        Self {
            low: Bound::PosInf,
            high: Bound::NegInf,
        }
    }

    pub fn is_empty(&self) -> bool {
        self.low > self.high
    }

    pub fn contains(&self, value: i64) -> bool {
        match (self.low, self.high) {
            (Bound::Finite(l), Bound::Finite(h)) => l <= value && value <= h,
            (Bound::NegInf, Bound::Finite(h)) => value <= h,
            (Bound::Finite(l), Bound::PosInf) => l <= value,
            (Bound::NegInf, Bound::PosInf) => true,
            _ => false,
        }
    }

    pub fn join(&self, other: &Interval) -> Interval {
        if self.is_empty() {
            return *other;
        }
        if other.is_empty() {
            return *self;
        }
        Interval {
            low: min(self.low, other.low),
            high: max(self.high, other.high),
        }
    }

    pub fn meet(&self, other: &Interval) -> Interval {
        Interval::new(max(self.low, other.low), min(self.high, other.high))
    }

    pub fn widen(&self, other: &Interval) -> Interval {
        let low = if other.low < self.low { Bound::NegInf } else { self.low };
        let high = if other.high > self.high { Bound::PosInf } else { self.high };
        Interval { low, high }
    }
}

impl fmt::Display for Interval {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "[{}, {}]", self.low, self.high)
    }
}

/// Interval domain: maps variables to intervals.
#[derive(Debug, Clone)]
pub struct IntervalDomain;

/// Abstract element: mapping from variables to intervals.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct IntervalElement {
    pub intervals: HashMap<String, Interval>,
    pub is_bottom: bool,
}

impl IntervalElement {
    pub fn new() -> Self {
        Self {
            intervals: HashMap::new(),
            is_bottom: false,
        }
    }

    pub fn bottom() -> Self {
        Self {
            intervals: HashMap::new(),
            is_bottom: true,
        }
    }

    pub fn top() -> Self {
        Self::new()
    }

    pub fn get(&self, var: &str) -> Interval {
        if self.is_bottom {
            return Interval::bottom();
        }
        self.intervals.get(var).copied().unwrap_or(Interval::top())
    }

    pub fn set(&mut self, var: String, interval: Interval) {
        if interval.is_empty() {
            self.is_bottom = true;
        } else {
            self.intervals.insert(var, interval);
        }
    }
}

impl Default for IntervalElement {
    fn default() -> Self {
        Self::new()
    }
}

impl AbstractDomain for IntervalDomain {
    type Element = IntervalElement;

    fn bottom(&self) -> Self::Element {
        IntervalElement::bottom()
    }

    fn top(&self) -> Self::Element {
        IntervalElement::top()
    }

    fn is_bottom(&self, elem: &Self::Element) -> bool {
        elem.is_bottom
    }

    fn is_top(&self, _elem: &Self::Element) -> bool {
        // Element is top if all variables have infinite intervals
        // For simplicity, we don't track this precisely
        false
    }

    fn le(&self, elem1: &Self::Element, elem2: &Self::Element) -> bool {
        if elem1.is_bottom {
            return true;
        }
        if elem2.is_bottom {
            return false;
        }

        // elem1 ⊑ elem2 if all intervals in elem1 are contained in elem2
        for (var, i1) in &elem1.intervals {
            let i2 = elem2.get(var);
            if i1.low < i2.low || i1.high > i2.high {
                return false;
            }
        }
        true
    }

    fn join(&self, elem1: &Self::Element, elem2: &Self::Element) -> Self::Element {
        if elem1.is_bottom {
            return elem2.clone();
        }
        if elem2.is_bottom {
            return elem1.clone();
        }

        let mut result = IntervalElement::new();
        let mut all_vars: std::collections::HashSet<_> = elem1.intervals.keys().collect();
        all_vars.extend(elem2.intervals.keys());

        for var in all_vars {
            let i1 = elem1.get(var);
            let i2 = elem2.get(var);
            result.set(var.clone(), i1.join(&i2));
        }

        result
    }

    fn meet(&self, elem1: &Self::Element, elem2: &Self::Element) -> Self::Element {
        if elem1.is_bottom || elem2.is_bottom {
            return IntervalElement::bottom();
        }

        let mut result = IntervalElement::new();
        let mut all_vars: std::collections::HashSet<_> = elem1.intervals.keys().collect();
        all_vars.extend(elem2.intervals.keys());

        for var in all_vars {
            let i1 = elem1.get(var);
            let i2 = elem2.get(var);
            let met = i1.meet(&i2);
            if met.is_empty() {
                return IntervalElement::bottom();
            }
            result.set(var.clone(), met);
        }

        result
    }

    fn widen(&self, elem1: &Self::Element, elem2: &Self::Element) -> Self::Element {
        if elem1.is_bottom {
            return elem2.clone();
        }
        if elem2.is_bottom {
            return elem1.clone();
        }

        let mut result = IntervalElement::new();
        let mut all_vars: std::collections::HashSet<_> = elem1.intervals.keys().collect();
        all_vars.extend(elem2.intervals.keys());

        for var in all_vars {
            let i1 = elem1.get(var);
            let i2 = elem2.get(var);
            result.set(var.clone(), i1.widen(&i2));
        }

        result
    }
}

impl NumericDomain for IntervalDomain {
    type Var = String;
    type Value = i64;

    fn constant(&self, var: &Self::Var, value: Self::Value) -> Self::Element {
        let mut elem = IntervalElement::new();
        elem.set(var.clone(), Interval::constant(value));
        elem
    }

    fn interval(&self, var: &Self::Var, low: Self::Value, high: Self::Value) -> Self::Element {
        let mut elem = IntervalElement::new();
        elem.set(var.clone(), Interval::new(Bound::Finite(low), Bound::Finite(high)));
        elem
    }

    fn assign(&self, elem: &Self::Element, var: &Self::Var, expr: &NumExpr<Self::Var, Self::Value>) -> Self::Element {
        if elem.is_bottom {
            return elem.clone();
        }

        let mut result = elem.clone();
        let interval = self.eval_expr(elem, expr);
        result.set(var.clone(), interval);
        result
    }

    fn assume(&self, elem: &Self::Element, pred: &NumPred<Self::Var, Self::Value>) -> Self::Element {
        if elem.is_bottom {
            return elem.clone();
        }

        // Simplified: only handle basic cases
        match pred {
            NumPred::True => elem.clone(),
            NumPred::False => IntervalElement::bottom(),
            NumPred::Lt(NumExpr::Var(v), NumExpr::Const(c)) => {
                let mut result = elem.clone();
                let current = elem.get(v);
                let refined = current.meet(&Interval::new(Bound::NegInf, Bound::Finite(c - 1)));
                result.set(v.clone(), refined);
                result
            }
            NumPred::Le(NumExpr::Var(v), NumExpr::Const(c)) => {
                let mut result = elem.clone();
                let current = elem.get(v);
                let refined = current.meet(&Interval::new(Bound::NegInf, Bound::Finite(*c)));
                result.set(v.clone(), refined);
                result
            }
            NumPred::Gt(NumExpr::Var(v), NumExpr::Const(c)) => {
                let mut result = elem.clone();
                let current = elem.get(v);
                let refined = current.meet(&Interval::new(Bound::Finite(c + 1), Bound::PosInf));
                result.set(v.clone(), refined);
                result
            }
            NumPred::Ge(NumExpr::Var(v), NumExpr::Const(c)) => {
                let mut result = elem.clone();
                let current = elem.get(v);
                let refined = current.meet(&Interval::new(Bound::Finite(*c), Bound::PosInf));
                result.set(v.clone(), refined);
                result
            }
            NumPred::And(p1, p2) => {
                let e1 = self.assume(elem, p1);
                self.assume(&e1, p2)
            }
            NumPred::Or(p1, p2) => {
                let e1 = self.assume(elem, p1);
                let e2 = self.assume(elem, p2);
                self.join(&e1, &e2)
            }
            NumPred::Not(p) => {
                // Negate the inner predicate
                match p.as_ref() {
                    NumPred::True => IntervalElement::bottom(),
                    NumPred::False => elem.clone(),
                    NumPred::Lt(e1, e2) => self.assume(elem, &NumPred::Ge(e1.clone(), e2.clone())),
                    NumPred::Le(e1, e2) => self.assume(elem, &NumPred::Gt(e1.clone(), e2.clone())),
                    NumPred::Gt(e1, e2) => self.assume(elem, &NumPred::Le(e1.clone(), e2.clone())),
                    NumPred::Ge(e1, e2) => self.assume(elem, &NumPred::Lt(e1.clone(), e2.clone())),
                    NumPred::Eq(e1, e2) => self.assume(elem, &NumPred::Neq(e1.clone(), e2.clone())),
                    NumPred::Neq(e1, e2) => self.assume(elem, &NumPred::Eq(e1.clone(), e2.clone())),
                    NumPred::Not(inner) => self.assume(elem, inner),
                    NumPred::And(p1, p2) => {
                        // ¬(p1 ∧ p2) = ¬p1 ∨ ¬p2 (De Morgan)
                        self.assume(
                            elem,
                            &NumPred::Or(Box::new(NumPred::Not(p1.clone())), Box::new(NumPred::Not(p2.clone()))),
                        )
                    }
                    NumPred::Or(p1, p2) => {
                        // ¬(p1 ∨ p2) = ¬p1 ∧ ¬p2 (De Morgan)
                        self.assume(
                            elem,
                            &NumPred::And(Box::new(NumPred::Not(p1.clone())), Box::new(NumPred::Not(p2.clone()))),
                        )
                    }
                }
            }
            _ => elem.clone(), // Other cases: keep as-is
        }
    }

    fn project(&self, elem: &Self::Element, var: &Self::Var) -> Self::Element {
        let mut result = elem.clone();
        result.intervals.remove(var);
        result
    }

    fn get_constant(&self, elem: &Self::Element, var: &Self::Var) -> Option<Self::Value> {
        let interval = elem.get(var);
        match (interval.low, interval.high) {
            (Bound::Finite(l), Bound::Finite(h)) if l == h => Some(l),
            _ => None,
        }
    }

    fn get_bounds(&self, elem: &Self::Element, var: &Self::Var) -> Option<(Self::Value, Self::Value)> {
        let interval = elem.get(var);
        match (interval.low, interval.high) {
            (Bound::Finite(l), Bound::Finite(h)) => Some((l, h)),
            _ => None,
        }
    }
}

impl IntervalDomain {
    fn eval_expr(&self, elem: &IntervalElement, expr: &NumExpr<String, i64>) -> Interval {
        match expr {
            NumExpr::Const(c) => Interval::constant(*c),
            NumExpr::Var(v) => elem.get(v),
            NumExpr::Add(e1, e2) => {
                let i1 = self.eval_expr(elem, e1);
                let i2 = self.eval_expr(elem, e2);
                Interval::new(i1.low.add(&i2.low), i1.high.add(&i2.high))
            }
            NumExpr::Sub(e1, e2) => {
                let i1 = self.eval_expr(elem, e1);
                let i2 = self.eval_expr(elem, e2);
                Interval::new(i1.low.sub(&i2.high), i1.high.sub(&i2.low))
            }
            NumExpr::Mul(e1, e2) => {
                let i1 = self.eval_expr(elem, e1);
                let i2 = self.eval_expr(elem, e2);
                // Simplified: compute all four corners
                let corners = [
                    i1.low.mul(&i2.low),
                    i1.low.mul(&i2.high),
                    i1.high.mul(&i2.low),
                    i1.high.mul(&i2.high),
                ];
                let low = corners.iter().min().copied().unwrap_or(Bound::NegInf);
                let high = corners.iter().max().copied().unwrap_or(Bound::PosInf);
                Interval::new(low, high)
            }
            NumExpr::Neg(e) => {
                let i = self.eval_expr(elem, e);
                Interval::new(i.high.neg(), i.low.neg())
            }
            _ => Interval::top(), // Div, Mod: simplified
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_interval_operations() {
        let i1 = Interval::new(Bound::Finite(0), Bound::Finite(10));
        let i2 = Interval::new(Bound::Finite(5), Bound::Finite(15));

        let joined = i1.join(&i2);
        assert_eq!(joined, Interval::new(Bound::Finite(0), Bound::Finite(15)));

        let met = i1.meet(&i2);
        assert_eq!(met, Interval::new(Bound::Finite(5), Bound::Finite(10)));

        let widened = i1.widen(&i2);
        assert_eq!(widened, Interval::new(Bound::Finite(0), Bound::PosInf));
    }

    #[test]
    fn test_interval_domain() {
        let domain = IntervalDomain;

        let e1 = domain.constant(&"x".to_string(), 5);
        assert_eq!(e1.get("x"), Interval::constant(5));

        let e2 = domain.interval(&"x".to_string(), 0, 10);
        let joined = domain.join(&e1, &e2);
        assert_eq!(joined.get("x"), Interval::new(Bound::Finite(0), Bound::Finite(10)));
    }

    #[test]
    fn test_interval_lattice_axioms() {
        use crate::domain::tests::test_lattice_axioms;

        let domain = IntervalDomain;

        // Create sample elements for testing
        let samples = vec![
            domain.bottom(),
            domain.top(),
            domain.constant(&"x".to_string(), 0),
            domain.constant(&"x".to_string(), 5),
            domain.interval(&"x".to_string(), 0, 10),
            domain.interval(&"x".to_string(), -5, 5),
            domain.interval(&"x".to_string(), 10, 20),
        ];

        // Validate all lattice axioms
        test_lattice_axioms(&domain, &samples);
    }
}
