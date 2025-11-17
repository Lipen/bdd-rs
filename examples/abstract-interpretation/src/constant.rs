//! Constant propagation abstract domain implementation.
//!
//! The constant domain tracks exact constant values when known, representing
//! unknowns as Top. It's one of the simplest and most effective abstract domains
//! for optimization and dead code detection.
//!
//! # Elements
//!
//! The lattice has three kinds of elements:
//! - ⊥ (Bottom): impossible/unreachable
//! - Const(n): exactly the constant value n
//! - ⊤ (Top): unknown/non-constant
//!
//! # Lattice Structure
//!
//! ```text
//!           ⊤ (Top - Unknown)
//!          / | \
//!    ... Const(n) ... (All possible constant values)
//!          \ | /
//!           ⊥ (Bottom)
//! ```
//!
//! # Properties
//!
//! - **Precision**: Exact for constants, loses all information otherwise
//! - **Operations**: Arithmetic folds constants, produces Top on overflow or mixed operations
//! - **Use Cases**: Constant folding, dead code detection, conditional simplification
//!
//! # Examples
//!
//! ```
//! use abstract_interpretation::constant::{ConstValue, ConstantDomain, ConstantElement};
//! use abstract_interpretation::domain::AbstractDomain;
//!
//! let domain = ConstantDomain;
//! let mut elem = ConstantElement::new();
//! elem.set("x".to_string(), ConstValue::Const(5));
//! elem.set("y".to_string(), ConstValue::Const(3));
//!
//! // x + y evaluates to constant 8
//! let sum = ConstValue::Const(5).add(ConstValue::Const(3));
//! assert_eq!(sum, ConstValue::Const(8));
//! ```

use std::collections::HashMap;
use std::fmt;

use super::domain::AbstractDomain;
use super::expr::{NumExpr, NumPred};
use super::numeric::NumericDomain;

/// Constant value in the lattice.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum ConstValue {
    /// Bottom: impossible/unreachable
    Bottom,
    /// Known constant value
    Const(i64),
    /// Top: unknown/non-constant
    Top,
}

impl ConstValue {
    /// Addition on constant values.
    pub fn add(self, other: ConstValue) -> ConstValue {
        match (self, other) {
            (ConstValue::Bottom, _) | (_, ConstValue::Bottom) => ConstValue::Bottom,
            (ConstValue::Top, _) | (_, ConstValue::Top) => ConstValue::Top,
            (ConstValue::Const(a), ConstValue::Const(b)) => {
                // Check for overflow
                match a.checked_add(b) {
                    Some(sum) => ConstValue::Const(sum),
                    None => ConstValue::Top, // Overflow → Top
                }
            }
        }
    }

    /// Subtraction on constant values.
    pub fn sub(self, other: ConstValue) -> ConstValue {
        match (self, other) {
            (ConstValue::Bottom, _) | (_, ConstValue::Bottom) => ConstValue::Bottom,
            (ConstValue::Top, _) | (_, ConstValue::Top) => ConstValue::Top,
            (ConstValue::Const(a), ConstValue::Const(b)) => match a.checked_sub(b) {
                Some(diff) => ConstValue::Const(diff),
                None => ConstValue::Top,
            },
        }
    }

    /// Multiplication on constant values.
    pub fn mul(self, other: ConstValue) -> ConstValue {
        match (self, other) {
            (ConstValue::Bottom, _) | (_, ConstValue::Bottom) => ConstValue::Bottom,
            (ConstValue::Top, _) | (_, ConstValue::Top) => ConstValue::Top,
            (ConstValue::Const(a), ConstValue::Const(b)) => match a.checked_mul(b) {
                Some(prod) => ConstValue::Const(prod),
                None => ConstValue::Top,
            },
        }
    }

    /// Division on constant values.
    pub fn div(self, other: ConstValue) -> ConstValue {
        match (self, other) {
            (ConstValue::Bottom, _) | (_, ConstValue::Bottom) => ConstValue::Bottom,
            (ConstValue::Top, _) | (_, ConstValue::Top) => ConstValue::Top,
            (_, ConstValue::Const(0)) => ConstValue::Top, // Division by zero
            (ConstValue::Const(a), ConstValue::Const(b)) => match a.checked_div(b) {
                Some(quot) => ConstValue::Const(quot),
                None => ConstValue::Top,
            },
        }
    }

    /// Modulo on constant values.
    pub fn modulo(self, other: ConstValue) -> ConstValue {
        match (self, other) {
            (ConstValue::Bottom, _) | (_, ConstValue::Bottom) => ConstValue::Bottom,
            (ConstValue::Top, _) | (_, ConstValue::Top) => ConstValue::Top,
            (_, ConstValue::Const(0)) => ConstValue::Top, // Modulo by zero
            (ConstValue::Const(a), ConstValue::Const(b)) => match a.checked_rem(b) {
                Some(rem) => ConstValue::Const(rem),
                None => ConstValue::Top,
            },
        }
    }

    /// Negation on constant values.
    pub fn neg(self) -> ConstValue {
        match self {
            ConstValue::Bottom => ConstValue::Bottom,
            ConstValue::Const(n) => match n.checked_neg() {
                Some(neg) => ConstValue::Const(neg),
                None => ConstValue::Top,
            },
            ConstValue::Top => ConstValue::Top,
        }
    }
}

impl fmt::Display for ConstValue {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ConstValue::Bottom => write!(f, "⊥"),
            ConstValue::Const(n) => write!(f, "{}", n),
            ConstValue::Top => write!(f, "⊤"),
        }
    }
}

/// Constant propagation domain for abstract interpretation.
#[derive(Debug, Clone)]
pub struct ConstantDomain;

/// Abstract element in the constant domain (maps variables to constant values).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ConstantElement {
    /// Mapping from variables to their constant value abstractions
    pub values: HashMap<String, ConstValue>,
    /// Whether this element is bottom (unreachable)
    pub is_bottom: bool,
}

impl ConstantElement {
    /// Create a new empty constant element.
    pub fn new() -> Self {
        Self {
            values: HashMap::new(),
            is_bottom: false,
        }
    }

    /// Create a bottom element.
    pub fn bottom() -> Self {
        Self {
            values: HashMap::new(),
            is_bottom: true,
        }
    }

    /// Get the constant value of a variable (returns Top if not defined).
    pub fn get(&self, var: &str) -> ConstValue {
        if self.is_bottom {
            return ConstValue::Bottom;
        }
        self.values.get(var).copied().unwrap_or(ConstValue::Top)
    }

    /// Set the constant value of a variable.
    pub fn set(&mut self, var: String, value: ConstValue) {
        if value == ConstValue::Bottom {
            self.is_bottom = true;
        } else {
            self.values.insert(var, value);
        }
    }
}

impl Default for ConstantElement {
    fn default() -> Self {
        Self::new()
    }
}

impl AbstractDomain for ConstantDomain {
    type Element = ConstantElement;

    fn bottom(&self) -> Self::Element {
        ConstantElement::bottom()
    }

    fn top(&self) -> Self::Element {
        ConstantElement::new()
    }

    fn is_bottom(&self, elem: &Self::Element) -> bool {
        elem.is_bottom
    }

    fn is_top(&self, _elem: &Self::Element) -> bool {
        // Element is top if all defined variables have Top value
        false
    }

    fn le(&self, elem1: &Self::Element, elem2: &Self::Element) -> bool {
        if elem1.is_bottom {
            return true;
        }
        if elem2.is_bottom {
            return false;
        }

        // elem1 ⊑ elem2 if:
        // - For each var in elem1, either it's not in elem2 (elem2[var] = Top)
        //   or elem1[var] ⊑ elem2[var]
        for (var, &v1) in &elem1.values {
            let v2 = elem2.get(var);
            if !Self::const_le(v1, v2) {
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

        let mut result = ConstantElement::new();

        // Collect all variables
        let mut vars: std::collections::HashSet<&String> = elem1.values.keys().collect();
        vars.extend(elem2.values.keys());

        for var in vars {
            let v1 = elem1.get(var);
            let v2 = elem2.get(var);
            let joined = Self::const_join(v1, v2);
            if joined != ConstValue::Top {
                result.set(var.clone(), joined);
            }
        }

        result
    }

    fn meet(&self, elem1: &Self::Element, elem2: &Self::Element) -> Self::Element {
        if elem1.is_bottom || elem2.is_bottom {
            return self.bottom();
        }

        let mut result = ConstantElement::new();

        // Collect all variables
        let mut vars: std::collections::HashSet<&String> = elem1.values.keys().collect();
        vars.extend(elem2.values.keys());

        for var in vars {
            let v1 = elem1.get(var);
            let v2 = elem2.get(var);
            let met = Self::const_meet(v1, v2);
            if met == ConstValue::Bottom {
                return self.bottom();
            }
            if met != ConstValue::Top {
                result.set(var.clone(), met);
            }
        }

        result
    }

    fn widen(&self, elem1: &Self::Element, elem2: &Self::Element) -> Self::Element {
        // For flat lattice (finite height), widen = join
        self.join(elem1, elem2)
    }

    fn narrow(&self, elem1: &Self::Element, elem2: &Self::Element) -> Self::Element {
        // For flat lattice (finite height), narrow = meet
        self.meet(elem1, elem2)
    }
}

impl ConstantDomain {
    /// Partial order on constant values.
    fn const_le(c1: ConstValue, c2: ConstValue) -> bool {
        match (c1, c2) {
            (ConstValue::Bottom, _) => true,
            (_, ConstValue::Top) => true,
            (ConstValue::Const(a), ConstValue::Const(b)) => a == b,
            _ => false,
        }
    }

    /// Join (LUB) on constant values.
    fn const_join(c1: ConstValue, c2: ConstValue) -> ConstValue {
        match (c1, c2) {
            (ConstValue::Bottom, c) | (c, ConstValue::Bottom) => c,
            (ConstValue::Top, _) | (_, ConstValue::Top) => ConstValue::Top,
            (ConstValue::Const(a), ConstValue::Const(b)) => {
                if a == b {
                    ConstValue::Const(a)
                } else {
                    ConstValue::Top
                }
            }
        }
    }

    /// Meet (GLB) on constant values.
    fn const_meet(c1: ConstValue, c2: ConstValue) -> ConstValue {
        match (c1, c2) {
            (ConstValue::Bottom, _) | (_, ConstValue::Bottom) => ConstValue::Bottom,
            (ConstValue::Top, c) | (c, ConstValue::Top) => c,
            (ConstValue::Const(a), ConstValue::Const(b)) => {
                if a == b {
                    ConstValue::Const(a)
                } else {
                    ConstValue::Bottom // Inconsistent
                }
            }
        }
    }
}

impl NumericDomain for ConstantDomain {
    type Var = String;
    type Value = i64;

    fn constant(&self, var: &Self::Var, value: Self::Value) -> Self::Element {
        let mut elem = ConstantElement::new();
        elem.set(var.clone(), ConstValue::Const(value));
        elem
    }

    fn interval(&self, var: &Self::Var, low: Self::Value, high: Self::Value) -> Self::Element {
        let mut elem = ConstantElement::new();
        if low == high {
            elem.set(var.clone(), ConstValue::Const(low));
        } else {
            // Not a singleton interval → Top
            elem.set(var.clone(), ConstValue::Top);
        }
        elem
    }

    fn assign(&self, elem: &Self::Element, var: &Self::Var, expr: &NumExpr<Self::Var, Self::Value>) -> Self::Element {
        if elem.is_bottom {
            return elem.clone();
        }

        let value = self.eval_expr(elem, expr);
        let mut result = elem.clone();
        result.set(var.clone(), value);
        result
    }

    fn assume(&self, elem: &Self::Element, pred: &NumPred<Self::Var, Self::Value>) -> Self::Element {
        if elem.is_bottom {
            return elem.clone();
        }

        match pred {
            NumPred::Eq(NumExpr::Var(v), NumExpr::Const(n)) | NumPred::Eq(NumExpr::Const(n), NumExpr::Var(v)) => {
                let current = elem.get(v);
                match current {
                    ConstValue::Const(c) if c != *n => return self.bottom(),
                    ConstValue::Bottom => return self.bottom(),
                    _ => {
                        let mut result = elem.clone();
                        result.set(v.clone(), ConstValue::Const(*n));
                        result
                    }
                }
            }

            NumPred::Neq(NumExpr::Var(v), NumExpr::Const(n)) | NumPred::Neq(NumExpr::Const(n), NumExpr::Var(v)) => {
                let current = elem.get(v);
                match current {
                    ConstValue::Const(c) if c == *n => return self.bottom(),
                    ConstValue::Const(_) => elem.clone(), // Different constant
                    _ => {
                        // Was Top, now we know it's not n, but still Top (infinite values)
                        elem.clone()
                    }
                }
            }

            // For inequalities, constant domain can't refine much
            NumPred::Lt(NumExpr::Var(v), NumExpr::Const(_n))
            | NumPred::Le(NumExpr::Var(v), NumExpr::Const(_n))
            | NumPred::Gt(NumExpr::Var(v), NumExpr::Const(_n))
            | NumPred::Ge(NumExpr::Var(v), NumExpr::Const(_n)) => {
                let current = elem.get(v);
                if let ConstValue::Const(c) = current {
                    // Check if the predicate is satisfied
                    let satisfied = match pred {
                        NumPred::Lt(_, NumExpr::Const(n)) => c < *n,
                        NumPred::Le(_, NumExpr::Const(n)) => c <= *n,
                        NumPred::Gt(_, NumExpr::Const(n)) => c > *n,
                        NumPred::Ge(_, NumExpr::Const(n)) => c >= *n,
                        _ => unreachable!(),
                    };
                    if satisfied {
                        elem.clone()
                    } else {
                        self.bottom()
                    }
                } else {
                    elem.clone() // Top remains Top
                }
            }

            _ => elem.clone(), // Unsupported predicates
        }
    }

    fn project(&self, elem: &Self::Element, var: &Self::Var) -> Self::Element {
        if elem.is_bottom {
            return elem.clone();
        }
        let mut result = elem.clone();
        result.values.remove(var);
        result
    }

    fn get_constant(&self, elem: &Self::Element, var: &Self::Var) -> Option<Self::Value> {
        if elem.is_bottom {
            return None;
        }
        match elem.get(var) {
            ConstValue::Const(n) => Some(n),
            _ => None,
        }
    }

    fn get_bounds(&self, elem: &Self::Element, var: &Self::Var) -> Option<(Self::Value, Self::Value)> {
        if elem.is_bottom {
            return None;
        }
        match elem.get(var) {
            ConstValue::Const(n) => Some((n, n)),
            ConstValue::Top => Some((i64::MIN, i64::MAX)),
            ConstValue::Bottom => None,
        }
    }
}

impl ConstantDomain {
    /// Evaluate a numeric expression to a constant value.
    fn eval_expr(&self, elem: &ConstantElement, expr: &NumExpr<String, i64>) -> ConstValue {
        match expr {
            NumExpr::Var(v) => elem.get(v),
            NumExpr::Const(n) => ConstValue::Const(*n),
            NumExpr::Add(e1, e2) => {
                let v1 = self.eval_expr(elem, e1);
                let v2 = self.eval_expr(elem, e2);
                v1.add(v2)
            }
            NumExpr::Sub(e1, e2) => {
                let v1 = self.eval_expr(elem, e1);
                let v2 = self.eval_expr(elem, e2);
                v1.sub(v2)
            }
            NumExpr::Mul(e1, e2) => {
                let v1 = self.eval_expr(elem, e1);
                let v2 = self.eval_expr(elem, e2);
                v1.mul(v2)
            }
            NumExpr::Div(e1, e2) => {
                let v1 = self.eval_expr(elem, e1);
                let v2 = self.eval_expr(elem, e2);
                v1.div(v2)
            }
            NumExpr::Mod(e1, e2) => {
                let v1 = self.eval_expr(elem, e1);
                let v2 = self.eval_expr(elem, e2);
                v1.modulo(v2)
            }
            NumExpr::Neg(e) => {
                let v = self.eval_expr(elem, e);
                v.neg()
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_const_constant_folding() {
        // Based on constant_propagation.rs Example 1
        let domain = ConstantDomain;

        let mut elem = ConstantElement::new();
        elem.set("x".to_string(), ConstValue::Const(5));
        elem.set("y".to_string(), ConstValue::Const(3));

        // z = x + y = 8
        let expr = NumExpr::Add(
            Box::new(NumExpr::Var("x".to_string())),
            Box::new(NumExpr::Var("y".to_string())),
        );
        elem = domain.assign(&elem, &"z".to_string(), &expr);
        assert_eq!(elem.get("z"), ConstValue::Const(8));

        // w = z * 2 = 16
        let expr = NumExpr::Mul(
            Box::new(NumExpr::Var("z".to_string())),
            Box::new(NumExpr::Const(2)),
        );
        elem = domain.assign(&elem, &"w".to_string(), &expr);
        assert_eq!(elem.get("w"), ConstValue::Const(16));

        // result = w - 4 = 12
        let expr = NumExpr::Sub(
            Box::new(NumExpr::Var("w".to_string())),
            Box::new(NumExpr::Const(4)),
        );
        elem = domain.assign(&elem, &"result".to_string(), &expr);
        assert_eq!(elem.get("result"), ConstValue::Const(12));
    }

    #[test]
    fn test_const_dead_code_detection() {
        // Based on constant_propagation.rs Example 2
        let domain = ConstantDomain;

        let mut elem = ConstantElement::new();
        elem.set("x".to_string(), ConstValue::Const(5));

        // Check if x > 10 is possible
        let pred = NumPred::Gt(NumExpr::Var("x".to_string()), NumExpr::Const(10));
        let refined = domain.assume(&elem, &pred);

        // Should be bottom (contradiction)
        assert!(refined.is_bottom);
    }

    #[test]
    fn test_const_conditional_simplification() {
        // Based on constant_propagation.rs Example 3
        let domain = ConstantDomain;

        let mut elem = ConstantElement::new();
        elem.set("DEBUG".to_string(), ConstValue::Const(0));

        // if (DEBUG) is always false
        let pred = NumPred::Eq(NumExpr::Var("DEBUG".to_string()), NumExpr::Const(0));
        let refined = domain.assume(&elem, &pred);

        // Should still be constant 0
        assert_eq!(refined.get("DEBUG"), ConstValue::Const(0));
        assert!(!refined.is_bottom);

        // if (DEBUG != 0) is always false
        let pred = NumPred::Eq(NumExpr::Var("DEBUG".to_string()), NumExpr::Const(1));
        let refined = domain.assume(&elem, &pred);

        // Should be bottom (contradiction)
        assert!(refined.is_bottom);
    }

    #[test]
    fn test_const_lattice_axioms() {
        use crate::domain::tests::test_lattice_axioms;

        let domain = ConstantDomain;

        // Sample elements for testing
        let samples = vec![
            domain.bottom(),
            domain.constant(&"x".to_string(), -10),
            domain.constant(&"x".to_string(), 0),
            domain.constant(&"x".to_string(), 5),
            domain.constant(&"x".to_string(), 100),
            domain.top(),
            {
                let mut elem = ConstantElement::new();
                elem.set("x".to_string(), ConstValue::Top);
                elem
            },
            // Multi-variable elements
            {
                let mut elem = ConstantElement::new();
                elem.set("x".to_string(), ConstValue::Const(5));
                elem.set("y".to_string(), ConstValue::Const(10));
                elem
            },
        ];

        test_lattice_axioms(&domain, &samples);
    }

    #[test]
    fn test_const_value_addition() {
        assert_eq!(ConstValue::Const(5).add(ConstValue::Const(3)), ConstValue::Const(8));
        assert_eq!(ConstValue::Const(5).add(ConstValue::Top), ConstValue::Top);
        assert_eq!(ConstValue::Bottom.add(ConstValue::Const(5)), ConstValue::Bottom);

        // Overflow
        assert_eq!(ConstValue::Const(i64::MAX).add(ConstValue::Const(1)), ConstValue::Top);
    }

    #[test]
    fn test_const_value_operations() {
        use ConstValue::*;

        assert_eq!(Const(10).sub(Const(3)), Const(7));
        assert_eq!(Const(5).mul(Const(4)), Const(20));
        assert_eq!(Const(15).div(Const(3)), Const(5));
        assert_eq!(Const(17).modulo(Const(5)), Const(2));
        assert_eq!(Const(-5).neg(), Const(5));

        // Division by zero
        assert_eq!(Const(10).div(Const(0)), Top);
        assert_eq!(Const(10).modulo(Const(0)), Top);
    }

    #[test]
    fn test_const_assign() {
        use NumExpr::*;
        let domain = ConstantDomain;

        let mut elem = ConstantElement::new();
        elem.set("x".to_string(), ConstValue::Const(5));
        elem.set("y".to_string(), ConstValue::Const(3));

        // z := x + y
        let expr = Add(Box::new(Var("x".to_string())), Box::new(Var("y".to_string())));
        let result = domain.assign(&elem, &"z".to_string(), &expr);
        assert_eq!(result.get("z"), ConstValue::Const(8));

        // z := x * y
        let expr = Mul(Box::new(Var("x".to_string())), Box::new(Var("y".to_string())));
        let result = domain.assign(&elem, &"z".to_string(), &expr);
        assert_eq!(result.get("z"), ConstValue::Const(15));
    }

    #[test]
    fn test_const_assign_with_top() {
        use NumExpr::*;
        let domain = ConstantDomain;

        let mut elem = ConstantElement::new();
        elem.set("x".to_string(), ConstValue::Const(5));
        elem.set("y".to_string(), ConstValue::Top);

        // z := x + y (Top propagates)
        let expr = Add(Box::new(Var("x".to_string())), Box::new(Var("y".to_string())));
        let result = domain.assign(&elem, &"z".to_string(), &expr);
        assert_eq!(result.get("z"), ConstValue::Top);
    }

    #[test]
    fn test_const_assume_eq() {
        use NumExpr::*;
        use NumPred::*;
        let domain = ConstantDomain;

        let mut elem = ConstantElement::new();
        elem.set("x".to_string(), ConstValue::Top);

        // Assume x = 5
        let result = domain.assume(&elem, &Eq(Var("x".to_string()), Const(5)));
        assert_eq!(result.get("x"), ConstValue::Const(5));
    }

    #[test]
    fn test_const_assume_contradiction() {
        use NumExpr::*;
        use NumPred::*;
        let domain = ConstantDomain;

        let mut elem = ConstantElement::new();
        elem.set("x".to_string(), ConstValue::Const(5));

        // Assume x = 10 (contradiction!)
        let result = domain.assume(&elem, &Eq(Var("x".to_string()), Const(10)));
        assert!(domain.is_bottom(&result));
    }

    #[test]
    fn test_const_assume_neq() {
        use NumExpr::*;
        use NumPred::*;
        let domain = ConstantDomain;

        let mut elem = ConstantElement::new();
        elem.set("x".to_string(), ConstValue::Const(5));

        // Assume x ≠ 5 (contradiction!)
        let result = domain.assume(&elem, &Neq(Var("x".to_string()), Const(5)));
        assert!(domain.is_bottom(&result));

        // Assume x ≠ 10 (consistent)
        let result = domain.assume(&elem, &Neq(Var("x".to_string()), Const(10)));
        assert_eq!(result.get("x"), ConstValue::Const(5));
    }

    #[test]
    fn test_const_get_constant() {
        let domain = ConstantDomain;

        let elem = domain.constant(&"x".to_string(), 42);
        assert_eq!(domain.get_constant(&elem, &"x".to_string()), Some(42));

        let mut elem = ConstantElement::new();
        elem.set("x".to_string(), ConstValue::Top);
        assert_eq!(domain.get_constant(&elem, &"x".to_string()), None);
    }

    #[test]
    fn test_const_get_bounds() {
        let domain = ConstantDomain;

        let elem = domain.constant(&"x".to_string(), 42);
        assert_eq!(domain.get_bounds(&elem, &"x".to_string()), Some((42, 42)));

        let mut elem = ConstantElement::new();
        elem.set("x".to_string(), ConstValue::Top);
        assert_eq!(domain.get_bounds(&elem, &"x".to_string()), Some((i64::MIN, i64::MAX)));
    }

    #[test]
    fn test_const_interval() {
        let domain = ConstantDomain;

        // Singleton interval
        let elem = domain.interval(&"x".to_string(), 5, 5);
        assert_eq!(elem.get("x"), ConstValue::Const(5));

        // Non-singleton interval
        let elem = domain.interval(&"x".to_string(), 1, 10);
        assert_eq!(elem.get("x"), ConstValue::Top);
    }

    #[test]
    fn test_const_project() {
        let domain = ConstantDomain;

        let mut elem = ConstantElement::new();
        elem.set("x".to_string(), ConstValue::Const(5));
        elem.set("y".to_string(), ConstValue::Const(10));

        let result = domain.project(&elem, &"x".to_string());
        assert_eq!(result.get("x"), ConstValue::Top); // x removed
        assert_eq!(result.get("y"), ConstValue::Const(10)); // y unchanged
    }

    #[test]
    fn test_const_widen_narrow() {
        let domain = ConstantDomain;

        let elem1 = domain.constant(&"x".to_string(), 5);
        let elem2 = domain.constant(&"x".to_string(), 5);

        // For flat lattice, widen = join
        let widened = domain.widen(&elem1, &elem2);
        assert_eq!(widened.get("x"), ConstValue::Const(5));

        // For flat lattice, narrow = meet
        let narrowed = domain.narrow(&elem1, &elem2);
        assert_eq!(narrowed.get("x"), ConstValue::Const(5));
    }

    #[test]
    fn test_const_complex_expression() {
        use NumExpr::*;
        let domain = ConstantDomain;

        let mut elem = ConstantElement::new();
        elem.set("x".to_string(), ConstValue::Const(10));
        elem.set("y".to_string(), ConstValue::Const(3));

        // z = (x + y) * 2 - 5
        let expr = Sub(
            Box::new(Mul(
                Box::new(Add(Box::new(Var("x".to_string())), Box::new(Var("y".to_string())))),
                Box::new(Const(2)),
            )),
            Box::new(Const(5)),
        );

        let result = domain.assign(&elem, &"z".to_string(), &expr);
        // (10 + 3) * 2 - 5 = 13 * 2 - 5 = 26 - 5 = 21
        assert_eq!(result.get("z"), ConstValue::Const(21));
    }
}
