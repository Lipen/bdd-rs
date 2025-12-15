//! Numeric expressions and predicates.

use std::fmt::Debug;

/// Numeric expression (right-hand side of assignments).
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum NumExpr<V, C = i64> {
    /// Variable reference
    Var(V),
    /// Constant value
    Const(C),
    /// Addition: e1 + e2
    Add(Box<NumExpr<V, C>>, Box<NumExpr<V, C>>),
    /// Subtraction: e1 - e2
    Sub(Box<NumExpr<V, C>>, Box<NumExpr<V, C>>),
    /// Multiplication: e1 * e2
    Mul(Box<NumExpr<V, C>>, Box<NumExpr<V, C>>),
    /// Division: e1 / e2
    Div(Box<NumExpr<V, C>>, Box<NumExpr<V, C>>),
    /// Negation: -e
    Neg(Box<NumExpr<V, C>>),
    /// Modulo: e1 % e2
    Mod(Box<NumExpr<V, C>>, Box<NumExpr<V, C>>),
}

impl<V, C> NumExpr<V, C> {
    /// Variable reference
    pub fn var(var: impl Into<V>) -> Self {
        NumExpr::Var(var.into())
    }

    /// Constant value
    pub fn constant(value: impl Into<C>) -> Self {
        NumExpr::Const(value.into())
    }

    /// Addition: self + other
    pub fn add(self, other: Self) -> Self {
        NumExpr::Add(Box::new(self), Box::new(other))
    }

    /// Subtraction: self - other
    pub fn sub(self, other: Self) -> Self {
        NumExpr::Sub(Box::new(self), Box::new(other))
    }

    /// Multiplication: self * other
    pub fn mul(self, other: Self) -> Self {
        NumExpr::Mul(Box::new(self), Box::new(other))
    }

    /// Division: self / other
    pub fn div(self, other: Self) -> Self {
        NumExpr::Div(Box::new(self), Box::new(other))
    }

    /// Negation: -self
    pub fn neg(self) -> Self {
        NumExpr::Neg(Box::new(self))
    }

    /// Modulo: self % other
    pub fn modulo(self, other: Self) -> Self {
        NumExpr::Mod(Box::new(self), Box::new(other))
    }

    /// Equality: self == other
    pub fn eq(self, other: Self) -> NumPred<V, C> {
        NumPred::Eq(self, other)
    }

    /// Inequality: self != other
    pub fn neq(self, other: Self) -> NumPred<V, C> {
        NumPred::Neq(self, other)
    }

    /// Less than: self < other
    pub fn lt(self, other: Self) -> NumPred<V, C> {
        NumPred::Lt(self, other)
    }

    /// Less or equal: self <= other
    pub fn le(self, other: Self) -> NumPred<V, C> {
        NumPred::Le(self, other)
    }

    /// Greater than: self > other
    pub fn gt(self, other: Self) -> NumPred<V, C> {
        NumPred::Gt(self, other)
    }

    /// Greater or equal: self >= other
    pub fn ge(self, other: Self) -> NumPred<V, C> {
        NumPred::Ge(self, other)
    }
}

/// Numeric predicate (boolean condition).
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum NumPred<V, C = i64> {
    /// Always true
    True,
    /// Always false
    False,
    /// Equality: e1 == e2
    Eq(NumExpr<V, C>, NumExpr<V, C>),
    /// Inequality: e1 != e2
    Neq(NumExpr<V, C>, NumExpr<V, C>),
    /// Less than: e1 < e2
    Lt(NumExpr<V, C>, NumExpr<V, C>),
    /// Less or equal: e1 <= e2
    Le(NumExpr<V, C>, NumExpr<V, C>),
    /// Greater than: e1 > e2
    Gt(NumExpr<V, C>, NumExpr<V, C>),
    /// Greater or equal: e1 >= e2
    Ge(NumExpr<V, C>, NumExpr<V, C>),
    /// Negation: !p
    Not(Box<NumPred<V, C>>),
    /// Conjunction: p1 && p2
    And(Box<NumPred<V, C>>, Box<NumPred<V, C>>),
    /// Disjunction: p1 || p2
    Or(Box<NumPred<V, C>>, Box<NumPred<V, C>>),
}

impl<V, C> NumPred<V, C> {
    /// Negation: !p
    pub fn not(self) -> Self {
        NumPred::Not(Box::new(self))
    }

    /// Conjunction: p1 && p2
    pub fn and(self, other: Self) -> Self {
        NumPred::And(Box::new(self), Box::new(other))
    }

    /// Disjunction: p1 || p2
    pub fn or(self, other: Self) -> Self {
        NumPred::Or(Box::new(self), Box::new(other))
    }
}

/// Program statements for abstract interpretation.
#[derive(Debug, Clone)]
pub enum Stmt<V> {
    /// Skip (no-op)
    Skip,
    /// Assignment: var := expr
    Assign(V, NumExpr<V>),
    /// Sequence: s1; s2
    Seq(Box<Stmt<V>>, Box<Stmt<V>>),
    /// Conditional: if (pred) then s1 else s2
    If(NumPred<V>, Box<Stmt<V>>, Box<Stmt<V>>),
    /// While loop: while (pred) do s
    While(NumPred<V>, Box<Stmt<V>>),
    /// Assertion: assert(pred)
    Assert(NumPred<V>),
    /// Assumption: assume(pred)
    Assume(NumPred<V>),
    /// Havoc: var := * (non-deterministic)
    Havoc(V),
}
