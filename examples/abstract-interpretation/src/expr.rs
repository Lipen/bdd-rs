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
