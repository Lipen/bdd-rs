use std::ops::{Add, BitXor, Mul, Neg};

use crate::bdd::Bdd;
use crate::reference::Ref;

pub trait Eval {
    fn eval(&self, bdd: &Bdd) -> Ref;
}

impl Bdd {
    pub fn eval(&self, value: impl Eval) -> Ref {
        value.eval(self)
    }
}

impl Eval for Ref {
    fn eval(&self, _bdd: &Bdd) -> Ref {
        *self
    }
}

#[derive(Debug)]
pub enum Expr {
    Term(Ref),
    Not(Box<Expr>),
    And(Box<Expr>, Box<Expr>),
    Or(Box<Expr>, Box<Expr>),
    Xor(Box<Expr>, Box<Expr>),
}

impl Expr {
    pub fn term(value: Ref) -> Self {
        Expr::Term(value)
    }

    pub fn not(value: Self) -> Self {
        match value {
            Expr::Term(term) => Expr::Term(-term),
            Expr::Not(inner) => *inner,
            _ => Expr::Not(Box::new(value)),
        }
    }

    pub fn and(lhs: Self, rhs: Self) -> Self {
        Expr::And(Box::new(lhs), Box::new(rhs))
    }

    pub fn or(lhs: Self, rhs: Self) -> Self {
        Expr::Or(Box::new(lhs), Box::new(rhs))
    }

    pub fn xor(lhs: Self, rhs: Self) -> Self {
        Expr::Xor(Box::new(lhs), Box::new(rhs))
    }
}

impl Eval for Expr {
    fn eval(&self, bdd: &Bdd) -> Ref {
        match self {
            Expr::Term(term) => term.eval(bdd),
            Expr::Not(inner) => -inner.eval(bdd),
            Expr::And(lhs, rhs) => bdd.apply_and(lhs.eval(bdd), rhs.eval(bdd)),
            Expr::Or(lhs, rhs) => bdd.apply_or(lhs.eval(bdd), rhs.eval(bdd)),
            Expr::Xor(lhs, rhs) => bdd.apply_xor(lhs.eval(bdd), rhs.eval(bdd)),
        }
    }
}

// -Expr = Expr::Not
impl Neg for Expr {
    type Output = Expr;

    fn neg(self) -> Self::Output {
        Expr::not(self)
    }
}

// Expr * Expr = Expr::And
impl Mul for Expr {
    type Output = Expr;

    fn mul(self, rhs: Self) -> Self::Output {
        Expr::and(self, rhs)
    }
}

// Ref * Expr = Expr::And
impl Mul<Expr> for Ref {
    type Output = Expr;

    fn mul(self, rhs: Expr) -> Self::Output {
        Expr::and(Expr::term(self), rhs)
    }
}

// Expr * Ref = Expr::And
impl Mul<Ref> for Expr {
    type Output = Expr;

    fn mul(self, rhs: Ref) -> Self::Output {
        Expr::and(self, Expr::term(rhs))
    }
}

// Ref * Ref = Expr::And
impl Mul for Ref {
    type Output = Expr;

    fn mul(self, rhs: Self) -> Self::Output {
        Expr::and(Expr::term(self), Expr::term(rhs))
    }
}

// Expr + Expr = Expr::Or
impl Add for Expr {
    type Output = Expr;

    fn add(self, rhs: Self) -> Self::Output {
        Expr::or(self, rhs)
    }
}

// Ref + Expr = Expr::Or
impl Add<Expr> for Ref {
    type Output = Expr;

    fn add(self, rhs: Expr) -> Self::Output {
        Expr::or(Expr::term(self), rhs)
    }
}

// Expr + Ref = Expr::Or
impl Add<Ref> for Expr {
    type Output = Expr;

    fn add(self, rhs: Ref) -> Self::Output {
        Expr::or(self, Expr::term(rhs))
    }
}

// Ref + Ref = Expr::Or
impl Add for Ref {
    type Output = Expr;

    fn add(self, rhs: Self) -> Self::Output {
        Expr::or(Expr::term(self), Expr::term(rhs))
    }
}

// Expr ^ Expr = Expr::Xor
impl BitXor for Expr {
    type Output = Expr;

    fn bitxor(self, rhs: Self) -> Self::Output {
        Expr::xor(self, rhs)
    }
}

// Ref ^ Expr = Expr::Xor
impl BitXor<Expr> for Ref {
    type Output = Expr;

    fn bitxor(self, rhs: Expr) -> Self::Output {
        Expr::xor(Expr::term(self), rhs)
    }
}

// Expr ^ Ref = Expr::Xor
impl BitXor<Ref> for Expr {
    type Output = Expr;

    fn bitxor(self, rhs: Ref) -> Self::Output {
        Expr::xor(self, Expr::term(rhs))
    }
}

// Ref ^ Ref = Expr::Xor
impl BitXor for Ref {
    type Output = Expr;

    fn bitxor(self, rhs: Self) -> Self::Output {
        Expr::xor(Expr::term(self), Expr::term(rhs))
    }
}

#[cfg(test)]
mod tests {
    use test_log::test;

    use super::*;

    #[test]
    fn test_eval_var() {
        let bdd = Bdd::default();
        let x = bdd.mk_var(1);

        let res = bdd.eval(x);
        assert_eq!(res, x);
    }

    #[test]
    fn test_eval_not_var() {
        let bdd = Bdd::default();
        let x = bdd.mk_var(1);

        let res = bdd.eval(-x);
        assert_eq!(res, -x);
    }

    #[test]
    fn test_eval_and() {
        let bdd = Bdd::default();
        let x = bdd.mk_var(1);
        let y = bdd.mk_var(2);

        let res = bdd.eval(x * y);
        let expected = bdd.apply_and(x, y);
        assert_eq!(res, expected);
    }

    #[test]
    fn test_eval_or() {
        let bdd = Bdd::default();
        let x = bdd.mk_var(1);
        let y = bdd.mk_var(2);

        let res = bdd.eval(x + y);
        let expected = bdd.apply_or(x, y);
        assert_eq!(res, expected);
    }

    #[test]
    fn test_eval_xor() {
        let bdd = Bdd::default();
        let x = bdd.mk_var(1);
        let y = bdd.mk_var(2);

        let res = bdd.eval(x ^ y);
        let expected = bdd.apply_xor(x, y);
        assert_eq!(res, expected);
    }

    #[test]
    fn test_eval_complex() {
        let bdd = Bdd::default();
        let x = bdd.mk_var(1);
        let y = bdd.mk_var(2);
        let z = bdd.mk_var(3);
        let t = bdd.mk_var(4);

        let res = bdd.eval(x + y ^ z * t);
        let expected = bdd.apply_xor(bdd.apply_or(x, y), bdd.apply_and(z, t));
        assert_eq!(res, expected);
    }

    #[test]
    fn test_eval_neg() {
        let bdd = Bdd::default();
        let x = bdd.mk_var(1);
        let y = bdd.mk_var(2);

        let res = bdd.eval(-x * -y);
        let expected = bdd.apply_and(-x, -y);
        assert_eq!(res, expected);

        let res = bdd.eval(-x + -y);
        let expected = bdd.apply_or(-x, -y);
        assert_eq!(res, expected);

        let res = bdd.eval(-x ^ -y);
        let expected = bdd.apply_xor(-x, -y);
        assert_eq!(res, expected);

        let res = bdd.eval(-(x * -y));
        let expected = -bdd.apply_and(x, -y);
        assert_eq!(res, expected);

        let res = bdd.eval(-(x + -y));
        let expected = -bdd.apply_or(x, -y);
        assert_eq!(res, expected);

        let res = bdd.eval(-(x ^ -y));
        let expected = -bdd.apply_xor(x, -y);
        assert_eq!(res, expected);

        let z = bdd.mk_var(3);

        let res = bdd.eval(-(-x * -(y + -z)));
        let expected = -bdd.apply_and(-x, -bdd.apply_or(y, -z));
        assert_eq!(res, expected);
    }
}
