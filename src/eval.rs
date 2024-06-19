use std::ops::{Add, BitXor, Mul};

use crate::bdd::Bdd;
use crate::reference::Ref;

pub struct BddAndOp {
    f: Ref,
    g: Ref,
}

impl Mul for Ref {
    type Output = BddAndOp;

    fn mul(self, rhs: Self) -> Self::Output {
        BddAndOp { f: self, g: rhs }
    }
}

pub struct BddOrOp {
    f: Ref,
    g: Ref,
}

impl Add for Ref {
    type Output = BddOrOp;

    fn add(self, rhs: Self) -> Self::Output {
        BddOrOp { f: self, g: rhs }
    }
}

pub struct BddXorOp {
    f: Ref,
    g: Ref,
}

impl BitXor for Ref {
    type Output = BddXorOp;

    fn bitxor(self, rhs: Self) -> Self::Output {
        BddXorOp { f: self, g: rhs }
    }
}

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
        self.clone()
    }
}

impl Eval for BddAndOp {
    fn eval(&self, bdd: &Bdd) -> Ref {
        bdd.apply_and(self.f, self.g)
    }
}

impl Eval for BddOrOp {
    fn eval(&self, bdd: &Bdd) -> Ref {
        bdd.apply_or(self.f, self.g)
    }
}

impl Eval for BddXorOp {
    fn eval(&self, bdd: &Bdd) -> Ref {
        bdd.apply_xor(self.f, self.g)
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
        let f = bdd.apply_and(x, y);
        let res = bdd.eval(x * y);
        assert_eq!(res, f);
    }

    #[test]
    fn test_eval_or() {
        let bdd = Bdd::default();
        let x = bdd.mk_var(1);
        let y = bdd.mk_var(2);
        let f = bdd.apply_or(x, y);
        let res = bdd.eval(x + y);
        assert_eq!(res, f);
    }

    #[test]
    fn test_eval_xor() {
        let bdd = Bdd::default();
        let x = bdd.mk_var(1);
        let y = bdd.mk_var(2);
        let f = bdd.apply_xor(x, y);
        let res = bdd.eval(x ^ y);
        assert_eq!(res, f);
    }
}
