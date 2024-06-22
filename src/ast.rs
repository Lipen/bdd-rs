use std::collections::VecDeque;
use std::ops::{Add, BitAnd, BitOr, BitXor, Mul, Neg};

use num_traits::Zero;

#[derive(Debug, Clone)]
pub enum ExprBoxed<T> {
    Term(T),
    Not(Box<ExprBoxed<T>>),
    And(Box<ExprBoxed<T>>, Box<ExprBoxed<T>>),
    Or(Box<ExprBoxed<T>>, Box<ExprBoxed<T>>),
    Xor(Box<ExprBoxed<T>>, Box<ExprBoxed<T>>),
    Ite(Box<ExprBoxed<T>>, Box<ExprBoxed<T>>, Box<ExprBoxed<T>>),
}

impl<T> ExprBoxed<T> {
    pub fn term(value: T) -> Self {
        ExprBoxed::Term(value)
    }

    pub fn not(value: Self) -> Self {
        match value {
            ExprBoxed::Term(term) => ExprBoxed::Term(term),
            ExprBoxed::Not(inner) => *inner,
            _ => ExprBoxed::Not(Box::new(value)),
        }
    }

    pub fn and(lhs: Self, rhs: Self) -> Self {
        ExprBoxed::And(Box::new(lhs), Box::new(rhs))
    }

    pub fn or(lhs: Self, rhs: Self) -> Self {
        ExprBoxed::Or(Box::new(lhs), Box::new(rhs))
    }

    pub fn xor(lhs: Self, rhs: Self) -> Self {
        ExprBoxed::Xor(Box::new(lhs), Box::new(rhs))
    }

    pub fn ite(cond: Self, then: Self, else_: Self) -> Self {
        ExprBoxed::Ite(Box::new(cond), Box::new(then), Box::new(else_))
    }
}

#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub struct Idx(usize);

#[derive(Debug)]
pub enum Expr<T, I = Idx> {
    Term(T),
    Not(I),
    And(I, I),
    Or(I, I),
    Xor(I, I),
    Ite(I, I, I),
}

impl<T, A> Expr<T, A> {
    #[inline(always)]
    pub fn fmap<B, F>(self, mut f: F) -> Expr<T, B>
    where
        F: FnMut(A) -> B,
    {
        match self {
            Expr::Term(a) => Expr::Term(a),
            Expr::Not(a) => Expr::Not(f(a)),
            Expr::And(a, b) => Expr::And(f(a), f(b)),
            Expr::Or(a, b) => Expr::Or(f(a), f(b)),
            Expr::Xor(a, b) => Expr::Xor(f(a), f(b)),
            Expr::Ite(a, b, c) => Expr::Ite(f(a), f(b), f(c)),
        }
    }

    #[inline(always)]
    pub fn fmap_ref<B, F>(&self, mut f: F) -> Expr<&T, B>
    where
        F: FnMut(&A) -> B,
    {
        match self {
            Expr::Term(a) => Expr::Term(a),
            Expr::Not(a) => Expr::Not(f(a)),
            Expr::And(a, b) => Expr::And(f(a), f(b)),
            Expr::Or(a, b) => Expr::Or(f(a), f(b)),
            Expr::Xor(a, b) => Expr::Xor(f(a), f(b)),
            Expr::Ite(a, b, c) => Expr::Ite(f(a), f(b), f(c)),
        }
    }
}

// See: https://recursion.wtf/posts/rust_schemes/
#[derive(Debug)]
pub struct ExprArena<T> {
    /// Topology sorted expressions, by construction.
    exprs: Vec<Expr<T>>,
}

impl<T> ExprArena<T> {
    pub fn get(&self, idx: Idx) -> &Expr<T> {
        &self.exprs[idx.0]
    }

    pub fn get_mut(&mut self, idx: Idx) -> &mut Expr<T> {
        &mut self.exprs[idx.0]
    }
}

impl<T> ExprArena<T> {
    fn expand_exprs<R, F>(seed: R, expand: F) -> Self
    where
        R: Clone,
        F: Fn(R) -> Expr<T, R>,
    {
        let mut frontier: VecDeque<R> = VecDeque::from([seed]);
        let mut exprs: Vec<Expr<T>> = vec![];

        while let Some(seed) = frontier.pop_front() {
            let expr = expand(seed);
            let expr = expr.fmap(|e| {
                frontier.push_back(e.clone());
                Idx(exprs.len() + frontier.len())
            });
            exprs.push(expr);
        }

        Self { exprs }
    }

    pub fn from_boxed(ast: &ExprBoxed<T>) -> Self
    where
        T: Clone,
    {
        Self::expand_exprs(ast, |seed| match seed {
            ExprBoxed::Term(term) => Expr::Term(term.clone()),
            ExprBoxed::Not(a) => Expr::Not(a),
            ExprBoxed::And(a, b) => Expr::And(a, b),
            ExprBoxed::Or(a, b) => Expr::Or(a, b),
            ExprBoxed::Xor(a, b) => Expr::Xor(a, b),
            ExprBoxed::Ite(a, b, c) => Expr::Ite(a, b, c),
        })
    }
}

impl<T> ExprArena<T> {
    fn collapse_exprs<R, F>(&self, mut collapse: F) -> R
    where
        F: FnMut(Expr<&T, R>) -> R,
    {
        let mut results: Vec<Option<R>> = std::iter::repeat_with(|| None)
            .take(self.exprs.len())
            .collect();

        for (i, expr) in self.exprs.iter().enumerate().rev() {
            let expr = expr.fmap_ref(|idx| results[idx.0].take().unwrap());
            let result = collapse(expr);
            results[i] = Some(result);
        }

        results.into_iter().next().unwrap().unwrap()
    }

    pub fn eval(&self) -> T
    where
        T: Clone,
        T: Neg<Output = T>,
        // T: BitAnd<Output=T>,
        // T: BitOr<Output=T>,
        T: Mul<Output = T>, // temporarily
        T: Add<Output = T>, // temporarily
        T: BitXor<Output = T>,
        T: Zero,
    {
        self.collapse_exprs::<T, _>(|expr| match expr {
            Expr::Term(term) => term.clone(),
            Expr::Not(a) => -a,
            Expr::And(a, b) => a * b,
            Expr::Or(a, b) => a + b,
            Expr::Xor(a, b) => a ^ b,
            Expr::Ite(a, b, c) => {
                if a.is_zero() {
                    b
                } else {
                    c
                }
            }
        })
    }

    pub fn to_boxed(&self) -> ExprBoxed<T>
    where
        T: Clone,
    {
        self.collapse_exprs::<ExprBoxed<T>, _>(|expr| match expr {
            Expr::Term(term) => ExprBoxed::term(term.clone()),
            Expr::Not(a) => ExprBoxed::not(a),
            Expr::And(a, b) => ExprBoxed::and(a, b),
            Expr::Or(a, b) => ExprBoxed::or(a, b),
            Expr::Xor(a, b) => ExprBoxed::xor(a, b),
            Expr::Ite(a, b, c) => ExprBoxed::ite(a, b, c),
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test() {
        let expr_boxed = ExprBoxed::and(
            ExprBoxed::term(4),
            ExprBoxed::or(ExprBoxed::term(2), ExprBoxed::Term(3)),
        );
        println!("expr_boxed = {:?}", expr_boxed);
        let arena = ExprArena::from_boxed(&expr_boxed);
        println!("arena = {:?}", arena);
        for expr in arena.exprs.iter() {
            println!("- {:?}", expr);
        }
        println!("eval = {}", arena.eval());
        println!("eval = {}", arena.eval());
        println!("eval = {}", arena.eval());
        println!("boxed = {:?}", arena.to_boxed());
    }
}
