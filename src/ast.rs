use std::collections::VecDeque;
use std::fmt::Display;
use std::ops::{Add, Mul, Neg};

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

    pub fn to_string(&self) -> String
    where
        T: Display,
    {
        match self {
            ExprBoxed::Term(term) => format!("{}", term),
            ExprBoxed::Not(a) => format!("~{}", a.to_string()),
            ExprBoxed::And(a, b) => format!("({} & {})", a.to_string(), b.to_string()),
            ExprBoxed::Or(a, b) => format!("({} | {})", a.to_string(), b.to_string()),
            ExprBoxed::Xor(a, b) => format!("({} ^ {})", a.to_string(), b.to_string()),
            ExprBoxed::Ite(a, b, c) => format!("({} ? {} : {})", a.to_string(), b.to_string(), c.to_string()),
        }
    }
}

#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub struct Idx(usize);

#[derive(Debug)]
pub enum Expr<T, N = Idx> {
    Term(T),
    Not(N),
    And(N, N),
    Or(N, N),
    Xor(N, N),
    Ite(N, N, N),
}

pub trait Functor {
    type Inner;
    type Mapped<R>: Functor;

    fn fmap<R, F>(self, f: F) -> Self::Mapped<R>
    where
        F: FnMut(Self::Inner) -> R;
}

// Just an example of how to implement the Functor trait for a type.
impl<T> Functor for Option<T> {
    type Inner = T;
    type Mapped<R> = Option<R>;

    fn fmap<R, F>(self, f: F) -> Self::Mapped<R>
    where
        F: FnMut(Self::Inner) -> R,
    {
        self.map(f)
    }
}

impl<T, N> Functor for Expr<T, N> {
    type Inner = N;
    type Mapped<R> = Expr<T, R>;

    fn fmap<R, F>(self, mut f: F) -> Self::Mapped<R>
    where
        F: FnMut(Self::Inner) -> R,
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

impl<'a, T, N> Functor for &'a Expr<T, N> {
    type Inner = &'a N;
    type Mapped<R> = Expr<&'a T, R>;

    fn fmap<R, F>(self, mut f: F) -> Self::Mapped<R>
    where
        F: FnMut(Self::Inner) -> R,
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

pub trait Tree {
    type Leaf;
    type Node;
}

impl<T, N> Tree for Expr<T, N> {
    type Leaf = T;
    type Node = N;
}

// See: https://recursion.wtf/posts/rust_schemes/
#[derive(Debug)]
pub struct Arena<E> {
    exprs: Vec<E>,
}

impl<E> Arena<E>
where
    E: Tree,
{
    fn expand_exprs<S, R, F>(seed: S, expand: F) -> Self
    where
        R: Functor<Inner = S, Mapped<Idx> = E>,
        F: Fn(S) -> R,
    {
        let mut frontier: VecDeque<S> = VecDeque::from([seed]);
        let mut exprs: Vec<E> = vec![];

        while let Some(seed) = frontier.pop_front() {
            let expr = expand(seed);
            let expr = expr.fmap(|e| {
                frontier.push_back(e);
                Idx(exprs.len() + frontier.len())
            });
            exprs.push(expr);
        }

        Self { exprs }
    }
}

impl<T> Arena<Expr<T>> {
    pub fn from_boxed(ast: &ExprBoxed<T>) -> Self
    where
        T: Clone,
    {
        Self::expand_exprs(ast, |seed| match seed {
            ExprBoxed::Term(term) => Expr::Term(term.clone()),
            ExprBoxed::Not(a) => Expr::Not(&**a),
            ExprBoxed::And(a, b) => Expr::And(&**a, &**b),
            ExprBoxed::Or(a, b) => Expr::Or(&**a, &**b),
            ExprBoxed::Xor(a, b) => Expr::Xor(&**a, &**b),
            ExprBoxed::Ite(a, b, c) => Expr::Ite(&**a, &**b, &**c),
        })
    }
}

impl<'a, E: 'a> Arena<E>
where
    &'a E: Functor<Inner = &'a Idx>,
{
    fn collapse_exprs<R, F>(&'a self, mut collapse: F) -> R
    where
        F: FnMut(<&'a E as Functor>::Mapped<R>) -> R,
    {
        let mut results: Vec<Option<R>> = std::iter::repeat_with(|| None).take(self.exprs.len()).collect();

        for (i, expr) in self.exprs.iter().enumerate().rev() {
            let expr = expr.fmap(|idx| results[idx.0].take().unwrap());
            let result = collapse(expr);
            results[i] = Some(result);
        }

        results.into_iter().next().unwrap().unwrap()
    }
}

impl<T> Arena<Expr<T>> {
    pub fn to_boxed(&self) -> ExprBoxed<T>
    where
        T: Clone,
    {
        self.collapse_exprs(|expr| match expr {
            Expr::Term(term) => ExprBoxed::term(term.clone()),
            Expr::Not(a) => ExprBoxed::not(a),
            Expr::And(a, b) => ExprBoxed::and(a, b),
            Expr::Or(a, b) => ExprBoxed::or(a, b),
            Expr::Xor(a, b) => ExprBoxed::xor(a, b),
            Expr::Ite(a, b, c) => ExprBoxed::ite(a, b, c),
        })
    }
}

impl<T> Arena<Expr<T>> {
    pub fn eval(&self) -> T
    where
        T: Clone,
        T: Neg<Output = T>,
        T: Mul<Output = T>,
        T: Add<Output = T>,
    {
        self.collapse_exprs(|expr: Expr<&T, T>| match expr {
            Expr::Term(term) => term.clone(),
            Expr::Not(a) => -a,
            Expr::And(a, b) => a * b,
            Expr::Or(a, b) => a + b,
            _ => todo!(),
        })
    }
}

impl<T> Arena<Expr<T>> {
    pub fn to_string(&self) -> String
    where
        T: Display,
    {
        self.collapse_exprs(|expr| match expr {
            Expr::Term(term) => format!("{}", term),
            Expr::Not(a) => format!("~{}", a),
            Expr::And(a, b) => format!("({} & {})", a, b),
            Expr::Or(a, b) => format!("({} | {})", a, b),
            Expr::Xor(a, b) => format!("({} ^ {})", a, b),
            Expr::Ite(a, b, c) => format!("({} ? {} : {})", a, b, c),
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_expr() {
        let expr_boxed = ExprBoxed::and(
            ExprBoxed::term(4),
            ExprBoxed::not(ExprBoxed::or(ExprBoxed::term(2), ExprBoxed::Term(3))),
        );
        println!("expr_boxed = {:?}", expr_boxed);
        println!("expr_boxed = {}", expr_boxed.to_string());
        let arena = Arena::from_boxed(&expr_boxed);
        println!("arena = {:?}", arena);
        println!("arena = {}", arena.to_string());
        for expr in arena.exprs.iter() {
            println!("- {:?}", expr);
        }
        println!("eval = {}", arena.eval());
        assert_eq!(arena.eval(), 4 * -(2 + 3));
        println!("boxed = {:?}", arena.to_boxed());
    }

    #[test]
    fn test_generic() {
        let expr_boxed = ExprBoxed::and(
            ExprBoxed::term(4),
            ExprBoxed::not(ExprBoxed::or(ExprBoxed::term(2), ExprBoxed::Term(3))),
        );
        println!("expr_boxed = {:?}", expr_boxed);
        println!("expr_boxed = {}", expr_boxed.to_string());
        let arena = Arena::from_boxed(&expr_boxed);
        println!("arena = {:?}", arena);
        println!("arena = {}", arena.to_string());
        for expr in arena.exprs.iter() {
            println!("- {:?}", expr);
        }
        println!("eval = {}", arena.eval());
        assert_eq!(arena.eval(), 4 * -(2 + 3));
        println!("boxed = {:?}", arena.to_boxed());
    }
}
