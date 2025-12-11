//! Mini-language for abstract interpretation analysis using SDDs
//!
//! Language supports:
//! - Variables with small integer domains (0-7)
//! - Integer constants
//! - Basic arithmetic (add, multiply, negate)
//! - Boolean predicates (less than, equal, not equal)
//! - Assignments and conditionals
//! - Assertions

use std::collections::HashMap;

/// Variable identifier (1-indexed to align with SDD convention)
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Var(pub usize);

impl Var {
    pub fn new(id: usize) -> Self {
        assert!(id > 0, "Variable IDs must be 1-indexed");
        Var(id)
    }
}

impl std::fmt::Display for Var {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "x{}", self.0)
    }
}

/// Arithmetic expressions
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Expr {
    Var(Var),
    Const(i32),
    Add(Box<Expr>, Box<Expr>),
    Mul(Box<Expr>, Box<Expr>),
    Neg(Box<Expr>),
}

impl Expr {
    /// Evaluate expression given variable assignment
    pub fn eval(&self, env: &HashMap<Var, i32>) -> i32 {
        match self {
            Expr::Var(v) => env.get(v).copied().unwrap_or(0),
            Expr::Const(c) => *c,
            Expr::Add(left, right) => left.eval(env) + right.eval(env),
            Expr::Mul(left, right) => left.eval(env) * right.eval(env),
            Expr::Neg(e) => -e.eval(env),
        }
    }

    /// Collect all variables appearing in expression
    pub fn vars(&self) -> Vec<Var> {
        let mut vars = Vec::new();
        self.collect_vars(&mut vars);
        vars.sort_unstable();
        vars.dedup();
        vars
    }

    fn collect_vars(&self, vars: &mut Vec<Var>) {
        match self {
            Expr::Var(v) => vars.push(*v),
            Expr::Const(_) => {}
            Expr::Add(left, right) | Expr::Mul(left, right) => {
                left.collect_vars(vars);
                right.collect_vars(vars);
            }
            Expr::Neg(e) => e.collect_vars(vars),
        }
    }
}

impl std::fmt::Display for Expr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Expr::Var(v) => write!(f, "{}", v),
            Expr::Const(c) => write!(f, "{}", c),
            Expr::Add(l, r) => write!(f, "({} + {})", l, r),
            Expr::Mul(l, r) => write!(f, "({} * {})", l, r),
            Expr::Neg(e) => write!(f, "(-{})", e),
        }
    }
}

/// Boolean predicates
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Predicate {
    Lt(Expr, Expr), // <
    Le(Expr, Expr), // <=
    Eq(Expr, Expr), // ==
    Ne(Expr, Expr), // !=
    And(Box<Predicate>, Box<Predicate>),
    Or(Box<Predicate>, Box<Predicate>),
    Not(Box<Predicate>),
}

impl Predicate {
    /// Evaluate predicate given variable assignment
    pub fn eval(&self, env: &HashMap<Var, i32>) -> bool {
        match self {
            Predicate::Lt(l, r) => l.eval(env) < r.eval(env),
            Predicate::Le(l, r) => l.eval(env) <= r.eval(env),
            Predicate::Eq(l, r) => l.eval(env) == r.eval(env),
            Predicate::Ne(l, r) => l.eval(env) != r.eval(env),
            Predicate::And(p1, p2) => p1.eval(env) && p2.eval(env),
            Predicate::Or(p1, p2) => p1.eval(env) || p2.eval(env),
            Predicate::Not(p) => !p.eval(env),
        }
    }

    /// Collect all variables in predicate
    pub fn vars(&self) -> Vec<Var> {
        let mut vars = Vec::new();
        self.collect_vars(&mut vars);
        vars.sort_unstable();
        vars.dedup();
        vars
    }

    fn collect_vars(&self, vars: &mut Vec<Var>) {
        match self {
            Predicate::Lt(l, r) | Predicate::Le(l, r) | Predicate::Eq(l, r) | Predicate::Ne(l, r) => {
                for v in l.vars() {
                    vars.push(v);
                }
                for v in r.vars() {
                    vars.push(v);
                }
            }
            Predicate::And(p1, p2) | Predicate::Or(p1, p2) => {
                p1.collect_vars(vars);
                p2.collect_vars(vars);
            }
            Predicate::Not(p) => p.collect_vars(vars),
        }
    }
}

impl std::fmt::Display for Predicate {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Predicate::Lt(l, r) => write!(f, "{} < {}", l, r),
            Predicate::Le(l, r) => write!(f, "{} <= {}", l, r),
            Predicate::Eq(l, r) => write!(f, "{} == {}", l, r),
            Predicate::Ne(l, r) => write!(f, "{} != {}", l, r),
            Predicate::And(p1, p2) => write!(f, "({} && {})", p1, p2),
            Predicate::Or(p1, p2) => write!(f, "({} || {})", p1, p2),
            Predicate::Not(p) => write!(f, "!{}", p),
        }
    }
}

/// Statement in the mini-language
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Stmt {
    /// Assignment: var = expr
    Assign(Var, Expr),

    /// Conditional branch: if pred { then_branch } else { else_branch }
    If(Predicate, Vec<Stmt>, Vec<Stmt>),

    /// Assume predicate (constraint): assume pred
    Assume(Predicate),

    /// Assert predicate (verification): assert pred
    Assert(Predicate),
}

impl std::fmt::Display for Stmt {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Stmt::Assign(var, expr) => write!(f, "{} := {}", var, expr),
            Stmt::If(pred, then_b, else_b) => {
                write!(f, "if {} {{ ", pred)?;
                for s in then_b {
                    write!(f, "{}; ", s)?;
                }
                write!(f, "}} else {{ ")?;
                for s in else_b {
                    write!(f, "{}; ", s)?;
                }
                write!(f, "}}")
            }
            Stmt::Assume(pred) => write!(f, "assume {}", pred),
            Stmt::Assert(pred) => write!(f, "assert {}", pred),
        }
    }
}

/// A program: sequence of statements
pub type Program = Vec<Stmt>;

/// Collect all variables used in a program
pub fn program_vars(prog: &Program) -> Vec<Var> {
    let mut vars = Vec::new();
    for stmt in prog {
        match stmt {
            Stmt::Assign(var, expr) => {
                vars.push(*var);
                for v in expr.vars() {
                    vars.push(v);
                }
            }
            Stmt::If(pred, then_b, else_b) => {
                for v in pred.vars() {
                    vars.push(v);
                }
                for v in program_vars(then_b) {
                    vars.push(v);
                }
                for v in program_vars(else_b) {
                    vars.push(v);
                }
            }
            Stmt::Assume(pred) | Stmt::Assert(pred) => {
                for v in pred.vars() {
                    vars.push(v);
                }
            }
        }
    }
    vars.sort_unstable();
    vars.dedup();
    vars
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_expr_eval() {
        let mut env = HashMap::new();
        env.insert(Var::new(1), 3);
        env.insert(Var::new(2), 5);

        let expr = Expr::Add(Box::new(Expr::Var(Var::new(1))), Box::new(Expr::Var(Var::new(2))));
        assert_eq!(expr.eval(&env), 8);
    }

    #[test]
    fn test_predicate_eval() {
        let mut env = HashMap::new();
        env.insert(Var::new(1), 3);
        env.insert(Var::new(2), 5);

        let pred = Predicate::Lt(Expr::Var(Var::new(1)), Expr::Var(Var::new(2)));
        assert!(pred.eval(&env));

        let pred_false = Predicate::Eq(Expr::Var(Var::new(1)), Expr::Var(Var::new(2)));
        assert!(!pred_false.eval(&env));
    }
}
