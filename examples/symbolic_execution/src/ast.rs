//! Abstract Syntax Tree for a simple imperative language.
//!
//! The language supports:
//! - Boolean variables
//! - Boolean expressions (AND, OR, NOT, XOR, IMPLIES)
//! - Assignments
//! - Conditionals (if-then-else)
//! - Sequences
//! - Loops (while)
//! - Assertions

use std::fmt;

/// Variable name
pub type Var = String;

/// Boolean expression
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Expr {
    /// Boolean literal
    Lit(bool),
    /// Variable reference
    Var(Var),
    /// Logical NOT
    Not(Box<Expr>),
    /// Logical AND
    And(Box<Expr>, Box<Expr>),
    /// Logical OR
    Or(Box<Expr>, Box<Expr>),
    /// Logical XOR
    Xor(Box<Expr>, Box<Expr>),
    /// Logical IMPLIES
    Implies(Box<Expr>, Box<Expr>),
    /// Equality
    Eq(Box<Expr>, Box<Expr>),
}

impl Expr {
    pub fn var(name: impl Into<String>) -> Self {
        Expr::Var(name.into())
    }

    pub fn and(self, other: Expr) -> Self {
        Expr::And(Box::new(self), Box::new(other))
    }

    pub fn or(self, other: Expr) -> Self {
        Expr::Or(Box::new(self), Box::new(other))
    }

    pub fn not(self) -> Self {
        Expr::Not(Box::new(self))
    }

    pub fn xor(self, other: Expr) -> Self {
        Expr::Xor(Box::new(self), Box::new(other))
    }

    pub fn implies(self, other: Expr) -> Self {
        Expr::Implies(Box::new(self), Box::new(other))
    }

    pub fn eq(self, other: Expr) -> Self {
        Expr::Eq(Box::new(self), Box::new(other))
    }
}

impl fmt::Display for Expr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Expr::Lit(b) => write!(f, "{}", b),
            Expr::Var(v) => write!(f, "{}", v),
            Expr::Not(e) => write!(f, "!{}", e),
            Expr::And(l, r) => write!(f, "({} && {})", l, r),
            Expr::Or(l, r) => write!(f, "({} || {})", l, r),
            Expr::Xor(l, r) => write!(f, "({} ^ {})", l, r),
            Expr::Implies(l, r) => write!(f, "({} => {})", l, r),
            Expr::Eq(l, r) => write!(f, "({} == {})", l, r),
        }
    }
}

/// Statement in the imperative language
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Stmt {
    /// Skip (no-op)
    Skip,
    /// Assignment: var = expr
    Assign(Var, Expr),
    /// Conditional: if expr then stmts else stmts
    If {
        condition: Expr,
        then_body: Vec<Stmt>,
        else_body: Vec<Stmt>,
    },
    /// Loop: while expr do stmts
    While { condition: Expr, body: Vec<Stmt> },
    /// Assertion: assert expr
    Assert(Expr),
    /// Assume: assume expr (strengthen path condition)
    Assume(Expr),
}

// Constructors
impl Stmt {
    pub fn assign(var: impl Into<String>, expr: Expr) -> Self {
        Stmt::Assign(var.into(), expr)
    }

    pub fn if_then_else(cond: Expr, then_body: Vec<Stmt>, else_body: Vec<Stmt>) -> Self {
        Stmt::If {
            condition: cond,
            then_body,
            else_body,
        }
    }

    pub fn if_then(cond: Expr, then_body: Vec<Stmt>) -> Self {
        Stmt::If {
            condition: cond,
            then_body,
            else_body: vec![],
        }
    }

    pub fn while_do(cond: Expr, body: Vec<Stmt>) -> Self {
        Stmt::While { condition: cond, body }
    }

    pub fn assert(expr: Expr) -> Self {
        Stmt::Assert(expr)
    }

    pub fn assume(expr: Expr) -> Self {
        Stmt::Assume(expr)
    }
}

impl fmt::Display for Stmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.fmt_indent(f, 0)
    }
}

impl Stmt {
    fn fmt_indent(&self, f: &mut fmt::Formatter<'_>, indent: usize) -> fmt::Result {
        let ind = "  ".repeat(indent);
        match self {
            Stmt::Skip => writeln!(f, "{}skip;", ind),
            Stmt::Assign(v, e) => writeln!(f, "{}{} = {};", ind, v, e),
            Stmt::If {
                condition,
                then_body,
                else_body,
            } => {
                writeln!(f, "{}if {} {{", ind, condition)?;
                for stmt in then_body {
                    stmt.fmt_indent(f, indent + 1)?;
                }
                if !else_body.is_empty() {
                    writeln!(f, "{}}} else {{", ind)?;
                    for stmt in else_body {
                        stmt.fmt_indent(f, indent + 1)?;
                    }
                }
                writeln!(f, "{}}}", ind)
            }
            Stmt::While { condition, body } => {
                writeln!(f, "{}while {} {{", ind, condition)?;
                for stmt in body {
                    stmt.fmt_indent(f, indent + 1)?;
                }
                writeln!(f, "{}}}", ind)
            }
            Stmt::Assert(e) => writeln!(f, "{}assert {};", ind, e),
            Stmt::Assume(e) => writeln!(f, "{}assume {};", ind, e),
        }
    }
}

/// A program is a named sequence of statements
#[derive(Debug, Clone)]
pub struct Program {
    pub name: String,
    pub body: Vec<Stmt>,
}

impl Program {
    pub fn new(name: impl Into<String>, body: Vec<Stmt>) -> Self {
        Program { name: name.into(), body }
    }
}

impl fmt::Display for Program {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "program {} {{", self.name)?;
        for stmt in &self.body {
            stmt.fmt_indent(f, 1)?;
        }
        writeln!(f, "}}")
    }
}
