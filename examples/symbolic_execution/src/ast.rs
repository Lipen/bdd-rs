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
    /// Sequence: stmt1; stmt2
    Seq(Box<Stmt>, Box<Stmt>),
    /// Assignment: var = expr
    Assign(Var, Expr),
    /// Conditional: if expr then stmt1 else stmt2
    If(Expr, Box<Stmt>, Box<Stmt>),
    /// Loop: while expr do stmt
    While(Expr, Box<Stmt>),
    /// Assertion: assert expr
    Assert(Expr),
    /// Assume: assume expr (strengthen path condition)
    Assume(Expr),
}

// Constructors
impl Stmt {
    pub fn seq(self, other: Stmt) -> Self {
        Stmt::Seq(Box::new(self), Box::new(other))
    }

    pub fn assign(var: impl Into<String>, expr: Expr) -> Self {
        Stmt::Assign(var.into(), expr)
    }

    pub fn if_then_else(cond: Expr, then_stmt: Stmt, else_stmt: Stmt) -> Self {
        Stmt::If(cond, Box::new(then_stmt), Box::new(else_stmt))
    }

    pub fn if_then(cond: Expr, then_stmt: Stmt) -> Self {
        Stmt::If(cond, Box::new(then_stmt), Box::new(Stmt::Skip))
    }

    pub fn while_do(cond: Expr, body: Stmt) -> Self {
        Stmt::While(cond, Box::new(body))
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
            Stmt::Seq(s1, s2) => {
                s1.fmt_indent(f, indent)?;
                s2.fmt_indent(f, indent)
            }
            Stmt::If(e, t, els) => {
                writeln!(f, "{}if {} {{", ind, e)?;
                t.fmt_indent(f, indent + 1)?;
                if **els != Stmt::Skip {
                    writeln!(f, "{}}} else {{", ind)?;
                    els.fmt_indent(f, indent + 1)?;
                }
                writeln!(f, "{}}}", ind)
            }
            Stmt::While(e, body) => {
                writeln!(f, "{}while {} {{", ind, e)?;
                body.fmt_indent(f, indent + 1)?;
                writeln!(f, "{}}}", ind)
            }
            Stmt::Assert(e) => writeln!(f, "{}assert {};", ind, e),
            Stmt::Assume(e) => writeln!(f, "{}assume {};", ind, e),
        }
    }
}

/// A program is just a statement with an optional name
#[derive(Debug, Clone)]
pub struct Program {
    pub name: String,
    pub stmt: Stmt,
}

impl Program {
    pub fn new(name: impl Into<String>, stmt: Stmt) -> Self {
        Program { name: name.into(), stmt }
    }
}

impl fmt::Display for Program {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "program {} {{", self.name)?;
        self.stmt.fmt_indent(f, 1)?;
        writeln!(f, "}}")
    }
}
