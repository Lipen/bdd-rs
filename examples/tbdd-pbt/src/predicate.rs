//! Predicate abstraction for T-BDD.
//!
//! Predicates are atomic boolean conditions extracted from program branches.
//! Each predicate becomes a BDD variable, allowing us to reason about path
//! conditions symbolically.

use std::collections::HashMap;
use std::fmt;

use bdd_rs::bdd::Bdd;
use bdd_rs::reference::Ref;
use bdd_rs::types::Var as BddVar;

/// A program variable (identified by name for simplicity).
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ProgramVar(pub String);

impl ProgramVar {
    pub fn new(name: impl Into<String>) -> Self {
        Self(name.into())
    }
}

impl fmt::Display for ProgramVar {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

/// Right-hand side of a comparison: either a variable or a constant.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Operand {
    Var(ProgramVar),
    Const(i64),
}

impl fmt::Display for Operand {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Operand::Var(v) => write!(f, "{}", v),
            Operand::Const(c) => write!(f, "{}", c),
        }
    }
}

/// Comparison operators for predicates.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum CompareOp {
    Lt, // <
    Le, // <=
    Gt, // >
    Ge, // >=
    Eq, // ==
    Ne, // !=
}

impl CompareOp {
    /// Returns the negation of this operator.
    pub fn negate(self) -> Self {
        match self {
            CompareOp::Lt => CompareOp::Ge,
            CompareOp::Le => CompareOp::Gt,
            CompareOp::Gt => CompareOp::Le,
            CompareOp::Ge => CompareOp::Lt,
            CompareOp::Eq => CompareOp::Ne,
            CompareOp::Ne => CompareOp::Eq,
        }
    }
}

impl fmt::Display for CompareOp {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            CompareOp::Lt => write!(f, "<"),
            CompareOp::Le => write!(f, "<="),
            CompareOp::Gt => write!(f, ">"),
            CompareOp::Ge => write!(f, ">="),
            CompareOp::Eq => write!(f, "=="),
            CompareOp::Ne => write!(f, "!="),
        }
    }
}

/// A predicate is an atomic boolean condition: `lhs op rhs`.
///
/// Examples:
/// - `x < 0`
/// - `y >= x`
/// - `a == 42`
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Predicate {
    pub lhs: ProgramVar,
    pub op: CompareOp,
    pub rhs: Operand,
}

impl Predicate {
    pub fn new(lhs: ProgramVar, op: CompareOp, rhs: Operand) -> Self {
        Self { lhs, op, rhs }
    }

    /// Convenience: `var < const`
    pub fn lt(var: impl Into<String>, val: i64) -> Self {
        Self::new(ProgramVar::new(var), CompareOp::Lt, Operand::Const(val))
    }

    /// Convenience: `var <= const`
    pub fn le(var: impl Into<String>, val: i64) -> Self {
        Self::new(ProgramVar::new(var), CompareOp::Le, Operand::Const(val))
    }

    /// Convenience: `var > const`
    pub fn gt(var: impl Into<String>, val: i64) -> Self {
        Self::new(ProgramVar::new(var), CompareOp::Gt, Operand::Const(val))
    }

    /// Convenience: `var >= const`
    pub fn ge(var: impl Into<String>, val: i64) -> Self {
        Self::new(ProgramVar::new(var), CompareOp::Ge, Operand::Const(val))
    }

    /// Convenience: `var == const`
    pub fn eq(var: impl Into<String>, val: i64) -> Self {
        Self::new(ProgramVar::new(var), CompareOp::Eq, Operand::Const(val))
    }

    /// Convenience: `var != const`
    pub fn ne(var: impl Into<String>, val: i64) -> Self {
        Self::new(ProgramVar::new(var), CompareOp::Ne, Operand::Const(val))
    }

    /// Convenience: `var1 < var2`
    pub fn lt_var(var1: impl Into<String>, var2: impl Into<String>) -> Self {
        Self::new(ProgramVar::new(var1), CompareOp::Lt, Operand::Var(ProgramVar::new(var2)))
    }

    /// Convenience: `var1 > var2`
    pub fn gt_var(var1: impl Into<String>, var2: impl Into<String>) -> Self {
        Self::new(ProgramVar::new(var1), CompareOp::Gt, Operand::Var(ProgramVar::new(var2)))
    }

    /// Convenience: `var1 == var2`
    pub fn eq_var(var1: impl Into<String>, var2: impl Into<String>) -> Self {
        Self::new(ProgramVar::new(var1), CompareOp::Eq, Operand::Var(ProgramVar::new(var2)))
    }

    /// Returns a predicate representing the negation.
    pub fn negate(&self) -> Self {
        Self {
            lhs: self.lhs.clone(),
            op: self.op.negate(),
            rhs: self.rhs.clone(),
        }
    }

    /// Get all program variables mentioned in this predicate.
    pub fn variables(&self) -> Vec<&ProgramVar> {
        let mut vars = vec![&self.lhs];
        if let Operand::Var(v) = &self.rhs {
            vars.push(v);
        }
        vars
    }
}

impl fmt::Display for Predicate {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} {} {}", self.lhs, self.op, self.rhs)
    }
}

/// A literal is a predicate with a polarity (positive or negative).
#[derive(Debug, Clone)]
pub struct Literal {
    pub predicate: Predicate,
    pub positive: bool,
}

impl Literal {
    pub fn pos(predicate: Predicate) -> Self {
        Self { predicate, positive: true }
    }

    pub fn neg(predicate: Predicate) -> Self {
        Self {
            predicate,
            positive: false,
        }
    }

    /// Get the effective predicate (accounting for polarity).
    pub fn effective_predicate(&self) -> Predicate {
        if self.positive {
            self.predicate.clone()
        } else {
            self.predicate.negate()
        }
    }
}

impl fmt::Display for Literal {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.positive {
            write!(f, "{}", self.predicate)
        } else {
            write!(f, "¬({})", self.predicate)
        }
    }
}

/// The predicate universe maps predicates to BDD variables.
///
/// This is the bridge between the program's boolean conditions and the BDD
/// representation of path conditions.
pub struct PredicateUniverse {
    /// Map from predicate to its BDD variable.
    pred_to_var: HashMap<Predicate, BddVar>,
}

impl PredicateUniverse {
    pub fn new() -> Self {
        Self {
            pred_to_var: HashMap::new(),
        }
    }

    /// Register a predicate and return its BDD variable.
    ///
    /// If the predicate already exists, returns the existing variable.
    pub fn register(&mut self, pred: Predicate, bdd: &Bdd) -> BddVar {
        *self.pred_to_var.entry(pred).or_insert_with(|| bdd.allocate_variable())
    }

    /// Get the BDD variable for a predicate, if registered.
    pub fn get_var(&self, pred: &Predicate) -> Option<BddVar> {
        self.pred_to_var.get(pred).copied()
    }

    /// Get the predicate for a BDD variable.
    pub fn get_predicate(&self, var: BddVar) -> Option<&Predicate> {
        self.pred_to_var.iter().find(|(_, &v)| v == var).map(|(pred, _)| pred)
    }

    /// Get all registered predicates.
    pub fn predicates(&self) -> impl Iterator<Item = &Predicate> {
        self.pred_to_var.keys()
    }

    /// Number of predicates.
    pub fn len(&self) -> usize {
        self.pred_to_var.len()
    }

    /// Check if empty.
    pub fn is_empty(&self) -> bool {
        self.pred_to_var.is_empty()
    }

    /// Create a BDD reference for a literal (predicate with polarity).
    pub fn literal_to_bdd(&self, lit: &Literal, bdd: &Bdd) -> Option<Ref> {
        let var = self.get_var(&lit.predicate)?;
        let bdd_var = bdd.mk_var(var);
        Some(if lit.positive { bdd_var } else { -bdd_var })
    }

    /// Get all program variables mentioned across all predicates.
    pub fn all_program_variables(&self) -> Vec<ProgramVar> {
        let mut vars: Vec<ProgramVar> = self.predicates().flat_map(|p| p.variables().into_iter().cloned()).collect();
        vars.sort_by(|a, b| a.0.cmp(&b.0));
        vars.dedup();
        vars
    }
}

impl Default for PredicateUniverse {
    fn default() -> Self {
        Self::new()
    }
}

impl fmt::Debug for PredicateUniverse {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut predicates = self.predicates().collect::<Vec<_>>();
        predicates.sort_by_key(|p| p.to_string());
        f.debug_struct("PredicateUniverse").field("predicates", &predicates).finish()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_predicate_display() {
        let p1 = Predicate::lt("x", 0);
        assert_eq!(p1.to_string(), "x < 0");

        let p2 = Predicate::gt_var("y", "x");
        assert_eq!(p2.to_string(), "y > x");

        let p3 = Predicate::eq("z", 42);
        assert_eq!(p3.to_string(), "z == 42");
    }

    #[test]
    fn test_predicate_negation() {
        let p = Predicate::lt("x", 0);
        let neg = p.negate();
        assert_eq!(neg.op, CompareOp::Ge);
        assert_eq!(neg.to_string(), "x >= 0");
    }

    #[test]
    fn test_predicate_universe() {
        let bdd = Bdd::default();
        let mut universe = PredicateUniverse::new();

        let p1 = Predicate::lt("x", 0);
        let p2 = Predicate::gt_var("y", "x");

        let v1 = universe.register(p1.clone(), &bdd);
        let v2 = universe.register(p2.clone(), &bdd);

        assert_eq!(v1.id(), 1);
        assert_eq!(v2.id(), 2);

        // Re-registering returns the same variable
        let v1_again = universe.register(p1.clone(), &bdd);
        assert_eq!(v1, v1_again);

        assert_eq!(universe.len(), 2);
    }
}
