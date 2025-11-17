//! Counterexample generation and test case synthesis.
//!
//! This module provides infrastructure for extracting concrete test cases from
//! symbolic execution results. A test case consists of concrete values for input
//! variables that trigger specific execution paths (e.g., assertion failures).

use std::collections::{HashMap, HashSet};

use bdd_rs::bdd::Bdd;

use crate::ast::Var;
use crate::state::SymbolicState;

/// Represents a concrete test case: assignments to input variables
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TestCase {
    /// Input variable assignments
    pub inputs: HashMap<Var, bool>,
    /// Additional metadata
    pub metadata: TestCaseMetadata,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TestCaseMetadata {
    /// Purpose of this test case
    pub purpose: TestCasePurpose,
    /// Human-readable description
    pub description: Option<String>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TestCasePurpose {
    /// Triggers an assertion failure
    AssertionViolation,
    /// Covers a specific path
    PathCoverage,
    /// Explores a particular branch
    BranchCoverage,
}

impl TestCase {
    pub fn new(inputs: HashMap<Var, bool>, purpose: TestCasePurpose) -> Self {
        TestCase {
            inputs,
            metadata: TestCaseMetadata {
                purpose,
                description: None,
            },
        }
    }

    pub fn with_description(mut self, description: String) -> Self {
        self.metadata.description = Some(description);
        self
    }

    /// Check if this test case assigns a value to the given variable
    pub fn has_input(&self, var: &Var) -> bool {
        self.inputs.contains_key(var)
    }

    /// Get the assigned value for an input variable
    pub fn get_input(&self, var: &Var) -> Option<bool> {
        self.inputs.get(var).copied()
    }
}

/// Configuration for counterexample generation
#[derive(Debug, Clone)]
pub struct CounterexampleConfig {
    /// Whether to minimize test cases (assign only necessary inputs)
    pub minimize: bool,
    /// Prefer specific values (e.g., false over true) for don't-care inputs
    pub prefer_false: bool,
}

impl Default for CounterexampleConfig {
    fn default() -> Self {
        CounterexampleConfig {
            minimize: true,
            prefer_false: true,
        }
    }
}

/// Extract a counterexample (test case) from a symbolic state
///
/// This function analyzes the path condition and determines concrete values
/// for input variables that would lead to this state being reached.
///
/// IMPORTANT: Uses the original symbolic values of inputs (before mutations),
/// not their current values in the store.
pub fn extract_counterexample(
    bdd: &Bdd,
    state: &SymbolicState,
    input_vars: &HashSet<Var>,
    config: &CounterexampleConfig,
) -> Option<TestCase> {
    let path_condition = state.path_condition();

    // Check if the path is feasible
    if bdd.is_zero(path_condition) {
        return None;
    }

    // Extract a satisfying assignment from the BDD
    // We need to get concrete values for all input variables
    let mut inputs = HashMap::new();

    // For each input variable, determine its ORIGINAL value under the path condition
    // We use the input's symbolic value (BDD variable), not its current store value
    for var in input_vars {
        if let Some(input_symbolic_val) = state.get_input_symbolic_value(var) {
            // Check if this input's original symbolic value is constrained by the path condition
            let val_and_pc = bdd.apply_and(input_symbolic_val, path_condition);
            let is_must_true = val_and_pc == path_condition;
            let is_must_false = bdd.is_zero(val_and_pc);

            if is_must_true {
                inputs.insert(var.clone(), true);
            } else if is_must_false {
                inputs.insert(var.clone(), false);
            } else {
                // Variable is unconstrained - pick a default value
                let default_value = if config.prefer_false { false } else { true };
                inputs.insert(var.clone(), default_value);
            }
        } else {
            // Input wasn't marked as such - fall back to current value
            if let Some(concrete_value) = state.get_concrete_value(var) {
                inputs.insert(var.clone(), concrete_value);
            } else {
                let default_value = if config.prefer_false { false } else { true };
                inputs.insert(var.clone(), default_value);
            }
        }
    }

    Some(TestCase::new(inputs, TestCasePurpose::AssertionViolation))
}

/// Extract counterexamples for all assertion failures
pub fn extract_all_counterexamples(
    bdd: &Bdd,
    states: &[(SymbolicState, crate::ast::Expr)],
    input_vars: &HashSet<Var>,
    config: &CounterexampleConfig,
) -> Vec<(TestCase, crate::ast::Expr)> {
    states
        .iter()
        .filter_map(|(state, expr)| extract_counterexample(bdd, state, input_vars, config).map(|tc| (tc, expr.clone())))
        .collect()
}

/// Infer input variables from a program
///
/// Input variables are those that:
/// 1. Are used before being assigned
/// 2. Appear in conditions before being defined
///
/// This is a simple heuristic - in practice, users might want to explicitly
/// declare input variables.
pub fn infer_input_variables(program: &crate::ast::Program) -> HashSet<Var> {
    let mut inputs = HashSet::new();
    let mut assigned = HashSet::new();

    fn collect_vars(stmts: &[crate::ast::Stmt], inputs: &mut HashSet<Var>, assigned: &mut HashSet<Var>) {
        for stmt in stmts {
            match stmt {
                crate::ast::Stmt::Assign(var, expr) => {
                    // First collect variables used in the expression
                    collect_expr_vars(expr, inputs, assigned);
                    // Then mark this variable as assigned
                    assigned.insert(var.clone());
                }
                crate::ast::Stmt::If {
                    condition,
                    then_body,
                    else_body,
                } => {
                    collect_expr_vars(condition, inputs, assigned);
                    collect_vars(then_body, inputs, assigned);
                    if !else_body.is_empty() {
                        collect_vars(else_body, inputs, assigned);
                    }
                }
                crate::ast::Stmt::While { condition, body } => {
                    collect_expr_vars(condition, inputs, assigned);
                    collect_vars(body, inputs, assigned);
                }
                crate::ast::Stmt::Assert(expr) | crate::ast::Stmt::Assume(expr) => {
                    collect_expr_vars(expr, inputs, assigned);
                }
                crate::ast::Stmt::Try {
                    try_body,
                    catch_var: _,
                    catch_body,
                    finally_body,
                } => {
                    collect_vars(try_body, inputs, assigned);
                    if !catch_body.is_empty() {
                        collect_vars(catch_body, inputs, assigned);
                    }
                    if !finally_body.is_empty() {
                        collect_vars(finally_body, inputs, assigned);
                    }
                }
                crate::ast::Stmt::Throw(expr) => {
                    collect_expr_vars(expr, inputs, assigned);
                }
                crate::ast::Stmt::Skip => {}
            }
        }
    }

    fn collect_expr_vars(expr: &crate::ast::Expr, inputs: &mut HashSet<Var>, assigned: &HashSet<Var>) {
        match expr {
            crate::ast::Expr::Var(v) => {
                // If variable is used before being assigned, it's an input
                if !assigned.contains(v) {
                    inputs.insert(v.clone());
                }
            }
            crate::ast::Expr::Lit(_) => {}
            crate::ast::Expr::Not(e) => collect_expr_vars(e, inputs, assigned),
            crate::ast::Expr::And(l, r)
            | crate::ast::Expr::Or(l, r)
            | crate::ast::Expr::Xor(l, r)
            | crate::ast::Expr::Implies(l, r)
            | crate::ast::Expr::Eq(l, r) => {
                collect_expr_vars(l, inputs, assigned);
                collect_expr_vars(r, inputs, assigned);
            }
        }
    }

    collect_vars(&program.body, &mut inputs, &mut assigned);
    inputs
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::{Expr, Program, Stmt};

    #[test]
    fn test_infer_input_variables() {
        // if x { y = true } else { y = false }; assert (x == y)
        let program = Program::new(
            "branch",
            vec![
                Stmt::if_then_else(
                    Expr::var("x"),
                    vec![Stmt::assign("y", Expr::Lit(true))],
                    vec![Stmt::assign("y", Expr::Lit(false))],
                ),
                Stmt::assert(Expr::var("x").eq(Expr::var("y"))),
            ],
        );

        let inputs = infer_input_variables(&program);
        assert_eq!(inputs.len(), 1);
        assert!(inputs.contains(&Var::from("x")));
    }

    #[test]
    fn test_infer_multiple_inputs() {
        // z = x ^ y; assert (z == ((x || y) && !(x && y)))
        let program = Program::new(
            "xor",
            vec![
                Stmt::assign("z", Expr::var("x").xor(Expr::var("y"))),
                Stmt::assert(Expr::var("z").eq(Expr::var("x").or(Expr::var("y")).and(Expr::var("x").and(Expr::var("y")).not()))),
            ],
        );

        let inputs = infer_input_variables(&program);
        assert_eq!(inputs.len(), 2);
        assert!(inputs.contains(&Var::from("x")));
        assert!(inputs.contains(&Var::from("y")));
    }

    #[test]
    fn test_assigned_not_input() {
        // x = true; y = x; assert y
        let program = Program::new(
            "simple",
            vec![
                Stmt::assign("x", Expr::Lit(true)),
                Stmt::assign("y", Expr::var("x")),
                Stmt::assert(Expr::var("y")),
            ],
        );

        let inputs = infer_input_variables(&program);
        assert_eq!(inputs.len(), 0); // No inputs - all variables assigned before use
    }
}
