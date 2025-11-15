//! Symbolic execution engine.
//!
//! This module implements symbolic execution for our imperative language.
//! It explores execution paths and tracks path conditions using BDDs.

use std::collections::VecDeque;

use bdd_rs::bdd::Bdd;

use crate::ast::{Expr, Stmt};
use crate::state::SymbolicState;

/// Result of symbolic execution
#[derive(Debug, Clone)]
pub struct ExecutionResult {
    /// Final states reached (if execution completed normally)
    pub final_states: Vec<SymbolicState>,
    /// States where assertions failed
    pub assertion_failures: Vec<(SymbolicState, Expr)>,
    /// Total number of paths explored
    pub paths_explored: usize,
    /// Number of feasible paths
    pub feasible_paths: usize,
}

impl ExecutionResult {
    pub fn new() -> Self {
        ExecutionResult {
            final_states: Vec::new(),
            assertion_failures: Vec::new(),
            paths_explored: 0,
            feasible_paths: 0,
        }
    }

    /// Check if all assertions passed
    pub fn all_assertions_passed(&self) -> bool {
        self.assertion_failures.is_empty()
    }

    /// Get number of assertion failures
    pub fn num_failures(&self) -> usize {
        self.assertion_failures.len()
    }
}

impl Default for ExecutionResult {
    fn default() -> Self {
        Self::new()
    }
}

/// Configuration for symbolic execution
#[derive(Debug, Clone)]
pub struct ExecutionConfig {
    /// Maximum number of loop iterations to unroll
    pub max_loop_unroll: usize,
    /// Maximum number of paths to explore
    pub max_paths: usize,
}

impl Default for ExecutionConfig {
    fn default() -> Self {
        ExecutionConfig {
            max_loop_unroll: 10,
            max_paths: 1000,
        }
    }
}

/// Symbolic executor
pub struct SymbolicExecutor<'a> {
    bdd: &'a Bdd,
    config: ExecutionConfig,
}

impl<'a> SymbolicExecutor<'a> {
    pub fn new(bdd: &'a Bdd) -> Self {
        SymbolicExecutor {
            bdd,
            config: ExecutionConfig::default(),
        }
    }

    pub fn with_config(bdd: &'a Bdd, config: ExecutionConfig) -> Self {
        SymbolicExecutor { bdd, config }
    }

    /// Execute a statement symbolically from an initial state
    pub fn execute(&self, stmt: &Stmt) -> ExecutionResult {
        self.execute_stmts(&[stmt.clone()])
    }

    /// Execute a list of statements symbolically
    pub fn execute_stmts(&self, stmts: &[Stmt]) -> ExecutionResult {
        let initial_state = SymbolicState::new(self.bdd);
        self.execute_stmts_from_state(stmts, initial_state)
    }

    /// Execute from a given initial state
    pub fn execute_from_state(&self, stmt: &Stmt, initial_state: SymbolicState) -> ExecutionResult {
        self.execute_stmts_from_state(&[stmt.clone()], initial_state)
    }

    /// Execute a list of statements from a given initial state
    pub fn execute_stmts_from_state(&self, stmts: &[Stmt], initial_state: SymbolicState) -> ExecutionResult {
        let mut result = ExecutionResult::new();
        let mut worklist: VecDeque<(Vec<Stmt>, SymbolicState)> = VecDeque::new();
        worklist.push_back((stmts.to_vec(), initial_state));

        while let Some((current_stmts, mut state)) = worklist.pop_front() {
            if result.paths_explored >= self.config.max_paths {
                eprintln!("Warning: Reached maximum path limit ({})", self.config.max_paths);
                break;
            }

            result.paths_explored += 1;

            if !state.is_feasible() {
                // Infeasible path, skip
                continue;
            }

            result.feasible_paths += 1;

            // Process statements one by one
            if current_stmts.is_empty() {
                // Empty statement list - we're done with this path
                result.final_states.push(state);
                continue;
            }

            let (first, rest) = current_stmts.split_first().unwrap();

            match first {
                Stmt::Skip => {
                    // Just continue with remaining statements
                    worklist.push_back((rest.to_vec(), state));
                }

                Stmt::Assign(ref var, ref expr) => {
                    let value = state.eval_expr(expr);
                    state.set(var.clone(), value);
                    worklist.push_back((rest.to_vec(), state));
                }

                Stmt::If {
                    ref condition,
                    ref then_body,
                    ref else_body,
                } => {
                    let cond_bdd = state.eval_expr(condition);

                    // Then branch: assume condition is true
                    let mut then_state = state.clone_state();
                    then_state.add_constraint(cond_bdd);
                    if then_state.is_feasible() {
                        // Execute then_body, then continue with rest
                        let mut then_stmts = then_body.clone();
                        then_stmts.extend_from_slice(rest);
                        worklist.push_back((then_stmts, then_state));
                    }

                    // Else branch: assume condition is false
                    let mut else_state = state;
                    else_state.add_constraint(self.bdd.apply_not(cond_bdd));
                    if else_state.is_feasible() {
                        // Execute else_body, then continue with rest
                        let mut else_stmts = else_body.clone();
                        else_stmts.extend_from_slice(rest);
                        worklist.push_back((else_stmts, else_state));
                    }
                }

                Stmt::While { ref condition, ref body } => {
                    // Simple loop unrolling: replace while with nested if statements
                    let mut unrolled_stmts = vec![];

                    // Build: if cond { body; ... nested ... } else { skip }
                    let mut current_if = Stmt::Skip;
                    for _ in 0..self.config.max_loop_unroll {
                        current_if = Stmt::if_then_else(
                            condition.clone(),
                            {
                                let mut body_stmts = body.clone();
                                body_stmts.push(current_if);
                                body_stmts
                            },
                            vec![],
                        );
                    }

                    unrolled_stmts.push(current_if);
                    unrolled_stmts.extend_from_slice(rest);
                    worklist.push_back((unrolled_stmts, state));
                }

                Stmt::Assert(ref expr) => {
                    let assertion = state.eval_expr(expr);
                    // Check if assertion can fail
                    let failure_condition = self.bdd.apply_and(state.path_condition(), self.bdd.apply_not(assertion));

                    if !self.bdd.is_zero(failure_condition) {
                        // Assertion can fail on this path
                        result.assertion_failures.push((state.clone_state(), expr.clone()));
                    }

                    // Continue execution assuming assertion holds
                    state.add_constraint(assertion);
                    if state.is_feasible() {
                        worklist.push_back((rest.to_vec(), state));
                    }
                }

                Stmt::Assume(ref expr) => {
                    let assumption = state.eval_expr(expr);
                    state.add_constraint(assumption);
                    if state.is_feasible() {
                        worklist.push_back((rest.to_vec(), state));
                    }
                }

                Stmt::Try {
                    ref try_body,
                    ref catch_var,
                    ref catch_body,
                    ref finally_body,
                } => {
                    // Execute try block - if throw occurs, execution jumps to catch
                    // For now, we explore both paths:
                    // 1. Normal execution (no exception)
                    // 2. Exception path (if catch exists)

                    // Normal path: try -> finally -> rest
                    let mut normal_stmts = try_body.clone();
                    normal_stmts.extend_from_slice(finally_body);
                    normal_stmts.extend_from_slice(rest);
                    worklist.push_back((normal_stmts, state.clone_state()));

                    // Exception path: catch -> finally -> rest (if catch exists)
                    if !catch_body.is_empty() {
                        let mut exception_state = state;
                        // If there's a catch variable, assign some symbolic exception value
                        if let Some(var) = catch_var {
                            // Create a fresh symbolic variable for the exception
                            let exception_var = format!("_exception_{}", result.assertion_failures.len());
                            let exception_idx = exception_state.var_map_mut().get_or_create(&exception_var.into());
                            let exception_bdd = self.bdd.mk_var(exception_idx);
                            exception_state.set(var.clone(), exception_bdd);
                        }
                        let mut exception_stmts = catch_body.clone();
                        exception_stmts.extend_from_slice(finally_body);
                        exception_stmts.extend_from_slice(rest);
                        worklist.push_back((exception_stmts, exception_state));
                    }
                }

                Stmt::Throw(ref expr) => {
                    // Throw terminates current execution path
                    // In a real implementation, this would propagate to the nearest catch
                    // For now, we treat it as a path terminator
                    // The exception value is evaluated but not used further
                    let _exception_value = state.eval_expr(expr);
                    // Path ends here - throw propagates upward
                    // TODO: If we're in a try-catch context, jump to catch handler
                }
            }
        }

        result
    }
}
