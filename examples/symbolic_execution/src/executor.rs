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
        let initial_state = SymbolicState::new(self.bdd);
        self.execute_from_state(stmt, initial_state)
    }

    /// Execute from a given initial state
    pub fn execute_from_state(&self, stmt: &Stmt, initial_state: SymbolicState) -> ExecutionResult {
        let mut result = ExecutionResult::new();
        let mut worklist: VecDeque<(Stmt, SymbolicState)> = VecDeque::new();
        worklist.push_back((stmt.clone(), initial_state));

        while let Some((current_stmt, mut state)) = worklist.pop_front() {
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

            match current_stmt {
                Stmt::Skip => {
                    result.final_states.push(state);
                }

                Stmt::Assign(ref var, ref expr) => {
                    let value = state.eval_expr(expr);
                    state.set(var.clone(), value);
                    result.final_states.push(state);
                }

                Stmt::Seq(ref s1, ref s2) => {
                    // Execute s1, then s2 for each resulting state
                    let intermediate_result = self.execute_from_state(s1, state);
                    for intermediate_state in intermediate_result.final_states {
                        worklist.push_back((*s2.clone(), intermediate_state));
                    }
                    // Propagate assertion failures
                    result.assertion_failures.extend(intermediate_result.assertion_failures);
                }

                Stmt::If(ref cond, ref then_branch, ref else_branch) => {
                    let cond_bdd = state.eval_expr(cond);

                    // Then branch: assume condition is true
                    let mut then_state = state.clone_state();
                    then_state.add_constraint(cond_bdd);
                    if then_state.is_feasible() {
                        worklist.push_back((*then_branch.clone(), then_state));
                    }

                    // Else branch: assume condition is false
                    let mut else_state = state;
                    else_state.add_constraint(self.bdd.apply_not(cond_bdd));
                    if else_state.is_feasible() {
                        worklist.push_back((*else_branch.clone(), else_state));
                    }
                }

                Stmt::While(ref cond, ref body) => {
                    // Simple loop unrolling
                    let mut unrolled = Stmt::Skip;
                    for _ in 0..self.config.max_loop_unroll {
                        // if cond { body; continue } else { break }
                        unrolled = Stmt::If(
                            cond.clone(),
                            Box::new(Stmt::Seq(body.clone(), Box::new(unrolled))),
                            Box::new(Stmt::Skip),
                        );
                    }
                    worklist.push_back((unrolled, state));
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
                        result.final_states.push(state);
                    }
                }

                Stmt::Assume(ref expr) => {
                    let assumption = state.eval_expr(expr);
                    state.add_constraint(assumption);
                    if state.is_feasible() {
                        result.final_states.push(state);
                    }
                }
            }
        }

        result
    }
}
