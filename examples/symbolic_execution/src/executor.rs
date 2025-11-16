//! Symbolic execution engine.
//!
//! This module implements symbolic execution for our imperative language.
//! It explores execution paths and tracks path conditions using BDDs.

use std::collections::HashSet;
use std::collections::VecDeque;

use bdd_rs::bdd::Bdd;

use crate::ast::{Expr, Var};
use crate::cfg::{BlockId, ControlFlowGraph, Instruction, Terminator};
use crate::counterexample::{extract_counterexample, CounterexampleConfig, TestCase};
use crate::state::SymbolicState;

/// Result of symbolic execution
#[derive(Debug, Clone)]
pub struct ExecutionResult {
    /// Final states reached (if execution completed normally)
    pub final_states: Vec<SymbolicState>,
    /// States where assertions failed
    pub assertion_failures: Vec<(SymbolicState, Expr)>,
    /// Counterexamples (test cases) for assertion failures
    pub counterexamples: Vec<(TestCase, Expr)>,
    /// Input variables inferred from the program
    pub input_variables: HashSet<Var>,
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
            counterexamples: Vec::new(),
            input_variables: HashSet::new(),
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
    /// Configuration for counterexample generation
    pub counterexample_config: CounterexampleConfig,
}

impl Default for ExecutionConfig {
    fn default() -> Self {
        ExecutionConfig {
            max_loop_unroll: 10,
            max_paths: 1000,
            counterexample_config: CounterexampleConfig::default(),
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

    /// Execute a CFG symbolically from an initial state
    pub fn execute(&self, cfg: &ControlFlowGraph, initial_state: SymbolicState) -> ExecutionResult {
        self.execute_with_inputs(cfg, initial_state, HashSet::new())
    }

    /// Execute with explicit input variables for counterexample generation
    pub fn execute_with_inputs(
        &self,
        cfg: &ControlFlowGraph,
        mut initial_state: SymbolicState,
        input_vars: HashSet<Var>,
    ) -> ExecutionResult {
        let mut result = ExecutionResult::new();

        // Mark input variables and initialize their symbolic values
        for var in &input_vars {
            initial_state.mark_as_input(var);
        }

        // Worklist: (current_block_id, state)
        let mut worklist: VecDeque<(BlockId, SymbolicState)> = VecDeque::new();
        worklist.push_back((cfg.entry, initial_state));

        while let Some((block_id, mut state)) = worklist.pop_front() {
            if result.paths_explored >= self.config.max_paths {
                eprintln!("Warning: Reached maximum path limit ({})", self.config.max_paths);
                break;
            }

            result.paths_explored += 1;

            if !state.is_feasible() {
                continue;
            }

            result.feasible_paths += 1;

            let block = match cfg.get_block(block_id) {
                Some(b) => b,
                None => {
                    eprintln!("Warning: Block {} not found", block_id);
                    continue;
                }
            };

            // Execute all instructions in the block
            let mut should_continue = true;
            for instruction in &block.instructions {
                match instruction {
                    Instruction::Assign(var, expr) => {
                        let value = state.eval_expr(expr);
                        state.set(var.clone(), value);
                    }
                    Instruction::Assume(expr) => {
                        let assumption = state.eval_expr(expr);
                        state.add_constraint(assumption);
                        if !state.is_feasible() {
                            should_continue = false;
                            break;
                        }
                    }
                    Instruction::Assert(expr) => {
                        let assertion = state.eval_expr(expr);
                        let failure_condition = self.bdd.apply_and(state.path_condition(), self.bdd.apply_not(assertion));

                        if !self.bdd.is_zero(failure_condition) {
                            result.assertion_failures.push((state.clone_state(), expr.clone()));
                        }

                        state.add_constraint(assertion);
                        if !state.is_feasible() {
                            should_continue = false;
                            break;
                        }
                    }
                    Instruction::Catch(catch_var) => {
                        // Catch instruction marks entry to catch block
                        // Bind catch variable to the thrown exception value
                        if let Some(var) = catch_var {
                            // Get the exception value that was thrown
                            if let Some(exception_value) = state.take_exception_value() {
                                state.set(var.clone(), exception_value);
                            } else {
                                // If no exception value was set (shouldn't happen), create symbolic
                                let exception_var = format!("_exception_{}", block_id);
                                let exception_bdd_var = state.get_or_create_index(&exception_var.into());
                                let exception_bdd = self.bdd.mk_var(exception_bdd_var);
                                state.set(var.clone(), exception_bdd);
                            }
                        }
                    }
                    Instruction::Throw(expr) => {
                        // Throw: evaluate exception value and jump to catch handler
                        let exception_value = state.eval_expr(expr);

                        // Jump to catch block if trap context exists
                        if let Some(trap_ctx) = &block.trap_context {
                            if let Some(catch_block) = trap_ctx.catch_target {
                                // Store the exception value in the state
                                let mut catch_state = state.clone_state();
                                catch_state.set_exception_value(exception_value);
                                worklist.push_back((catch_block, catch_state));
                            }
                        }
                        // After throw, don't continue normal flow
                        should_continue = false;
                        break;
                    }
                }
            }

            if !should_continue {
                continue;
            }

            // Process terminator
            match &block.terminator {
                Terminator::Return => {
                    result.final_states.push(state);
                }
                Terminator::Goto(target) => {
                    worklist.push_back((*target, state));
                }
                Terminator::Branch {
                    condition,
                    true_target,
                    false_target,
                } => {
                    let cond_bdd = state.eval_expr(condition);

                    // True branch
                    let mut true_state = state.clone_state();
                    true_state.add_constraint(cond_bdd);
                    if true_state.is_feasible() {
                        worklist.push_back((*true_target, true_state));
                    }

                    // False branch
                    let mut false_state = state;
                    false_state.add_constraint(self.bdd.apply_not(cond_bdd));
                    if false_state.is_feasible() {
                        worklist.push_back((*false_target, false_state));
                    }
                }
            }
        }

        // Generate counterexamples for assertion failures
        result.input_variables = input_vars.clone();
        for (state, expr) in &result.assertion_failures {
            if let Some(counterexample) = extract_counterexample(self.bdd, state, &input_vars, &self.config.counterexample_config) {
                result.counterexamples.push((counterexample, expr.clone()));
            }
        }

        result
    }
}
