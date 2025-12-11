//! SDD-based abstract interpreter for program analysis
//!
//! Executes programs over abstract states represented as SDDs,
//! computing reachable states and checking assertions.

use std::collections::HashMap;

use crate::bit_encoding::BitEncoding;
use crate::cfg::{compile_to_cfg, CfgEdgeLabel, ControlFlowGraph, NodeId};
use crate::language::{program_vars, Program};
use crate::sdd_domain::SddAbstractState;
use crate::vtree_strategy::VtreeStrategy;

/// Main abstract interpreter using SDD states
pub struct SddAbstractInterpreter {
    #[allow(dead_code)]
    program: Program,
    cfg: ControlFlowGraph,
    encoding: BitEncoding,
    vtree_strategy: VtreeStrategy,
    /// Maps CFG nodes to their abstract state
    node_states: HashMap<NodeId, SddAbstractState>,
}

impl SddAbstractInterpreter {
    /// Create a new abstract interpreter for a program
    pub fn new(program: &Program, vtree_strategy: VtreeStrategy) -> Self {
        let cfg = compile_to_cfg(program);
        let vars = program_vars(program);
        let encoding = BitEncoding::new(&vars);

        SddAbstractInterpreter {
            program: program.clone(),
            cfg,
            encoding,
            vtree_strategy,
            node_states: HashMap::new(),
        }
    }

    /// Run abstract interpretation analysis
    pub fn analyze(&mut self) -> InterpreterResult {
        let mut result = InterpreterResult {
            vtree_strategy: self.vtree_strategy,
            initial_state_size: 0,
            final_state_size: 0,
            total_states_computed: 0,
            assertions_safe: Vec::new(),
            assertions_violated: Vec::new(),
            max_state_size: 0,
        };

        // Initialize entry state
        let mut entry_state = SddAbstractState::top(self.encoding.clone());
        result.initial_state_size = entry_state.size;
        result.max_state_size = entry_state.size;

        // Worklist algorithm for fixed-point computation
        let mut worklist = vec![self.cfg.entry];
        let mut visited = std::collections::HashSet::new();

        while let Some(node_id) = worklist.pop() {
            if visited.contains(&node_id) {
                continue;
            }
            visited.insert(node_id);
            result.total_states_computed += 1;

            // Get or compute state at this node
            let node_state = if node_id == self.cfg.entry {
                entry_state.clone()
            } else {
                self.node_states
                    .get(&node_id)
                    .cloned()
                    .unwrap_or_else(|| SddAbstractState::bottom(self.encoding.clone()))
            };

            // Process outgoing edges
            for (succ_id, edge_label) in self.cfg.successors(node_id) {
                let succ_state = match &edge_label {
                    CfgEdgeLabel::Seq => node_state.clone(),
                    CfgEdgeLabel::Assign(var, expr) => node_state.assign(*var, expr),
                    CfgEdgeLabel::Assume(pred) => node_state.assume(pred),
                    CfgEdgeLabel::Assert(pred) => {
                        // Check if assertion can be violated
                        let violated = node_state.assume(pred).num_models < node_state.num_models;
                        if violated {
                            result.assertions_violated.push(format!("Assert {} at node {}", pred, node_id.0));
                        } else {
                            result.assertions_safe.push(format!("Assert {} at node {}", pred, node_id.0));
                        }
                        node_state.clone()
                    }
                    CfgEdgeLabel::CondTrue(pred) => node_state.assume(pred),
                    CfgEdgeLabel::CondFalse(pred) => {
                        // Assume negation
                        node_state.assume(&crate::language::Predicate::Not(Box::new(pred.clone())))
                    }
                };

                // Update successor state
                let old_state = self.node_states.get(&succ_id).cloned();
                let new_state = match old_state {
                    Some(s) => s.join(&succ_state),
                    None => succ_state,
                };

                // Track maximum state size
                if new_state.size > result.max_state_size {
                    result.max_state_size = new_state.size;
                }

                self.node_states.insert(succ_id, new_state);
                worklist.push(succ_id);
            }

            // Update entry state for next iteration
            if node_id == self.cfg.entry {
                entry_state = self.node_states.get(&self.cfg.entry).cloned().unwrap_or(entry_state);
            }
        }

        // Find final state
        if let Some(final_node) = self.cfg.nodes.iter().find(|n| n.is_final) {
            if let Some(state) = self.node_states.get(&final_node.id) {
                result.final_state_size = state.size;
            }
        }

        result
    }
}

/// Result of abstract interpretation
#[derive(Debug, Clone)]
pub struct InterpreterResult {
    pub vtree_strategy: VtreeStrategy,
    pub initial_state_size: usize,
    pub final_state_size: usize,
    pub total_states_computed: usize,
    pub assertions_safe: Vec<String>,
    pub assertions_violated: Vec<String>,
    pub max_state_size: usize,
}

impl InterpreterResult {
    /// Print a human-readable report
    pub fn print_report(&self) {
        println!("\n📊 Abstract Interpretation Results");
        println!("━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━");
        println!("VTree Strategy: {}", self.vtree_strategy);
        println!("Initial state size: {}", self.initial_state_size);
        println!("Final state size: {}", self.final_state_size);
        println!("Max state size: {}", self.max_state_size);
        println!("Total states computed: {}", self.total_states_computed);

        if !self.assertions_safe.is_empty() {
            println!("\n✓ Safe assertions:");
            for a in &self.assertions_safe {
                println!("  • {}", a);
            }
        }

        if !self.assertions_violated.is_empty() {
            println!("\n✗ Potentially violated assertions:");
            for a in &self.assertions_violated {
                println!("  • {}", a);
            }
        } else {
            println!("\n✓ All assertions are safe!");
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::language::{Expr, Stmt, Var};

    #[test]
    fn test_interpreter_creation() {
        let prog = vec![Stmt::Assign(Var::new(1), Expr::Const(0))];
        let interpreter = SddAbstractInterpreter::new(&prog, VtreeStrategy::Balanced);
        assert_eq!(interpreter.encoding.num_sdd_vars(), 3);
    }
}
