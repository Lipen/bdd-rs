//! Control Flow Graph representation for programs
//!
//! Converts imperative program statements into a graph for abstract interpretation.

use crate::language::{Expr, Predicate, Program, Stmt, Var};

/// Unique identifier for CFG nodes
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct NodeId(pub usize);

/// Labels on edges indicating the condition/action taken
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CfgEdgeLabel {
    /// Unconditional transition
    Seq,
    /// True branch of condition
    CondTrue(Predicate),
    /// False branch of condition
    CondFalse(Predicate),
    /// Assignment statement
    Assign(Var, Expr),
    /// Assume constraint
    Assume(Predicate),
    /// Assert property (may lead to error state)
    Assert(Predicate),
}

/// A node in the CFG
#[derive(Debug, Clone)]
pub struct CfgNode {
    pub id: NodeId,
    pub label: String,
    pub is_error: bool,
    pub is_final: bool,
}

/// Control Flow Graph
#[derive(Debug, Clone)]
pub struct ControlFlowGraph {
    pub nodes: Vec<CfgNode>,
    pub edges: Vec<(NodeId, NodeId, CfgEdgeLabel)>,
    pub entry: NodeId,
}

/// Builder for constructing CFGs
pub struct CfgBuilder {
    nodes: Vec<CfgNode>,
    edges: Vec<(NodeId, NodeId, CfgEdgeLabel)>,
    next_id: usize,
}

impl CfgBuilder {
    pub fn new() -> Self {
        let mut builder = CfgBuilder {
            nodes: Vec::new(),
            edges: Vec::new(),
            next_id: 0,
        };
        // Create entry node
        let _entry = builder.new_node("entry", false, false);
        builder
    }

    /// Create a new CFG node
    pub fn new_node(&mut self, label: &str, is_error: bool, is_final: bool) -> NodeId {
        let id = NodeId(self.next_id);
        self.next_id += 1;
        self.nodes.push(CfgNode {
            id,
            label: label.to_string(),
            is_error,
            is_final,
        });
        id
    }

    /// Add an edge between two nodes
    pub fn add_edge(&mut self, from: NodeId, to: NodeId, label: CfgEdgeLabel) {
        self.edges.push((from, to, label));
    }

    /// Build the final CFG
    pub fn build(self) -> ControlFlowGraph {
        let entry = NodeId(0);
        ControlFlowGraph {
            nodes: self.nodes,
            edges: self.edges,
            entry,
        }
    }
}

impl Default for CfgBuilder {
    fn default() -> Self {
        Self::new()
    }
}

/// Compile a program into a CFG
pub fn compile_to_cfg(prog: &Program) -> ControlFlowGraph {
    let mut builder = CfgBuilder::new();
    let entry = builder.entry();

    let mut current = entry;

    for stmt in prog {
        match stmt {
            Stmt::Assign(var, expr) => {
                let next = builder.new_node(&format!("{} := {}", var, expr), false, false);
                builder.add_edge(current, next, CfgEdgeLabel::Assign(*var, expr.clone()));
                current = next;
            }
            Stmt::Assume(pred) => {
                let next = builder.new_node(&format!("assume {}", pred), false, false);
                builder.add_edge(current, next, CfgEdgeLabel::Assume(pred.clone()));
                current = next;
            }
            Stmt::Assert(pred) => {
                let next = builder.new_node(&format!("assert {}", pred), false, false);
                let error = builder.new_node(&format!("ERROR: assert failed"), true, true);
                builder.add_edge(current, next, CfgEdgeLabel::Assert(pred.clone()));
                builder.add_edge(current, error, CfgEdgeLabel::Assert(pred.clone()));
                current = next;
            }
            Stmt::If(pred, then_stmts, else_stmts) => {
                // Build then branch
                let then_start = builder.new_node(&format!("if {} then", pred), false, false);
                builder.add_edge(current, then_start, CfgEdgeLabel::CondTrue(pred.clone()));

                let mut then_current = then_start;
                for s in then_stmts {
                    match s {
                        Stmt::Assign(var, expr) => {
                            let next = builder.new_node(&format!("{} := {}", var, expr), false, false);
                            builder.add_edge(then_current, next, CfgEdgeLabel::Assign(*var, expr.clone()));
                            then_current = next;
                        }
                        _ => {
                            // Simplified: nested if statements not fully handled
                        }
                    }
                }

                // Build else branch
                let else_start = builder.new_node(&format!("if {} else", pred), false, false);
                builder.add_edge(current, else_start, CfgEdgeLabel::CondFalse(pred.clone()));

                let mut else_current = else_start;
                for s in else_stmts {
                    match s {
                        Stmt::Assign(var, expr) => {
                            let next = builder.new_node(&format!("{} := {}", var, expr), false, false);
                            builder.add_edge(else_current, next, CfgEdgeLabel::Assign(*var, expr.clone()));
                            else_current = next;
                        }
                        _ => {
                            // Simplified
                        }
                    }
                }

                // Merge branches
                let merge = builder.new_node("merge", false, false);
                builder.add_edge(then_current, merge, CfgEdgeLabel::Seq);
                builder.add_edge(else_current, merge, CfgEdgeLabel::Seq);
                current = merge;
            }
        }
    }

    // Mark final node
    if let Some(node) = builder.nodes.get_mut(current.0) {
        node.is_final = true;
    }

    builder.build()
}

impl ControlFlowGraph {
    /// Get all successors of a node
    pub fn successors(&self, node: NodeId) -> Vec<(NodeId, CfgEdgeLabel)> {
        self.edges
            .iter()
            .filter(|(from, _, _)| *from == node)
            .map(|(_, to, label)| (*to, label.clone()))
            .collect()
    }

    /// Get all predecessors of a node
    pub fn predecessors(&self, node: NodeId) -> Vec<(NodeId, CfgEdgeLabel)> {
        self.edges
            .iter()
            .filter(|(_, to, _)| *to == node)
            .map(|(from, _, label)| (*from, label.clone()))
            .collect()
    }

    /// Find node by label (for debugging)
    pub fn find_node(&self, label: &str) -> Option<NodeId> {
        self.nodes.iter().find(|n| n.label == label).map(|n| n.id)
    }
}

// Helper to access entry node ID
impl CfgBuilder {
    fn entry(&self) -> NodeId {
        NodeId(0)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_cfg_builder() {
        let mut builder = CfgBuilder::new();
        let n1 = builder.new_node("n1", false, false);
        let n2 = builder.new_node("n2", false, true);
        builder.add_edge(n1, n2, CfgEdgeLabel::Seq);

        let cfg = builder.build();
        assert_eq!(cfg.nodes.len(), 3); // entry + n1 + n2
        assert_eq!(cfg.edges.len(), 2); // entry->n1 + n1->n2
    }
}
