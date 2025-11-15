//! Visualization of programs as DOT graphs.
//!
//! This module provides functions to visualize programs as:
//! - Abstract Syntax Trees (AST)
//! - Control Flow Graphs (CFG)

use std::fmt::Write;

use crate::ast::{Expr, Stmt};
use crate::cfg::ControlFlowGraph;

/// Generate DOT representation of an AST
pub fn ast_to_dot(stmts: &[Stmt], name: &str) -> String {
    let mut dot = String::new();
    writeln!(dot, "digraph AST_{} {{", name.replace(' ', "_")).unwrap();
    writeln!(dot, "  node [shape=box, style=rounded];").unwrap();
    writeln!(dot, "  rankdir=TB;").unwrap();
    writeln!(dot).unwrap();

    let mut counter = 0;

    if stmts.is_empty() {
        // Empty program
        writeln!(dot, "  n0 [label=\"empty\", fillcolor=lightgray, style=\"filled,rounded\"];").unwrap();
    } else if stmts.len() == 1 {
        // Single statement
        ast_stmt_to_dot(&stmts[0], &mut dot, &mut counter, None);
    } else {
        // Multiple statements - create a root node
        let root = counter;
        counter += 1;
        writeln!(
            dot,
            "  n{} [label=\"program\", fillcolor=lightyellow, style=\"filled,rounded\"];",
            root
        )
        .unwrap();

        for stmt in stmts {
            let stmt_id = ast_stmt_to_dot(stmt, &mut dot, &mut counter, Some(root));
            writeln!(dot, "  n{} -> n{};", root, stmt_id).unwrap();
        }
    }

    writeln!(dot, "}}").unwrap();
    dot
}

fn ast_stmt_to_dot(stmt: &Stmt, dot: &mut String, counter: &mut usize, parent: Option<usize>) -> usize {
    let id = *counter;
    *counter += 1;

    match stmt {
        Stmt::Skip => {
            writeln!(dot, "  n{} [label=\"skip\", fillcolor=lightgray, style=\"filled,rounded\"];", id).unwrap();
        }
        Stmt::Assign(var, expr) => {
            writeln!(
                dot,
                "  n{} [label=\"{} :=\", fillcolor=lightblue, style=\"filled,rounded\"];",
                id, var
            )
            .unwrap();
            let expr_id = ast_expr_to_dot(expr, dot, counter);
            writeln!(dot, "  n{} -> n{} [label=\"value\"];", id, expr_id).unwrap();
        }
        Stmt::If {
            condition,
            then_body,
            else_body,
        } => {
            writeln!(dot, "  n{} [label=\"if\", fillcolor=lightgreen, style=\"filled,rounded\"];", id).unwrap();
            let cond_id = ast_expr_to_dot(condition, dot, counter);
            writeln!(dot, "  n{} -> n{} [label=\"cond\"];", id, cond_id).unwrap();

            // Then body
            if !then_body.is_empty() {
                let then_id = ast_stmts_to_dot(then_body, dot, counter, Some(id), "then");
                writeln!(dot, "  n{} -> n{} [label=\"then\"];", id, then_id).unwrap();
            }

            // Else body
            if !else_body.is_empty() {
                let else_id = ast_stmts_to_dot(else_body, dot, counter, Some(id), "else");
                writeln!(dot, "  n{} -> n{} [label=\"else\"];", id, else_id).unwrap();
            }
        }
        Stmt::While { condition, body } => {
            writeln!(dot, "  n{} [label=\"while\", fillcolor=orange, style=\"filled,rounded\"];", id).unwrap();
            let cond_id = ast_expr_to_dot(condition, dot, counter);
            writeln!(dot, "  n{} -> n{} [label=\"cond\"];", id, cond_id).unwrap();

            if !body.is_empty() {
                let body_id = ast_stmts_to_dot(body, dot, counter, Some(id), "body");
                writeln!(dot, "  n{} -> n{} [label=\"body\"];", id, body_id).unwrap();
            }
        }
        Stmt::Assert(expr) => {
            writeln!(
                dot,
                "  n{} [label=\"assert\", fillcolor=red, style=\"filled,rounded\", fontcolor=white];",
                id
            )
            .unwrap();
            let expr_id = ast_expr_to_dot(expr, dot, counter);
            writeln!(dot, "  n{} -> n{} [label=\"property\"];", id, expr_id).unwrap();
        }
        Stmt::Assume(expr) => {
            writeln!(
                dot,
                "  n{} [label=\"assume\", fillcolor=purple, style=\"filled,rounded\", fontcolor=white];",
                id
            )
            .unwrap();
            let expr_id = ast_expr_to_dot(expr, dot, counter);
            writeln!(dot, "  n{} -> n{} [label=\"constraint\"];", id, expr_id).unwrap();
        }
        Stmt::Try {
            try_body,
            catch_var,
            catch_body,
            finally_body,
        } => {
            writeln!(dot, "  n{} [label=\"try\", fillcolor=orange, style=\"filled,rounded\"];", id).unwrap();

            // Try body
            if !try_body.is_empty() {
                let try_id = ast_stmts_to_dot(try_body, dot, counter, Some(id), "try");
                writeln!(dot, "  n{} -> n{} [label=\"try\"];", id, try_id).unwrap();
            }

            // Catch body
            if !catch_body.is_empty() {
                let catch_id = ast_stmts_to_dot(catch_body, dot, counter, Some(id), "catch");
                let catch_label = if let Some(var) = catch_var {
                    format!("catch ({})", var)
                } else {
                    "catch".to_string()
                };
                writeln!(dot, "  n{} -> n{} [label=\"{}\"];", id, catch_id, catch_label).unwrap();
            }

            // Finally body
            if !finally_body.is_empty() {
                let finally_id = ast_stmts_to_dot(finally_body, dot, counter, Some(id), "finally");
                writeln!(dot, "  n{} -> n{} [label=\"finally\"];", id, finally_id).unwrap();
            }
        }
        Stmt::Throw(expr) => {
            writeln!(
                dot,
                "  n{} [label=\"throw\", fillcolor=red, style=\"filled,rounded\", fontcolor=white];",
                id
            )
            .unwrap();
            let expr_id = ast_expr_to_dot(expr, dot, counter);
            writeln!(dot, "  n{} -> n{} [label=\"exception\"];", id, expr_id).unwrap();
        }
    }

    if let Some(_parent_id) = parent {
        // Don't draw this edge, parent already draws it
    }

    id
}

fn ast_stmts_to_dot(stmts: &[Stmt], dot: &mut String, counter: &mut usize, parent: Option<usize>, label: &str) -> usize {
    if stmts.is_empty() {
        let id = *counter;
        *counter += 1;
        writeln!(dot, "  n{} [label=\"skip\", fillcolor=lightgray, style=\"filled,rounded\"];", id).unwrap();
        return id;
    }

    if stmts.len() == 1 {
        return ast_stmt_to_dot(&stmts[0], dot, counter, parent);
    }

    // Multiple statements - create a sequence node
    let seq_id = *counter;
    *counter += 1;
    writeln!(
        dot,
        "  n{} [label=\"{}\", fillcolor=lightyellow, style=\"filled,rounded\"];",
        seq_id, label
    )
    .unwrap();

    for stmt in stmts {
        let stmt_id = ast_stmt_to_dot(stmt, dot, counter, Some(seq_id));
        writeln!(dot, "  n{} -> n{};", seq_id, stmt_id).unwrap();
    }

    seq_id
}

fn ast_expr_to_dot(expr: &Expr, dot: &mut String, counter: &mut usize) -> usize {
    let id = *counter;
    *counter += 1;

    match expr {
        Expr::Lit(b) => {
            writeln!(dot, "  n{} [label=\"{}\", shape=ellipse, fillcolor=white, style=filled];", id, b).unwrap();
        }
        Expr::Var(v) => {
            writeln!(
                dot,
                "  n{} [label=\"{}\", shape=ellipse, fillcolor=lightcyan, style=filled];",
                id, v
            )
            .unwrap();
        }
        Expr::Not(e) => {
            writeln!(dot, "  n{} [label=\"¬\", shape=circle, fillcolor=wheat, style=filled];", id).unwrap();
            let e_id = ast_expr_to_dot(e, dot, counter);
            writeln!(dot, "  n{} -> n{};", id, e_id).unwrap();
        }
        Expr::And(l, r) => {
            writeln!(dot, "  n{} [label=\"∧\", shape=circle, fillcolor=wheat, style=filled];", id).unwrap();
            let l_id = ast_expr_to_dot(l, dot, counter);
            let r_id = ast_expr_to_dot(r, dot, counter);
            writeln!(dot, "  n{} -> n{} [label=\"L\"];", id, l_id).unwrap();
            writeln!(dot, "  n{} -> n{} [label=\"R\"];", id, r_id).unwrap();
        }
        Expr::Or(l, r) => {
            writeln!(dot, "  n{} [label=\"∨\", shape=circle, fillcolor=wheat, style=filled];", id).unwrap();
            let l_id = ast_expr_to_dot(l, dot, counter);
            let r_id = ast_expr_to_dot(r, dot, counter);
            writeln!(dot, "  n{} -> n{} [label=\"L\"];", id, l_id).unwrap();
            writeln!(dot, "  n{} -> n{} [label=\"R\"];", id, r_id).unwrap();
        }
        Expr::Xor(l, r) => {
            writeln!(dot, "  n{} [label=\"⊕\", shape=circle, fillcolor=wheat, style=filled];", id).unwrap();
            let l_id = ast_expr_to_dot(l, dot, counter);
            let r_id = ast_expr_to_dot(r, dot, counter);
            writeln!(dot, "  n{} -> n{} [label=\"L\"];", id, l_id).unwrap();
            writeln!(dot, "  n{} -> n{} [label=\"R\"];", id, r_id).unwrap();
        }
        Expr::Implies(l, r) => {
            writeln!(dot, "  n{} [label=\"⇒\", shape=circle, fillcolor=wheat, style=filled];", id).unwrap();
            let l_id = ast_expr_to_dot(l, dot, counter);
            let r_id = ast_expr_to_dot(r, dot, counter);
            writeln!(dot, "  n{} -> n{} [label=\"L\"];", id, l_id).unwrap();
            writeln!(dot, "  n{} -> n{} [label=\"R\"];", id, r_id).unwrap();
        }
        Expr::Eq(l, r) => {
            writeln!(dot, "  n{} [label=\"=\", shape=circle, fillcolor=wheat, style=filled];", id).unwrap();
            let l_id = ast_expr_to_dot(l, dot, counter);
            let r_id = ast_expr_to_dot(r, dot, counter);
            writeln!(dot, "  n{} -> n{} [label=\"L\"];", id, l_id).unwrap();
            writeln!(dot, "  n{} -> n{} [label=\"R\"];", id, r_id).unwrap();
        }
    }

    id
}

/// Control Flow Graph node (for visualization only)
#[derive(Debug, Clone)]
pub enum CfgNode {
    Entry,
    Exit,
    Statement(String),
    Condition(String),
    Assert(String),
    Assume(String),
}

/// Control Flow Graph (for visualization only)
/// This is a simple graph structure used for DOT rendering.
/// For actual symbolic execution, use `ControlFlowGraph` from cfg.rs.
#[derive(Debug)]
pub struct DotCfg {
    nodes: Vec<CfgNode>,
    edges: Vec<(usize, usize, Option<String>)>, // (from, to, label)
}

impl DotCfg {
    pub fn new() -> Self {
        DotCfg {
            nodes: vec![CfgNode::Entry],
            edges: Vec::new(),
        }
    }

    fn add_node(&mut self, node: CfgNode) -> usize {
        let id = self.nodes.len();
        self.nodes.push(node);
        id
    }

    fn add_edge(&mut self, from: usize, to: usize, label: Option<String>) {
        self.edges.push((from, to, label));
    }

    /// Build CFG from a statement
    pub fn from_stmt(stmt: &Stmt) -> Self {
        let mut cfg = DotCfg::new();
        let exit_id = cfg.add_node(CfgNode::Exit);
        cfg.build_stmt(stmt, 0, exit_id);
        cfg
    }

    fn build_stmt(&mut self, stmt: &Stmt, entry: usize, exit: usize) -> () {
        match stmt {
            Stmt::Skip => {
                self.add_edge(entry, exit, None);
            }
            Stmt::Assign(var, expr) => {
                let stmt_id = self.add_node(CfgNode::Statement(format!("{} := {}", var, expr)));
                self.add_edge(entry, stmt_id, None);
                self.add_edge(stmt_id, exit, None);
            }
            Stmt::If {
                condition,
                then_body,
                else_body,
            } => {
                let cond_id = self.add_node(CfgNode::Condition(format!("{}", condition)));
                self.add_edge(entry, cond_id, None);

                let then_id = self.add_node(CfgNode::Statement("•".to_string()));
                let else_id = self.add_node(CfgNode::Statement("•".to_string()));

                self.add_edge(cond_id, then_id, Some("true".to_string()));
                self.add_edge(cond_id, else_id, Some("false".to_string()));

                self.build_stmts(then_body, then_id, exit);
                self.build_stmts(else_body, else_id, exit);
            }
            Stmt::While { condition, body } => {
                let cond_id = self.add_node(CfgNode::Condition(format!("{}", condition)));
                self.add_edge(entry, cond_id, None);

                let body_entry = self.add_node(CfgNode::Statement("•".to_string()));
                self.add_edge(cond_id, body_entry, Some("true".to_string()));

                self.build_stmts(body, body_entry, cond_id);
                self.add_edge(cond_id, exit, Some("false".to_string()));
            }
            Stmt::Assert(expr) => {
                let assert_id = self.add_node(CfgNode::Assert(format!("{}", expr)));
                self.add_edge(entry, assert_id, None);
                self.add_edge(assert_id, exit, None);
            }
            Stmt::Assume(expr) => {
                let assume_id = self.add_node(CfgNode::Assume(format!("{}", expr)));
                self.add_edge(entry, assume_id, None);
                self.add_edge(assume_id, exit, None);
            }
            Stmt::Try {
                try_body,
                catch_var: _,
                catch_body,
                finally_body,
            } => {
                let try_id = self.add_node(CfgNode::Statement("try".to_string()));
                self.add_edge(entry, try_id, None);

                if !finally_body.is_empty() {
                    let finally_id = self.add_node(CfgNode::Statement("finally".to_string()));
                    self.build_stmts(try_body, try_id, finally_id);
                    if !catch_body.is_empty() {
                        let catch_id = self.add_node(CfgNode::Statement("catch".to_string()));
                        self.add_edge(try_id, catch_id, Some("exception".to_string()));
                        self.build_stmts(catch_body, catch_id, finally_id);
                    }
                    self.build_stmts(finally_body, finally_id, exit);
                } else if !catch_body.is_empty() {
                    let catch_id = self.add_node(CfgNode::Statement("catch".to_string()));
                    self.add_edge(try_id, catch_id, Some("exception".to_string()));
                    self.build_stmts(try_body, try_id, exit);
                    self.build_stmts(catch_body, catch_id, exit);
                } else {
                    self.build_stmts(try_body, try_id, exit);
                }
            }
            Stmt::Throw(expr) => {
                let throw_id = self.add_node(CfgNode::Statement(format!("throw {}", expr)));
                self.add_edge(entry, throw_id, None);
                // Throw doesn't connect to exit - it propagates upward
            }
        }
    }

    fn build_stmts(&mut self, stmts: &[Stmt], entry: usize, exit: usize) {
        if stmts.is_empty() {
            self.add_edge(entry, exit, None);
            return;
        }

        if stmts.len() == 1 {
            self.build_stmt(&stmts[0], entry, exit);
            return;
        }

        let mut current = entry;
        for (i, stmt) in stmts.iter().enumerate() {
            let is_last = i == stmts.len() - 1;
            let next = if is_last {
                exit
            } else {
                self.add_node(CfgNode::Statement("•".to_string()))
            };
            self.build_stmt(stmt, current, next);
            current = next;
        }
    }

    /// Convert CFG to DOT format
    pub fn to_dot(&self, name: &str) -> String {
        let mut dot = String::new();
        writeln!(dot, "digraph CFG_{} {{", name.replace(' ', "_")).unwrap();
        writeln!(dot, "  node [shape=box];").unwrap();
        writeln!(dot, "  rankdir=TB;").unwrap();
        writeln!(dot).unwrap();

        // Render nodes
        for (id, node) in self.nodes.iter().enumerate() {
            match node {
                CfgNode::Entry => {
                    writeln!(
                        dot,
                        "  n{} [label=\"ENTRY\", shape=ellipse, fillcolor=green, style=filled, fontcolor=white];",
                        id
                    )
                    .unwrap();
                }
                CfgNode::Exit => {
                    writeln!(
                        dot,
                        "  n{} [label=\"EXIT\", shape=ellipse, fillcolor=red, style=filled, fontcolor=white];",
                        id
                    )
                    .unwrap();
                }
                CfgNode::Statement(s) => {
                    writeln!(
                        dot,
                        "  n{} [label=\"{}\", fillcolor=lightblue, style=filled];",
                        id,
                        s.replace('"', "\\\"")
                    )
                    .unwrap();
                }
                CfgNode::Condition(c) => {
                    writeln!(
                        dot,
                        "  n{} [label=\"{}\", shape=diamond, fillcolor=lightyellow, style=filled];",
                        id,
                        c.replace('"', "\\\"")
                    )
                    .unwrap();
                }
                CfgNode::Assert(a) => {
                    writeln!(
                        dot,
                        "  n{} [label=\"assert {}\", fillcolor=orange, style=filled];",
                        id,
                        a.replace('"', "\\\"")
                    )
                    .unwrap();
                }
                CfgNode::Assume(a) => {
                    writeln!(
                        dot,
                        "  n{} [label=\"assume {}\", fillcolor=purple, style=filled, fontcolor=white];",
                        id,
                        a.replace('"', "\\\"")
                    )
                    .unwrap();
                }
            }
        }

        writeln!(dot).unwrap();

        // Render edges
        for (from, to, label) in &self.edges {
            if let Some(lbl) = label {
                writeln!(dot, "  n{} -> n{} [label=\"{}\"];", from, to, lbl).unwrap();
            } else {
                writeln!(dot, "  n{} -> n{};", from, to).unwrap();
            }
        }

        writeln!(dot, "}}").unwrap();
        dot
    }
}

impl Default for DotCfg {
    fn default() -> Self {
        Self::new()
    }
}

/// Generate DOT representation of CFG (with basic blocks)
pub fn cfg_to_dot(cfg: &ControlFlowGraph, name: &str) -> String {
    let mut dot = String::new();
    writeln!(dot, "digraph CFG_{} {{", name.replace(' ', "_")).unwrap();
    writeln!(dot, "  node [shape=box];").unwrap();
    writeln!(dot, "  rankdir=TB;").unwrap();
    writeln!(dot, "  compound=true;").unwrap();
    writeln!(dot).unwrap();

    // Sort block IDs for consistent output
    let mut block_ids: Vec<_> = cfg.blocks.keys().copied().collect();
    block_ids.sort();

    // Render each basic block as a subgraph with explicit statements
    for id in &block_ids {
        let block = &cfg.blocks[id];

        writeln!(dot, "  subgraph cluster_bb{} {{", id).unwrap();
        writeln!(dot, "    label=\"Block bb{}\";", id).unwrap();
        writeln!(dot, "    style=rounded;").unwrap();

        // Color based on block type
        if *id == cfg.entry {
            writeln!(dot, "    color=green;").unwrap();
            writeln!(dot, "    penwidth=2;").unwrap();
        } else if matches!(block.terminator, crate::cfg::Terminator::Return) {
            writeln!(dot, "    color=red;").unwrap();
            writeln!(dot, "    penwidth=2;").unwrap();
        } else {
            writeln!(dot, "    color=blue;").unwrap();
        }
        writeln!(dot).unwrap();

        // Create a node for each instruction
        if block.instructions.is_empty() {
            let node_id = format!("bb{}_empty", id);
            writeln!(dot, "    {} [label=\"(empty)\", shape=plaintext, fontcolor=gray];", node_id).unwrap();
        } else {
            for (i, instr) in block.instructions.iter().enumerate() {
                let node_id = format!("bb{}_{}", id, i);
                let label = instr.to_string().replace('"', "\\\"");

                // Color based on instruction type
                let (color, font_color) = match instr {
                    crate::cfg::Instruction::Assert(_) => ("orange", "black"),
                    crate::cfg::Instruction::Assume(_) => ("purple", "white"),
                    crate::cfg::Instruction::Assign(_, _) => ("lightblue", "black"),
                    crate::cfg::Instruction::Throw(_) => ("red", "white"),
                };

                writeln!(
                    dot,
                    "    {} [label=\"{}\", fillcolor={}, style=filled, fontcolor={}];",
                    node_id, label, color, font_color
                )
                .unwrap();

                // Connect instructions within the block
                if i > 0 {
                    let prev_node_id = format!("bb{}_{}", id, i - 1);
                    writeln!(dot, "    {} -> {};", prev_node_id, node_id).unwrap();
                }
            }
        }

        // Add terminator node
        let term_node_id = format!("bb{}_term", id);
        let term_label = match &block.terminator {
            crate::cfg::Terminator::Goto(_) => "goto".to_string(),
            crate::cfg::Terminator::Branch { condition, .. } => {
                format!("branch {}", condition.to_string().replace('"', "\\\""))
            }
            crate::cfg::Terminator::Return => "return".to_string(),
        };

        let (term_shape, term_color) = match &block.terminator {
            crate::cfg::Terminator::Branch { .. } => ("diamond", "lightyellow"),
            _ => ("ellipse", "lightgray"),
        };

        writeln!(
            dot,
            "    {} [label=\"{}\", shape={}, fillcolor={}, style=filled];",
            term_node_id, term_label, term_shape, term_color
        )
        .unwrap();

        // Connect last instruction to terminator
        if !block.instructions.is_empty() {
            let last_instr = format!("bb{}_{}", id, block.instructions.len() - 1);
            writeln!(dot, "    {} -> {};", last_instr, term_node_id).unwrap();
        } else {
            let empty_node = format!("bb{}_empty", id);
            writeln!(dot, "    {} -> {};", empty_node, term_node_id).unwrap();
        }

        writeln!(dot, "  }}").unwrap();
        writeln!(dot).unwrap();
    }

    // Render edges between blocks (from terminators to first instruction of target)
    for id in &block_ids {
        let block = &cfg.blocks[id];
        let term_node = format!("bb{}_term", id);

        match &block.terminator {
            crate::cfg::Terminator::Goto(target) => {
                let target_entry = if let Some(block) = cfg.blocks.get(target) {
                    if block.instructions.is_empty() {
                        format!("bb{}_empty", target)
                    } else {
                        format!("bb{}_0", target)
                    }
                } else {
                    eprintln!("Warning: Goto target bb{} does not exist", target);
                    continue;
                };
                writeln!(
                    dot,
                    "  {} -> {} [ltail=cluster_bb{}, lhead=cluster_bb{}];",
                    term_node, target_entry, id, target
                )
                .unwrap();
            }
            crate::cfg::Terminator::Branch {
                true_target, false_target, ..
            } => {
                // Check if target blocks exist
                let true_entry = if let Some(block) = cfg.blocks.get(true_target) {
                    if block.instructions.is_empty() {
                        format!("bb{}_empty", true_target)
                    } else {
                        format!("bb{}_0", true_target)
                    }
                } else {
                    eprintln!("Warning: Branch target bb{} does not exist", true_target);
                    continue;
                };

                let false_entry = if let Some(block) = cfg.blocks.get(false_target) {
                    if block.instructions.is_empty() {
                        format!("bb{}_empty", false_target)
                    } else {
                        format!("bb{}_0", false_target)
                    }
                } else {
                    eprintln!("Warning: Branch target bb{} does not exist", false_target);
                    continue;
                };

                writeln!(
                    dot,
                    "  {} -> {} [label=\"true\", color=green, ltail=cluster_bb{}, lhead=cluster_bb{}];",
                    term_node, true_entry, id, true_target
                )
                .unwrap();
                writeln!(
                    dot,
                    "  {} -> {} [label=\"false\", color=red, ltail=cluster_bb{}, lhead=cluster_bb{}];",
                    term_node, false_entry, id, false_target
                )
                .unwrap();
            }
            crate::cfg::Terminator::Return => {
                // No outgoing edges
            }
        }

        // Add exceptional control flow edges from trap_context
        // Note: Finally is NOT shown here because it's in the normal control flow
        // (try blocks already exit to finally). Only catch is exceptional flow.
        if let Some(trap_ctx) = &block.trap_context {
            if let Some(catch_target) = trap_ctx.catch_target {
                let catch_entry = if let Some(block) = cfg.blocks.get(&catch_target) {
                    if block.instructions.is_empty() {
                        format!("bb{}_empty", catch_target)
                    } else {
                        format!("bb{}_0", catch_target)
                    }
                } else {
                    eprintln!("Warning: Catch target bb{} does not exist", catch_target);
                    format!("bb{}_missing", catch_target)
                };

                let catch_label = if let Some(var) = &trap_ctx.catch_variable {
                    format!("catch ({})", var)
                } else {
                    "catch".to_string()
                };

                writeln!(
                    dot,
                    "  {} -> {} [label=\"{}\", style=dashed, color=red, ltail=cluster_bb{}, lhead=cluster_bb{}];",
                    term_node, catch_entry, catch_label, id, catch_target
                )
                .unwrap();
            }
        }
    }

    writeln!(dot, "}}").unwrap();
    dot
}
