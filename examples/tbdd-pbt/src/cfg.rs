//! Control Flow Graph representation for T-BDD.
//!
//! This module provides CFG construction and path extraction for
//! automatic predicate discovery and test generation.
//!
//! ## Overview
//!
//! A Control Flow Graph (CFG) represents program structure:
//! - **Nodes** are basic blocks (straight-line code)
//! - **Edges** represent control flow (sequential, conditional, back edges)
//!
//! ## Example
//!
//! ```rust
//! use tbdd_pbt::cfg::{CfgBuilder, Terminator};
//! use tbdd_pbt::Predicate;
//!
//! let mut builder = CfgBuilder::new();
//! let entry = builder.entry();
//! let then_block = builder.new_block("then");
//! let else_block = builder.new_block("else");
//!
//! builder.set_terminator(entry, Terminator::Branch {
//!     condition: Predicate::lt("x", 0),
//!     true_target: then_block,
//!     false_target: else_block,
//! });
//! builder.set_terminator(then_block, Terminator::Return);
//! builder.set_terminator(else_block, Terminator::Return);
//!
//! let cfg = builder.build();
//! ```

use std::collections::HashSet;
use std::fmt;

use ananke_bdd::bdd::Bdd;
use ananke_bdd::reference::Ref;

use crate::predicate::{Literal, Predicate, PredicateUniverse};

/// Unique identifier for a basic block.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct BlockId(pub usize);

impl fmt::Display for BlockId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "B{}", self.0)
    }
}

/// A statement within a basic block.
///
/// Currently simplified — in a full implementation, this would include
/// assignments, function calls, etc.
#[derive(Debug, Clone)]
pub enum Statement {
    /// Variable assignment: var = expr
    Assign { var: String, expr: Expression },
    /// Assertion that must hold
    Assert(Predicate),
    /// Assumption for path condition
    Assume(Predicate),
    /// No operation (placeholder)
    Nop,
}

/// A simple expression for assignments.
#[derive(Debug, Clone)]
pub enum Expression {
    /// Constant value
    Const(i64),
    /// Variable reference
    Var(String),
    /// Binary operation
    BinOp {
        lhs: Box<Expression>,
        op: BinOpKind,
        rhs: Box<Expression>,
    },
}

/// Binary operation kinds.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BinOpKind {
    Add, // +
    Sub, // -
    Mul, // *
    Div, // /
    Mod, // %
}

impl fmt::Display for BinOpKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            BinOpKind::Add => write!(f, "+"),
            BinOpKind::Sub => write!(f, "-"),
            BinOpKind::Mul => write!(f, "*"),
            BinOpKind::Div => write!(f, "/"),
            BinOpKind::Mod => write!(f, "%"),
        }
    }
}

/// How control flow leaves a basic block.
#[derive(Debug, Clone)]
pub enum Terminator {
    /// Unconditional jump to another block.
    Goto(BlockId),
    /// Conditional branch based on a predicate.
    Branch {
        condition: Predicate,
        true_target: BlockId,
        false_target: BlockId,
    },
    /// Function return.
    Return,
    /// Unreachable (after panic, infinite loop, etc.).
    Unreachable,
}

impl fmt::Display for Terminator {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Terminator::Goto(target) => write!(f, "goto {}", target),
            Terminator::Branch {
                condition,
                true_target,
                false_target,
            } => {
                write!(f, "if {} then {} else {}", condition, true_target, false_target)
            }
            Terminator::Return => write!(f, "return"),
            Terminator::Unreachable => write!(f, "unreachable"),
        }
    }
}

/// A basic block in the CFG.
#[derive(Debug, Clone)]
pub struct BasicBlock {
    /// Unique identifier.
    pub id: BlockId,
    /// Human-readable label.
    pub label: String,
    /// Statements in the block.
    pub statements: Vec<Statement>,
    /// How control leaves this block.
    pub terminator: Terminator,
}

impl BasicBlock {
    fn new(id: BlockId, label: impl Into<String>) -> Self {
        Self {
            id,
            label: label.into(),
            statements: Vec::new(),
            terminator: Terminator::Unreachable,
        }
    }

    /// Get successor block IDs from the terminator.
    pub fn successors(&self) -> Vec<BlockId> {
        match &self.terminator {
            Terminator::Goto(target) => vec![*target],
            Terminator::Branch {
                true_target, false_target, ..
            } => vec![*true_target, *false_target],
            Terminator::Return | Terminator::Unreachable => vec![],
        }
    }
}

/// A complete control flow graph.
///
/// Edges are stored implicitly in block terminators, not as a separate list.
#[derive(Debug, Clone)]
pub struct ControlFlowGraph {
    /// All basic blocks, indexed by BlockId.
    pub blocks: Vec<BasicBlock>,
    /// Entry block ID.
    pub entry: BlockId,
}

impl ControlFlowGraph {
    /// Create a new CFG with the given blocks and entry point.
    pub fn new(blocks: Vec<BasicBlock>, entry: BlockId) -> Self {
        Self { blocks, entry }
    }

    /// Get a block by ID.
    pub fn block(&self, id: BlockId) -> Option<&BasicBlock> {
        self.blocks.get(id.0)
    }

    /// Get successor block IDs (derived from terminator).
    pub fn successors(&self, block: BlockId) -> Vec<BlockId> {
        self.block(block).map(|b| b.successors()).unwrap_or_default()
    }

    /// Get predecessor block IDs (computed by scanning all blocks).
    pub fn predecessors(&self, block: BlockId) -> Vec<BlockId> {
        self.blocks
            .iter()
            .filter(|b| b.successors().contains(&block))
            .map(|b| b.id)
            .collect()
    }

    /// Get exit blocks (those with Return terminator).
    pub fn exits(&self) -> Vec<BlockId> {
        self.blocks
            .iter()
            .filter(|b| matches!(b.terminator, Terminator::Return))
            .map(|b| b.id)
            .collect()
    }

    /// Number of blocks.
    pub fn num_blocks(&self) -> usize {
        self.blocks.len()
    }

    /// Count edges (derived from terminators).
    pub fn num_edges(&self) -> usize {
        self.blocks.iter().map(|b| b.successors().len()).sum()
    }

    /// Extract all predicates from branch conditions.
    pub fn extract_predicates(&self) -> Vec<Predicate> {
        let mut predicates = Vec::new();
        let mut seen = HashSet::new();

        for block in &self.blocks {
            if let Terminator::Branch { ref condition, .. } = block.terminator {
                if seen.insert(condition.clone()) {
                    predicates.push(condition.clone());
                }
            }
        }

        predicates
    }

    /// Build a predicate universe from this CFG.
    pub fn build_universe(&self, bdd: &Bdd) -> PredicateUniverse {
        let mut universe = PredicateUniverse::new();
        for predicate in self.extract_predicates() {
            universe.register(predicate, bdd);
        }
        universe
    }

    /// Enumerate all paths through the CFG up to a depth bound.
    pub fn enumerate_paths(&self, max_depth: usize) -> Vec<CfgPath> {
        let mut paths = Vec::new();
        let mut stack = vec![PathState {
            block: self.entry,
            condition: Vec::new(),
            depth: 0,
            visited: HashSet::new(),
        }];

        while let Some(state) = stack.pop() {
            if state.depth > max_depth {
                continue;
            }

            let block = &self.blocks[state.block.0];

            match &block.terminator {
                Terminator::Return => {
                    paths.push(CfgPath {
                        blocks: state.visited.into_iter().collect(),
                        condition: state.condition,
                    });
                }
                Terminator::Goto(target) => {
                    if !state.visited.contains(target) {
                        let mut new_visited = state.visited.clone();
                        new_visited.insert(*target);
                        stack.push(PathState {
                            block: *target,
                            condition: state.condition,
                            depth: state.depth + 1,
                            visited: new_visited,
                        });
                    }
                }
                Terminator::Branch {
                    condition,
                    true_target,
                    false_target,
                } => {
                    // True branch
                    if !state.visited.contains(true_target) {
                        let mut true_cond = state.condition.clone();
                        true_cond.push(Literal::pos(condition.clone()));
                        let mut new_visited = state.visited.clone();
                        new_visited.insert(*true_target);
                        stack.push(PathState {
                            block: *true_target,
                            condition: true_cond,
                            depth: state.depth + 1,
                            visited: new_visited,
                        });
                    }

                    // False branch
                    if !state.visited.contains(false_target) {
                        let mut false_cond = state.condition.clone();
                        false_cond.push(Literal::neg(condition.clone()));
                        let mut new_visited = state.visited.clone();
                        new_visited.insert(*false_target);
                        stack.push(PathState {
                            block: *false_target,
                            condition: false_cond,
                            depth: state.depth + 1,
                            visited: new_visited,
                        });
                    }
                }
                Terminator::Unreachable => {}
            }
        }

        paths
    }

    /// Convert all paths to a single BDD representing the path space.
    pub fn paths_to_bdd(&self, universe: &PredicateUniverse, bdd: &Bdd, max_depth: usize) -> Ref {
        let paths = self.enumerate_paths(max_depth);
        let mut result = bdd.zero();

        for path in paths {
            let path_bdd = path.to_bdd(universe, bdd);
            result = bdd.apply_or(result, path_bdd);
        }

        result
    }

    /// Export to DOT format for visualization.
    pub fn to_dot(&self) -> String {
        let mut dot = String::from("digraph CFG {\n");
        dot.push_str("  rankdir=TB;\n");
        dot.push_str("  node [shape=box, fontname=\"monospace\"];\n");
        dot.push_str("  edge [fontname=\"monospace\"];\n\n");

        // Entry marker
        dot.push_str("  __entry [shape=point, width=0.1];\n");
        dot.push_str(&format!("  __entry -> {};\n\n", self.entry));

        let exits = self.exits();

        // Blocks
        for block in &self.blocks {
            let term_str = match &block.terminator {
                Terminator::Return => "return".to_string(),
                Terminator::Goto(t) => format!("goto {}", t),
                Terminator::Branch { condition, .. } => format!("if {}", condition),
                Terminator::Unreachable => "unreachable".to_string(),
            };

            let label = if block.statements.is_empty() {
                format!("{}\\n{}", block.label, term_str)
            } else {
                format!("{}\\n...\\n{}", block.label, term_str)
            };

            let style = if exits.contains(&block.id) {
                ", style=filled, fillcolor=lightgray"
            } else if block.id == self.entry {
                ", style=filled, fillcolor=lightblue"
            } else {
                ""
            };

            dot.push_str(&format!("  {} [label=\"{}\"{}];\n", block.id, label, style));
        }

        dot.push_str("\n");

        // Edges (derived from terminators)
        for block in &self.blocks {
            match &block.terminator {
                Terminator::Goto(target) => {
                    dot.push_str(&format!("  {} -> {};\n", block.id, target));
                }
                Terminator::Branch {
                    condition,
                    true_target,
                    false_target,
                } => {
                    dot.push_str(&format!(
                        "  {} -> {} [label=\"{}\", color=darkgreen];\n",
                        block.id, true_target, condition
                    ));
                    dot.push_str(&format!(
                        "  {} -> {} [label=\"!{}\", color=darkred];\n",
                        block.id, false_target, condition
                    ));
                }
                Terminator::Return | Terminator::Unreachable => {}
            }
        }

        dot.push_str("}\n");
        dot
    }
}

/// Internal state for path enumeration.
struct PathState {
    block: BlockId,
    condition: Vec<Literal>,
    depth: usize,
    visited: HashSet<BlockId>,
}

/// A path through the CFG.
#[derive(Debug, Clone)]
pub struct CfgPath {
    /// Blocks visited along this path.
    pub blocks: Vec<BlockId>,
    /// Path condition as conjunction of literals.
    pub condition: Vec<Literal>,
}

impl CfgPath {
    /// Convert path condition to a BDD.
    pub fn to_bdd(&self, universe: &PredicateUniverse, bdd: &Bdd) -> Ref {
        let mut result = bdd.one();

        for literal in &self.condition {
            if let Some(lit_bdd) = universe.literal_to_bdd(literal, bdd) {
                result = bdd.apply_and(result, lit_bdd);
            }
        }

        result
    }

    /// Get the effective predicates (accounting for polarity).
    pub fn effective_predicates(&self) -> Vec<Predicate> {
        self.condition.iter().map(|lit| lit.effective_predicate()).collect()
    }
}

/// Builder for constructing CFGs incrementally.
pub struct CfgBuilder {
    blocks: Vec<BasicBlock>,
    next_id: usize,
    entry: Option<BlockId>,
}

impl CfgBuilder {
    /// Create a new CFG builder.
    pub fn new() -> Self {
        Self {
            blocks: Vec::new(),
            next_id: 0,
            entry: None,
        }
    }

    /// Get or create the entry block.
    pub fn entry(&mut self) -> BlockId {
        if let Some(entry) = self.entry {
            entry
        } else {
            let id = self.new_block("entry");
            self.entry = Some(id);
            id
        }
    }

    /// Create a new basic block with a label.
    pub fn new_block(&mut self, label: impl Into<String>) -> BlockId {
        let id = BlockId(self.next_id);
        self.next_id += 1;
        self.blocks.push(BasicBlock::new(id, label));
        id
    }

    /// Add a statement to a block.
    pub fn add_statement(&mut self, block: BlockId, stmt: Statement) {
        if let Some(b) = self.blocks.get_mut(block.0) {
            b.statements.push(stmt);
        }
    }

    /// Set the terminator for a block.
    pub fn set_terminator(&mut self, block: BlockId, terminator: Terminator) {
        if let Some(b) = self.blocks.get_mut(block.0) {
            b.terminator = terminator;
        }
    }

    /// Convenience: add a return terminator.
    pub fn add_return(&mut self, block: BlockId) {
        self.set_terminator(block, Terminator::Return);
    }

    /// Convenience: add a goto terminator.
    pub fn add_goto(&mut self, from: BlockId, to: BlockId) {
        self.set_terminator(from, Terminator::Goto(to));
    }

    /// Convenience: add a branch terminator.
    pub fn add_branch(&mut self, block: BlockId, condition: Predicate, true_target: BlockId, false_target: BlockId) {
        self.set_terminator(
            block,
            Terminator::Branch {
                condition,
                true_target,
                false_target,
            },
        );
    }

    /// Build the complete CFG.
    pub fn build(self) -> ControlFlowGraph {
        let entry = self.entry.unwrap_or(BlockId(0));
        ControlFlowGraph::new(self.blocks, entry)
    }
}

impl Default for CfgBuilder {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_cfg_builder() {
        let mut builder = CfgBuilder::new();

        let entry = builder.entry();
        let then_block = builder.new_block("then");
        let else_block = builder.new_block("else");

        builder.add_branch(entry, Predicate::lt("x", 0), then_block, else_block);
        builder.add_return(then_block);
        builder.add_return(else_block);

        let cfg = builder.build();

        assert_eq!(cfg.num_blocks(), 3);
        assert_eq!(cfg.num_edges(), 2);
        assert_eq!(cfg.exits().len(), 2);
    }

    #[test]
    fn test_path_enumeration() {
        let mut builder = CfgBuilder::new();

        let entry = builder.entry();
        let b1 = builder.new_block("b1");
        let b2 = builder.new_block("b2");

        builder.add_branch(entry, Predicate::lt("x", 0), b1, b2);
        builder.add_return(b1);
        builder.add_return(b2);

        let cfg = builder.build();
        let paths = cfg.enumerate_paths(10);

        assert_eq!(paths.len(), 2);
        assert!(paths.iter().any(|p| p.condition.len() == 1 && p.condition[0].positive));
        assert!(paths.iter().any(|p| p.condition.len() == 1 && !p.condition[0].positive));
    }

    #[test]
    fn test_predicate_extraction() {
        let mut builder = CfgBuilder::new();

        let entry = builder.entry();
        let b1 = builder.new_block("b1");
        let b2 = builder.new_block("b2");
        let b3 = builder.new_block("b3");
        let b4 = builder.new_block("b4");

        builder.add_branch(entry, Predicate::lt("x", 0), b1, b2);
        builder.add_return(b1);
        builder.add_branch(b2, Predicate::eq("x", 0), b3, b4);
        builder.add_return(b3);
        builder.add_return(b4);

        let cfg = builder.build();
        let predicates = cfg.extract_predicates();

        assert_eq!(predicates.len(), 2);
    }

    #[test]
    fn test_path_to_bdd() {
        let mut builder = CfgBuilder::new();

        let entry = builder.entry();
        let b1 = builder.new_block("b1");
        let b2 = builder.new_block("b2");

        builder.add_branch(entry, Predicate::lt("x", 0), b1, b2);
        builder.add_return(b1);
        builder.add_return(b2);

        let cfg = builder.build();
        let bdd = Bdd::default();
        let universe = cfg.build_universe(&bdd);

        let path_space = cfg.paths_to_bdd(&universe, &bdd, 10);

        // Should be TRUE (all paths covered = tautology in this simple case)
        assert!(bdd.is_one(path_space));
    }

    #[test]
    fn test_categorize_cfg() {
        // Model the categorize function from basic example
        let mut builder = CfgBuilder::new();

        let entry = builder.entry();
        let negative = builder.new_block("negative");
        let check_zero = builder.new_block("check_zero");
        let zero = builder.new_block("zero");
        let check_small = builder.new_block("check_small");
        let small = builder.new_block("small");
        let large = builder.new_block("large");

        let p1 = Predicate::lt("x", 0);
        let p2 = Predicate::eq("x", 0);
        let p3 = Predicate::lt("x", 100);

        builder.add_branch(entry, p1, negative, check_zero);
        builder.add_return(negative);
        builder.add_branch(check_zero, p2, zero, check_small);
        builder.add_return(zero);
        builder.add_branch(check_small, p3, small, large);
        builder.add_return(small);
        builder.add_return(large);

        let cfg = builder.build();

        assert_eq!(cfg.num_blocks(), 7);
        let paths = cfg.enumerate_paths(10);
        assert_eq!(paths.len(), 4); // negative, zero, small, large
    }
}
