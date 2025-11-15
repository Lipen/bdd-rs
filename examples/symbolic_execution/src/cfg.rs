//! Control Flow Graph with Basic Blocks
//!
//! A CFG represents a program as a graph of basic blocks connected by edges.
//! Each basic block is a maximal sequence of straight-line code (no branches).

use std::collections::HashMap;
use std::fmt;

use crate::ast::{Expr, Stmt, Var};

/// A basic block: a sequence of non-control-flow statements
#[derive(Debug, Clone)]
pub struct BasicBlock {
    pub id: BlockId,
    pub instructions: Vec<Instruction>,
    pub terminator: Terminator,
}

/// Unique identifier for a basic block
pub type BlockId = usize;

/// An instruction within a basic block (straight-line code)
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Instruction {
    /// Assignment: var = expr
    Assign(Var, Expr),
    /// Assertion: assert expr
    Assert(Expr),
    /// Assumption: assume expr
    Assume(Expr),
}

impl fmt::Display for Instruction {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Instruction::Assign(v, e) => write!(f, "{} = {}", v, e),
            Instruction::Assert(e) => write!(f, "assert {}", e),
            Instruction::Assume(e) => write!(f, "assume {}", e),
        }
    }
}

/// Terminator: how a basic block ends (control flow transfer)
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Terminator {
    /// Jump to another block unconditionally
    Goto(BlockId),
    /// Conditional branch: if expr then true_target else false_target
    Branch {
        condition: Expr,
        true_target: BlockId,
        false_target: BlockId,
    },
    /// Return/exit from the program
    Return,
}

impl fmt::Display for Terminator {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Terminator::Goto(target) => write!(f, "goto bb{}", target),
            Terminator::Branch {
                condition,
                true_target,
                false_target,
            } => write!(f, "if {} then bb{} else bb{}", condition, true_target, false_target),
            Terminator::Return => write!(f, "return"),
        }
    }
}

/// Control Flow Graph: a collection of basic blocks
#[derive(Debug, Clone)]
pub struct ControlFlowGraph {
    /// All basic blocks, indexed by BlockId
    pub blocks: HashMap<BlockId, BasicBlock>,
    /// Entry point of the CFG
    pub entry: BlockId,
}

impl ControlFlowGraph {
    /// Create a new empty CFG
    pub fn new(entry: BlockId) -> Self {
        ControlFlowGraph {
            blocks: HashMap::new(),
            entry,
        }
    }

    /// Add a basic block to the CFG
    pub fn add_block(&mut self, block: BasicBlock) {
        self.blocks.insert(block.id, block);
    }

    /// Get a basic block by ID
    pub fn get_block(&self, id: BlockId) -> Option<&BasicBlock> {
        self.blocks.get(&id)
    }

    /// Get successors of a block
    pub fn successors(&self, id: BlockId) -> Vec<BlockId> {
        self.blocks
            .get(&id)
            .map(|block| match &block.terminator {
                Terminator::Goto(target) => vec![*target],
                Terminator::Branch {
                    true_target, false_target, ..
                } => vec![*true_target, *false_target],
                Terminator::Return => vec![],
            })
            .unwrap_or_default()
    }

    /// Build a CFG from an AST statement
    pub fn from_stmt(stmt: &Stmt) -> Self {
        Self::from_stmts(&[stmt.clone()])
    }

    /// Build a CFG from a list of statements
    pub fn from_stmts(stmts: &[Stmt]) -> Self {
        let mut builder = CfgBuilder::new();
        let exit = builder.fresh_block();
        builder.build_stmts(stmts, builder.entry, exit);

        // Flush any remaining instructions at entry
        if !builder.current_instructions.is_empty() {
            builder.flush_block(builder.entry, Terminator::Goto(exit));
        }

        // Add return terminator to exit block
        builder.set_terminator(exit, Terminator::Return);

        builder.finalize()
    }
}

impl fmt::Display for ControlFlowGraph {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "CFG (entry: bb{}):", self.entry)?;

        // Sort blocks by ID for consistent output
        let mut block_ids: Vec<_> = self.blocks.keys().copied().collect();
        block_ids.sort();

        for id in block_ids {
            let block = &self.blocks[&id];
            writeln!(f, "\nbb{}:", id)?;
            for instr in &block.instructions {
                writeln!(f, "  {}", instr)?;
            }
            writeln!(f, "  {}", block.terminator)?;
        }

        Ok(())
    }
}

/// Builder for constructing a CFG from an AST
struct CfgBuilder {
    next_block_id: BlockId,
    blocks: HashMap<BlockId, BasicBlock>,
    entry: BlockId,
    /// Instructions accumulated for the current block being built
    current_instructions: Vec<Instruction>,
}

impl CfgBuilder {
    fn new() -> Self {
        let entry = 0;
        CfgBuilder {
            next_block_id: 1,
            blocks: HashMap::new(),
            entry,
            current_instructions: Vec::new(),
        }
    }

    /// Allocate a fresh block ID
    fn fresh_block(&mut self) -> BlockId {
        let id = self.next_block_id;
        self.next_block_id += 1;
        id
    }

    /// Add an instruction to the current block being built
    fn add_instruction(&mut self, instr: Instruction) {
        self.current_instructions.push(instr);
    }

    /// Flush accumulated instructions into a block with the given terminator
    fn flush_block(&mut self, block_id: BlockId, terminator: Terminator) {
        let instructions = std::mem::take(&mut self.current_instructions);
        let block = BasicBlock {
            id: block_id,
            instructions,
            terminator,
        };
        self.blocks.insert(block_id, block);
    }

    /// Set terminator for a block (assumes no instructions pending)
    fn set_terminator(&mut self, block_id: BlockId, terminator: Terminator) {
        if let Some(block) = self.blocks.get_mut(&block_id) {
            block.terminator = terminator;
        } else {
            // Block doesn't exist yet, create it empty
            let block = BasicBlock {
                id: block_id,
                instructions: Vec::new(),
                terminator,
            };
            self.blocks.insert(block_id, block);
        }
    }

    /// Build CFG from a list of statements, connecting entry to exit
    fn build_stmts(&mut self, stmts: &[Stmt], entry: BlockId, exit: BlockId) {
        if stmts.is_empty() {
            // Empty body, just connect entry to exit
            if !self.current_instructions.is_empty() {
                self.flush_block(entry, Terminator::Goto(exit));
            } else {
                self.set_terminator(entry, Terminator::Goto(exit));
            }
            return;
        }

        let mut current = entry;

        for (i, stmt) in stmts.iter().enumerate() {
            let is_last = i == stmts.len() - 1;
            match stmt {
                Stmt::Skip => {
                    // No-op, continue
                }

                Stmt::Assign(var, expr) => {
                    self.add_instruction(Instruction::Assign(var.clone(), expr.clone()));
                }

                Stmt::Assert(expr) => {
                    self.add_instruction(Instruction::Assert(expr.clone()));
                }

                Stmt::Assume(expr) => {
                    self.add_instruction(Instruction::Assume(expr.clone()));
                }

                Stmt::If {
                    condition,
                    then_body,
                    else_body,
                } => {
                    // Flush any pending instructions to current block
                    let branch_block = if self.current_instructions.is_empty() {
                        current
                    } else {
                        let bb = self.fresh_block();
                        self.flush_block(current, Terminator::Goto(bb));
                        bb
                    };

                    let then_block = self.fresh_block();
                    let else_block = self.fresh_block();
                    let merge_block = if is_last { exit } else { self.fresh_block() };

                    self.set_terminator(
                        branch_block,
                        Terminator::Branch {
                            condition: condition.clone(),
                            true_target: then_block,
                            false_target: else_block,
                        },
                    );

                    self.build_stmts(then_body, then_block, merge_block);
                    // Always ensure then block exists, even if empty
                    if !self.current_instructions.is_empty() {
                        self.flush_block(then_block, Terminator::Goto(merge_block));
                    } else if !self.blocks.contains_key(&then_block) {
                        self.set_terminator(then_block, Terminator::Goto(merge_block));
                    }

                    self.build_stmts(else_body, else_block, merge_block);
                    // Always ensure else block exists, even if empty
                    if !self.current_instructions.is_empty() {
                        self.flush_block(else_block, Terminator::Goto(merge_block));
                    } else if !self.blocks.contains_key(&else_block) {
                        self.set_terminator(else_block, Terminator::Goto(merge_block));
                    }

                    current = merge_block;
                }

                Stmt::While { condition, body } => {
                    // Flush any pending instructions to current block
                    let loop_header = if self.current_instructions.is_empty() {
                        current
                    } else {
                        let bb = self.fresh_block();
                        self.flush_block(current, Terminator::Goto(bb));
                        bb
                    };

                    let body_block = self.fresh_block();
                    let after_loop = if is_last { exit } else { self.fresh_block() };

                    self.set_terminator(
                        loop_header,
                        Terminator::Branch {
                            condition: condition.clone(),
                            true_target: body_block,
                            false_target: after_loop,
                        },
                    );

                    self.build_stmts(body, body_block, loop_header);
                    // Always ensure body block exists, even if empty
                    if !self.current_instructions.is_empty() {
                        self.flush_block(body_block, Terminator::Goto(loop_header));
                    } else if !self.blocks.contains_key(&body_block) {
                        self.set_terminator(body_block, Terminator::Goto(loop_header));
                    }

                    current = after_loop;
                }
            }
        }

        // Flush any remaining instructions
        if !self.current_instructions.is_empty() {
            self.flush_block(current, Terminator::Goto(exit));
        }
    }

    /// Build CFG from statement (legacy compatibility)
    #[allow(dead_code)]
    fn build_stmt(&mut self, stmt: &Stmt, entry: BlockId, exit: BlockId) {
        self.build_stmts(std::slice::from_ref(stmt), entry, exit);
    }

    /// Finalize the CFG construction
    fn finalize(self) -> ControlFlowGraph {
        ControlFlowGraph {
            blocks: self.blocks,
            entry: self.entry,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_simple_sequence() {
        // x = true; y = false
        let stmts = vec![
            Stmt::Assign("x".into(), Expr::Lit(true)),
            Stmt::Assign("y".into(), Expr::Lit(false)),
        ];

        let cfg = ControlFlowGraph::from_stmts(&stmts);

        // Should have entry block with both assignments, and exit
        assert!(cfg.blocks.len() >= 2);
        assert_eq!(cfg.entry, 0);
    }

    #[test]
    fn test_if_statement() {
        // if x { y = true } else { y = false }
        let stmts = vec![Stmt::if_then_else(
            Expr::Var("x".into()),
            vec![Stmt::Assign("y".into(), Expr::Lit(true))],
            vec![Stmt::Assign("y".into(), Expr::Lit(false))],
        )];

        let cfg = ControlFlowGraph::from_stmts(&stmts);

        // Entry should be a branch
        let entry_block = cfg.get_block(cfg.entry).unwrap();
        match &entry_block.terminator {
            Terminator::Branch { .. } => {}
            _ => panic!("Entry should be a branch"),
        }
    }

    #[test]
    fn test_while_loop() {
        // while x { y = !y }
        let stmts = vec![Stmt::while_do(
            Expr::Var("x".into()),
            vec![Stmt::Assign("y".into(), Expr::Not(Box::new(Expr::Var("y".into()))))],
        )];

        let cfg = ControlFlowGraph::from_stmts(&stmts);

        // Entry (loop header) should be a branch
        let entry_block = cfg.get_block(cfg.entry).unwrap();
        match &entry_block.terminator {
            Terminator::Branch { true_target, .. } => {
                // Body should loop back to entry
                let body_successors = cfg.successors(*true_target);
                assert!(body_successors.contains(&cfg.entry), "Body should loop back to header");
            }
            _ => panic!("Loop header should be a branch"),
        }
    }

    #[test]
    fn test_nested_if() {
        // if x { if y { z = true } }
        let stmts = vec![Stmt::if_then(
            Expr::Var("x".into()),
            vec![Stmt::if_then(
                Expr::Var("y".into()),
                vec![Stmt::Assign("z".into(), Expr::Lit(true))],
            )],
        )];

        let cfg = ControlFlowGraph::from_stmts(&stmts);

        // Should have multiple branch points
        let mut branch_count = 0;
        for block in cfg.blocks.values() {
            if matches!(block.terminator, Terminator::Branch { .. }) {
                branch_count += 1;
            }
        }
        assert_eq!(branch_count, 2, "Should have 2 branch points for nested if");
    }

    #[test]
    fn test_nested_if_then_only() {
        // if a { if b { x = true }; y = false }
        let stmts = vec![Stmt::if_then(
            Expr::Var("a".into()),
            vec![
                Stmt::if_then(Expr::Var("b".into()), vec![Stmt::Assign("x".into(), Expr::Lit(true))]),
                Stmt::Assign("y".into(), Expr::Lit(false)),
            ],
        )];

        let cfg = ControlFlowGraph::from_stmts(&stmts);

        // Verify we have 2 branches
        let mut branch_count = 0;
        for block in cfg.blocks.values() {
            if matches!(block.terminator, Terminator::Branch { .. }) {
                branch_count += 1;
            }
        }
        assert_eq!(branch_count, 2, "Should have 2 branch points");

        // Verify y=false appears in the CFG
        let has_y_assign = cfg
            .blocks
            .values()
            .any(|b| b.instructions.iter().any(|i| matches!(i, Instruction::Assign(v, _) if v == "y")));
        assert!(has_y_assign, "Should have y = false assignment");
    }

    #[test]
    fn test_nested_if_then_else() {
        // if a { if b { x = true } else { x = false } } else { x = z }
        let stmts = vec![Stmt::if_then_else(
            Expr::Var("a".into()),
            vec![Stmt::if_then_else(
                Expr::Var("b".into()),
                vec![Stmt::Assign("x".into(), Expr::Lit(true))],
                vec![Stmt::Assign("x".into(), Expr::Lit(false))],
            )],
            vec![Stmt::Assign("x".into(), Expr::Var("z".into()))],
        )];

        let cfg = ControlFlowGraph::from_stmts(&stmts);

        // Should have 2 branch points
        let mut branch_count = 0;
        for block in cfg.blocks.values() {
            if matches!(block.terminator, Terminator::Branch { .. }) {
                branch_count += 1;
            }
        }
        assert_eq!(branch_count, 2, "Should have 2 branch points for nested if-then-else");

        // Should have 3 assignments to x (one in each path)
        let x_assign_count = cfg
            .blocks
            .values()
            .flat_map(|b| &b.instructions)
            .filter(|i| matches!(i, Instruction::Assign(v, _) if v == "x"))
            .count();
        assert_eq!(x_assign_count, 3, "Should have 3 assignments to x");
    }

    #[test]
    fn test_if_followed_by_if() {
        // if a { x = true }; if b { y = true }
        let stmts = vec![
            Stmt::if_then(Expr::Var("a".into()), vec![Stmt::Assign("x".into(), Expr::Lit(true))]),
            Stmt::if_then(Expr::Var("b".into()), vec![Stmt::Assign("y".into(), Expr::Lit(true))]),
        ];

        let cfg = ControlFlowGraph::from_stmts(&stmts);

        // Should have 2 separate branch points
        let mut branch_count = 0;
        for block in cfg.blocks.values() {
            if matches!(block.terminator, Terminator::Branch { .. }) {
                branch_count += 1;
            }
        }
        assert_eq!(branch_count, 2, "Should have 2 branch points for sequential ifs");

        // Check both variables appear
        let has_x = cfg
            .blocks
            .values()
            .any(|b| b.instructions.iter().any(|i| matches!(i, Instruction::Assign(v, _) if v == "x")));
        let has_y = cfg
            .blocks
            .values()
            .any(|b| b.instructions.iter().any(|i| matches!(i, Instruction::Assign(v, _) if v == "y")));
        assert!(has_x, "Should have x assignment");
        assert!(has_y, "Should have y assignment");
    }

    #[test]
    fn test_mutex_cfg() {
        // req1 = true; if req2 { skip } else { acquire1 = true };
        // req2 = true; if req1 { skip } else { acquire2 = true };
        // assert !(acquire1 && acquire2)
        let stmts = vec![
            Stmt::Assign("req1".into(), Expr::Lit(true)),
            Stmt::if_then_else(
                Expr::Var("req2".into()),
                vec![Stmt::Skip],
                vec![Stmt::Assign("acquire1".into(), Expr::Lit(true))],
            ),
            Stmt::Assign("req2".into(), Expr::Lit(true)),
            Stmt::if_then_else(
                Expr::Var("req1".into()),
                vec![Stmt::Skip],
                vec![Stmt::Assign("acquire2".into(), Expr::Lit(true))],
            ),
            Stmt::Assert(Expr::Var("acquire1".into()).and(Expr::Var("acquire2".into())).not()),
        ];

        let cfg = ControlFlowGraph::from_stmts(&stmts);
        println!("\n{}", cfg);

        // Verify structure
        assert!(cfg.blocks.len() > 5, "Should have multiple blocks");
    }
}
