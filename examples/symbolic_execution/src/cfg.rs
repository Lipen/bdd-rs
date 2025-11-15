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
        let mut builder = CfgBuilder::new();
        let exit = builder.fresh_block();
        builder.build_stmt(stmt, builder.entry, exit);

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

    /// Build CFG from statement, connecting entry to exit
    fn build_stmt(&mut self, stmt: &Stmt, entry: BlockId, exit: BlockId) {
        match stmt {
            Stmt::Skip => {
                // Flush any pending instructions and connect to exit
                if !self.current_instructions.is_empty() {
                    self.flush_block(entry, Terminator::Goto(exit));
                } else {
                    self.set_terminator(entry, Terminator::Goto(exit));
                }
            }

            Stmt::Assign(var, expr) => {
                // Accumulate assignment in current block
                self.add_instruction(Instruction::Assign(var.clone(), expr.clone()));
            }

            Stmt::Assert(expr) => {
                // Accumulate assertion in current block
                self.add_instruction(Instruction::Assert(expr.clone()));
            }

            Stmt::Assume(expr) => {
                // Accumulate assumption in current block
                self.add_instruction(Instruction::Assume(expr.clone()));
            }

            Stmt::Seq(s1, s2) => {
                // Process both statements, only creating intermediate blocks for control flow
                match (&**s1, &**s2) {
                    // If both are straight-line, accumulate in same block
                    (Stmt::Skip | Stmt::Assign(_, _) | Stmt::Assert(_) | Stmt::Assume(_),
                     Stmt::Skip | Stmt::Assign(_, _) | Stmt::Assert(_) | Stmt::Assume(_)) => {
                        self.build_stmt(s1, entry, exit);
                        self.build_stmt(s2, entry, exit);
                    }
                    // If s1 is straight-line and s2 is control flow
                    (Stmt::Skip | Stmt::Assign(_, _) | Stmt::Assert(_) | Stmt::Assume(_),
                     Stmt::If(_, _, _) | Stmt::While(_, _) | Stmt::Seq(_, _)) => {
                        // Accumulate s1, then handle s2
                        self.build_stmt(s1, entry, exit);
                        // Now flush and continue with s2
                        let mid = self.fresh_block();
                        self.flush_block(entry, Terminator::Goto(mid));
                        self.build_stmt(s2, mid, exit);
                        // Flush s2 if needed
                        if !self.current_instructions.is_empty() {
                            self.flush_block(mid, Terminator::Goto(exit));
                        }
                    }
                    // If s1 is control flow
                    _ => {
                        // Need intermediate block for merge point
                        let mid = self.fresh_block();
                        self.build_stmt(s1, entry, mid);
                        // After s1 completes, continue with s2 from mid
                        self.build_stmt(s2, mid, exit);
                        // Flush s2 if needed
                        if !self.current_instructions.is_empty() {
                            self.flush_block(mid, Terminator::Goto(exit));
                        }
                    }
                }
            }

            Stmt::If(cond, then_stmt, else_stmt) => {
                // Flush any pending instructions to entry block
                if !self.current_instructions.is_empty() {
                    let cond_block = self.fresh_block();
                    self.flush_block(entry, Terminator::Goto(cond_block));

                    // Branch from the new block
                    let then_block = self.fresh_block();
                    let else_block = self.fresh_block();
                    self.set_terminator(
                        cond_block,
                        Terminator::Branch {
                            condition: cond.clone(),
                            true_target: then_block,
                            false_target: else_block,
                        },
                    );

                    self.build_stmt(then_stmt, then_block, exit);
                    // Flush then branch
                    if !self.current_instructions.is_empty() {
                        self.flush_block(then_block, Terminator::Goto(exit));
                    }

                    self.build_stmt(else_stmt, else_block, exit);
                    // Flush else branch
                    if !self.current_instructions.is_empty() {
                        self.flush_block(else_block, Terminator::Goto(exit));
                    }
                } else {
                    // Entry block is empty, use it for the branch
                    let then_block = self.fresh_block();
                    let else_block = self.fresh_block();

                    self.set_terminator(
                        entry,
                        Terminator::Branch {
                            condition: cond.clone(),
                            true_target: then_block,
                            false_target: else_block,
                        },
                    );

                    self.build_stmt(then_stmt, then_block, exit);
                    // Flush then branch
                    if !self.current_instructions.is_empty() {
                        self.flush_block(then_block, Terminator::Goto(exit));
                    }

                    self.build_stmt(else_stmt, else_block, exit);
                    // Flush else branch
                    if !self.current_instructions.is_empty() {
                        self.flush_block(else_block, Terminator::Goto(exit));
                    }
                }
            }

            Stmt::While(cond, body) => {
                // Flush any pending instructions to entry block
                if !self.current_instructions.is_empty() {
                    let loop_header = self.fresh_block();
                    self.flush_block(entry, Terminator::Goto(loop_header));

                    // Loop header evaluates condition
                    let body_block = self.fresh_block();
                    self.set_terminator(
                        loop_header,
                        Terminator::Branch {
                            condition: cond.clone(),
                            true_target: body_block,
                            false_target: exit,
                        },
                    );

                    // Body loops back to header
                    self.build_stmt(body, body_block, loop_header);
                    // Flush body
                    if !self.current_instructions.is_empty() {
                        self.flush_block(body_block, Terminator::Goto(loop_header));
                    }
                } else {
                    // Entry becomes loop header
                    let body_block = self.fresh_block();
                    self.set_terminator(
                        entry,
                        Terminator::Branch {
                            condition: cond.clone(),
                            true_target: body_block,
                            false_target: exit,
                        },
                    );

                    // Body loops back to header
                    self.build_stmt(body, body_block, entry);
                    // Flush body
                    if !self.current_instructions.is_empty() {
                        self.flush_block(body_block, Terminator::Goto(entry));
                    }
                }
            }
        }
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
        // x = true
        // y = false
        let stmt = Stmt::Assign("x".into(), Expr::Lit(true)).seq(Stmt::Assign("y".into(), Expr::Lit(false)));

        let cfg = ControlFlowGraph::from_stmt(&stmt);

        // Should have entry block with x=true, intermediate with y=false, and exit
        assert!(cfg.blocks.len() >= 2);
        assert_eq!(cfg.entry, 0);
    }

    #[test]
    fn test_if_statement() {
        // if x {
        //   y = true
        // } else {
        //   y = false
        // }
        let stmt = Stmt::If(
            Expr::Var("x".into()),
            Box::new(Stmt::Assign("y".into(), Expr::Lit(true))),
            Box::new(Stmt::Assign("y".into(), Expr::Lit(false))),
        );

        let cfg = ControlFlowGraph::from_stmt(&stmt);

        // Entry should be a branch
        let entry_block = cfg.get_block(cfg.entry).unwrap();
        match &entry_block.terminator {
            Terminator::Branch { .. } => {}
            _ => panic!("Entry should be a branch"),
        }
    }

    #[test]
    fn test_while_loop() {
        // while x {
        //   y = !y
        // }
        let stmt = Stmt::While(
            Expr::Var("x".into()),
            Box::new(Stmt::Assign("y".into(), Expr::Not(Box::new(Expr::Var("y".into()))))),
        );

        let cfg = ControlFlowGraph::from_stmt(&stmt);

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
        // if x {
        //   if y {
        //     z = true
        //   }
        // }
        let stmt = Stmt::If(
            Expr::Var("x".into()),
            Box::new(Stmt::If(
                Expr::Var("y".into()),
                Box::new(Stmt::Assign("z".into(), Expr::Lit(true))),
                Box::new(Stmt::Skip),
            )),
            Box::new(Stmt::Skip),
        );

        let cfg = ControlFlowGraph::from_stmt(&stmt);

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
        // if a {
        //   if b { x = true }
        //   y = false
        // }
        // Nested if with then-only, followed by assignment
        let stmt = Stmt::If(
            Expr::Var("a".into()),
            Box::new(
                Stmt::If(
                    Expr::Var("b".into()),
                    Box::new(Stmt::Assign("x".into(), Expr::Lit(true))),
                    Box::new(Stmt::Skip),
                )
                .seq(Stmt::Assign("y".into(), Expr::Lit(false))),
            ),
            Box::new(Stmt::Skip),
        );

        let cfg = ControlFlowGraph::from_stmt(&stmt);

        // Verify we have 2 branches
        let mut branch_count = 0;
        for block in cfg.blocks.values() {
            if matches!(block.terminator, Terminator::Branch { .. }) {
                branch_count += 1;
            }
        }
        assert_eq!(branch_count, 2, "Should have 2 branch points");

        // Verify y=false appears in the CFG
        let has_y_assign = cfg.blocks.values().any(|b| {
            b.instructions
                .iter()
                .any(|i| matches!(i, Instruction::Assign(v, _) if v == "y"))
        });
        assert!(has_y_assign, "Should have y = false assignment");
    }

    #[test]
    fn test_nested_if_then_else() {
        // if a {
        //   if b {
        //     x = true
        //   } else {
        //     x = false
        //   }
        // } else {
        //   x = z
        // }
        let stmt = Stmt::If(
            Expr::Var("a".into()),
            Box::new(Stmt::If(
                Expr::Var("b".into()),
                Box::new(Stmt::Assign("x".into(), Expr::Lit(true))),
                Box::new(Stmt::Assign("x".into(), Expr::Lit(false))),
            )),
            Box::new(Stmt::Assign("x".into(), Expr::Var("z".into()))),
        );

        let cfg = ControlFlowGraph::from_stmt(&stmt);

        // Should have 2 branch points
        let mut branch_count = 0;
        for block in cfg.blocks.values() {
            if matches!(block.terminator, Terminator::Branch { .. }) {
                branch_count += 1;
            }
        }
        assert_eq!(
            branch_count, 2,
            "Should have 2 branch points for nested if-then-else"
        );

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
        // if a {
        //   x = true
        // }
        // if b {
        //   y = true
        // }
        let stmt = Stmt::If(
            Expr::Var("a".into()),
            Box::new(Stmt::Assign("x".into(), Expr::Lit(true))),
            Box::new(Stmt::Skip),
        )
        .seq(Stmt::If(
            Expr::Var("b".into()),
            Box::new(Stmt::Assign("y".into(), Expr::Lit(true))),
            Box::new(Stmt::Skip),
        ));

        let cfg = ControlFlowGraph::from_stmt(&stmt);

        // Should have 2 separate branch points
        let mut branch_count = 0;
        for block in cfg.blocks.values() {
            if matches!(block.terminator, Terminator::Branch { .. }) {
                branch_count += 1;
            }
        }
        assert_eq!(
            branch_count, 2,
            "Should have 2 branch points for sequential ifs"
        );

        // Check both variables appear
        let has_x = cfg.blocks.values().any(|b| {
            b.instructions
                .iter()
                .any(|i| matches!(i, Instruction::Assign(v, _) if v == "x"))
        });
        let has_y = cfg.blocks.values().any(|b| {
            b.instructions
                .iter()
                .any(|i| matches!(i, Instruction::Assign(v, _) if v == "y"))
        });
        assert!(has_x, "Should have x assignment");
        assert!(has_y, "Should have y assignment");
    }

    #[test]
    fn test_mutex_cfg() {
        // req1 = true
        // if req2 {
        //   skip
        // } else {
        //   acquire1 = true
        // }
        // req2 = true
        // if req1 {
        //   skip
        // } else {
        //   acquire2 = true
        // }
        // assert !(acquire1 && acquire2)
        let thread1 = Stmt::Assign("req1".into(), Expr::Lit(true)).seq(Stmt::If(
            Expr::Var("req2".into()),
            Box::new(Stmt::Skip),
            Box::new(Stmt::Assign("acquire1".into(), Expr::Lit(true))),
        ));

        let thread2 = Stmt::Assign("req2".into(), Expr::Lit(true)).seq(Stmt::If(
            Expr::Var("req1".into()),
            Box::new(Stmt::Skip),
            Box::new(Stmt::Assign("acquire2".into(), Expr::Lit(true))),
        ));

        let stmt = thread1
            .seq(thread2)
            .seq(Stmt::Assert(Expr::Var("acquire1".into()).and(Expr::Var("acquire2".into())).not()));

        let cfg = ControlFlowGraph::from_stmt(&stmt);
        println!("\n{}", cfg);

        // Verify structure
        assert!(cfg.blocks.len() > 5, "Should have multiple blocks");
    }
}
