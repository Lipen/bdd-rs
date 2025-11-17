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
    pub trap_context: Option<TrapContext>,
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
    /// Throw exception
    Throw(Expr),
    /// Catch exception: optionally bind to variable
    Catch(Option<Var>),
}

impl fmt::Display for Instruction {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Instruction::Assign(v, e) => write!(f, "{} = {}", v, e),
            Instruction::Assert(e) => write!(f, "assert {}", e),
            Instruction::Assume(e) => write!(f, "assume {}", e),
            Instruction::Throw(e) => write!(f, "throw {}", e),
            Instruction::Catch(Some(v)) => write!(f, "catch ({})", v),
            Instruction::Catch(None) => write!(f, "catch"),
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

#[derive(Debug, Clone)]
pub struct TrapContext {
    pub catch_variable: Option<Var>,
    pub catch_target: Option<BlockId>,
    pub finally_target: Option<BlockId>,
    pub parent: Option<BlockId>, // for nested try
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
            writeln!(f, "bb{}:", id)?;
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
    /// Current trap context (for nested try-catch)
    current_trap_context: Option<TrapContext>,
}

impl CfgBuilder {
    fn new() -> Self {
        let entry = 0;
        CfgBuilder {
            next_block_id: 1,
            blocks: HashMap::new(),
            entry,
            current_instructions: Vec::new(),
            current_trap_context: None,
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
        self.flush_block_with_trap(block_id, terminator, None);
    }

    /// Flush accumulated instructions into a block with terminator and trap context
    fn flush_block_with_trap(&mut self, block_id: BlockId, terminator: Terminator, trap_context: Option<TrapContext>) {
        let instructions = std::mem::take(&mut self.current_instructions);
        let block = BasicBlock {
            id: block_id,
            instructions,
            terminator,
            trap_context,
        };
        self.blocks.insert(block_id, block);
    }

    /// Set terminator for a block (assumes no instructions pending)
    fn set_terminator(&mut self, block_id: BlockId, terminator: Terminator) {
        self.set_terminator_with_trap(block_id, terminator, None);
    }

    /// Set terminator with trap context for a block
    fn set_terminator_with_trap(&mut self, block_id: BlockId, terminator: Terminator, trap_context: Option<TrapContext>) {
        if let Some(block) = self.blocks.get_mut(&block_id) {
            block.terminator = terminator;
            block.trap_context = trap_context;
        } else {
            // Block doesn't exist yet, create it empty
            let block = BasicBlock {
                id: block_id,
                instructions: Vec::new(),
                terminator,
                trap_context,
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

                Stmt::Throw(expr) => {
                    // Throw is an instruction that will be handled during execution
                    // The trap_context in the containing block determines where control flows
                    self.add_instruction(Instruction::Throw(expr.clone()));
                }

                Stmt::Try {
                    try_body,
                    catch_var,
                    catch_body,
                    finally_body,
                } => {
                    // Determine the try block entry point
                    let try_block = if self.current_instructions.is_empty() {
                        // Reuse current block as try block (no need for transition)
                        current
                    } else {
                        // Flush pending instructions and create fresh try block
                        let try_bb = self.fresh_block();
                        self.flush_block(current, Terminator::Goto(try_bb));
                        try_bb
                    };

                    // Create blocks for catch, finally, and after
                    let catch_block = if !catch_body.is_empty() { Some(self.fresh_block()) } else { None };
                    let finally_block = if !finally_body.is_empty() { Some(self.fresh_block()) } else { None };
                    let after_block = if is_last { exit } else { self.fresh_block() };

                    // Build trap context for try block, with parent set to current outer context
                    let parent_catch_block = self.current_trap_context.as_ref().and_then(|ctx| ctx.catch_target);
                    let trap_context = TrapContext {
                        catch_variable: catch_var.clone(),
                        catch_target: catch_block,
                        finally_target: finally_block,
                        parent: parent_catch_block,
                    };

                    // Remember which blocks existed before building try body
                    let existing_blocks: std::collections::HashSet<_> = self.blocks.keys().copied().collect();

                    // Save current trap context and set new one for nested try blocks
                    let saved_trap_context = self.current_trap_context.clone();
                    self.current_trap_context = Some(trap_context.clone());

                    // Build try block - normal exit goes to finally if present, otherwise after
                    let try_exit = finally_block.unwrap_or(after_block);
                    self.build_stmts(try_body, try_block, try_exit);

                    // Restore previous trap context
                    self.current_trap_context = saved_trap_context;

                    // Flush any remaining instructions
                    if !self.current_instructions.is_empty() {
                        self.flush_block(try_block, Terminator::Goto(try_exit));
                    } else if !self.blocks.contains_key(&try_block) {
                        self.set_terminator(try_block, Terminator::Goto(try_exit));
                    }

                    // Apply trap_context to ALL new blocks created during try body construction
                    // (excluding catch, finally, and after blocks which are handlers/continuation)
                    for (&block_id, block) in self.blocks.iter_mut() {
                        // Skip blocks that existed before, and handler/continuation blocks
                        if existing_blocks.contains(&block_id) {
                            continue;
                        }
                        if Some(block_id) == catch_block || Some(block_id) == finally_block || block_id == after_block {
                            continue;
                        }
                        // Apply trap context if not already set
                        if block.trap_context.is_none() {
                            block.trap_context = Some(trap_context.clone());
                        }
                    }

                    // Build catch block if present - also goes to finally
                    if let Some(cb) = catch_block {
                        // Insert Catch instruction at the beginning of catch block
                        self.add_instruction(Instruction::Catch(catch_var.clone()));
                        self.build_stmts(catch_body, cb, finally_block.unwrap_or(after_block));
                        if !self.current_instructions.is_empty() {
                            self.flush_block(cb, Terminator::Goto(finally_block.unwrap_or(after_block)));
                        } else if !self.blocks.contains_key(&cb) {
                            self.set_terminator(cb, Terminator::Goto(finally_block.unwrap_or(after_block)));
                        }
                    }

                    // Build finally block if present
                    if let Some(fb) = finally_block {
                        self.build_stmts(finally_body, fb, after_block);
                        if !self.current_instructions.is_empty() {
                            self.flush_block(fb, Terminator::Goto(after_block));
                        } else if !self.blocks.contains_key(&fb) {
                            self.set_terminator(fb, Terminator::Goto(after_block));
                        }
                    }

                    current = after_block;
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

    #[test]
    fn test_try_catch_finally() {
        // try { x = true; if error { throw x; } y = false; } catch (e) { y = e; } finally { z = y; }
        let stmts = vec![Stmt::Try {
            try_body: vec![
                Stmt::Assign("x".into(), Expr::Lit(true)),
                Stmt::if_then(Expr::Var("error".into()), vec![Stmt::Throw(Expr::Var("x".into()))]),
                Stmt::Assign("y".into(), Expr::Lit(false)),
            ],
            catch_var: Some("e".into()),
            catch_body: vec![Stmt::Assign("y".into(), Expr::Var("e".into()))],
            finally_body: vec![Stmt::Assign("z".into(), Expr::Var("y".into()))],
        }];

        let cfg = ControlFlowGraph::from_stmts(&stmts);
        println!("\n{}", cfg);

        // Verify try block has trap context
        let try_blocks: Vec<_> = cfg.blocks.values().filter(|b| b.trap_context.is_some()).collect();
        assert!(!try_blocks.is_empty(), "Should have blocks with trap context");

        // Verify structure has try, catch, finally blocks
        assert!(cfg.blocks.len() >= 5, "Should have multiple blocks for try-catch-finally");
    }

    #[test]
    fn test_simple_throw() {
        // x = true; throw x
        let stmts = vec![Stmt::Assign("x".into(), Expr::Lit(true)), Stmt::Throw(Expr::Var("x".into()))];

        let cfg = ControlFlowGraph::from_stmts(&stmts);
        println!("\n{}", cfg);

        // Verify throw instruction exists
        let has_throw = cfg
            .blocks
            .values()
            .any(|b| b.instructions.iter().any(|i| matches!(i, Instruction::Throw(_))));
        assert!(has_throw, "Should have throw instruction");
    }

    #[test]
    fn test_nested_try_catch() {
        // try {
        //   x = true;
        //   try {
        //     y = true;
        //     if inner_error { throw y; }
        //   } catch (e1) {
        //     y = e1;
        //   }
        //   if outer_error { throw x; }
        // } catch (e2) {
        //   x = e2;
        // }
        let stmts = vec![Stmt::Try {
            try_body: vec![
                Stmt::Assign("x".into(), Expr::Lit(true)),
                Stmt::Try {
                    try_body: vec![
                        Stmt::Assign("y".into(), Expr::Lit(true)),
                        Stmt::if_then(Expr::Var("inner_error".into()), vec![Stmt::Throw(Expr::Var("y".into()))]),
                    ],
                    catch_var: Some("e1".into()),
                    catch_body: vec![Stmt::Assign("y".into(), Expr::Var("e1".into()))],
                    finally_body: vec![],
                },
                Stmt::if_then(Expr::Var("outer_error".into()), vec![Stmt::Throw(Expr::Var("x".into()))]),
            ],
            catch_var: Some("e2".into()),
            catch_body: vec![Stmt::Assign("x".into(), Expr::Var("e2".into()))],
            finally_body: vec![],
        }];

        let cfg = ControlFlowGraph::from_stmts(&stmts);
        println!("\n{}", cfg);

        // Verify we have blocks with trap context
        let trap_blocks: Vec<_> = cfg.blocks.values().filter(|b| b.trap_context.is_some()).collect();
        assert!(!trap_blocks.is_empty(), "Should have blocks with trap context");

        // Verify nested structure: inner try blocks should have parent pointing to outer catch
        let mut found_nested_context = false;
        for block in &trap_blocks {
            if let Some(trap_ctx) = &block.trap_context {
                if trap_ctx.parent.is_some() {
                    found_nested_context = true;
                    // Verify parent points to a valid catch block
                    let parent_id = trap_ctx.parent.unwrap();
                    assert!(cfg.blocks.contains_key(&parent_id), "Parent catch block should exist");
                }
            }
        }
        assert!(found_nested_context, "Should have nested trap context with parent set");

        // Verify we have two catch blocks (one for inner, one for outer)
        let catch_instruction_count = cfg
            .blocks
            .values()
            .flat_map(|b| &b.instructions)
            .filter(|i| matches!(i, Instruction::Catch(_)))
            .count();
        assert_eq!(catch_instruction_count, 2, "Should have 2 catch instructions");
    }

    #[test]
    fn test_nested_finally() {
        // try {
        //   x = true;
        //   try {
        //     y = true;
        //   } catch (e1) {
        //     z = e1;
        //   } finally {
        //     inner_finally = true;
        //   }
        //   after_inner = true;
        // } catch (e2) {
        //   outer_catch = true;
        // } finally {
        //   outer_finally = true;
        // }
        let stmts = vec![Stmt::Try {
            try_body: vec![
                Stmt::Assign("x".into(), Expr::Lit(true)),
                Stmt::Try {
                    try_body: vec![Stmt::Assign("y".into(), Expr::Lit(true))],
                    catch_var: Some("e1".into()),
                    catch_body: vec![Stmt::Assign("z".into(), Expr::Var("e1".into()))],
                    finally_body: vec![Stmt::Assign("inner_finally".into(), Expr::Lit(true))],
                },
                Stmt::Assign("after_inner".into(), Expr::Lit(true)),
            ],
            catch_var: Some("e2".into()),
            catch_body: vec![Stmt::Assign("outer_catch".into(), Expr::Lit(true))],
            finally_body: vec![Stmt::Assign("outer_finally".into(), Expr::Lit(true))],
        }];

        let cfg = ControlFlowGraph::from_stmts(&stmts);
        println!("\n{}", cfg);

        // Verify we have finally blocks
        let has_inner_finally = cfg.blocks.values().any(|b| {
            b.instructions
                .iter()
                .any(|i| matches!(i, Instruction::Assign(v, _) if v == "inner_finally"))
        });
        let has_outer_finally = cfg.blocks.values().any(|b| {
            b.instructions
                .iter()
                .any(|i| matches!(i, Instruction::Assign(v, _) if v == "outer_finally"))
        });
        assert!(has_inner_finally, "Should have inner finally block");
        assert!(has_outer_finally, "Should have outer finally block");

        // Verify after_inner exists (comes after inner try-catch-finally)
        let has_after_inner = cfg.blocks.values().any(|b| {
            b.instructions
                .iter()
                .any(|i| matches!(i, Instruction::Assign(v, _) if v == "after_inner"))
        });
        assert!(has_after_inner, "Should have after_inner assignment");
    }

    #[test]
    fn test_finally_in_catch() {
        // try {
        //   x = true;
        // } catch (e) {
        //   in_catch = e;
        //   try {
        //     nested_in_catch = true;
        //   } catch (e2) {
        //     nested_catch = e2;
        //   } finally {
        //     nested_finally = true;
        //   }
        // }
        let stmts = vec![Stmt::Try {
            try_body: vec![Stmt::Assign("x".into(), Expr::Lit(true))],
            catch_var: Some("e".into()),
            catch_body: vec![
                Stmt::Assign("in_catch".into(), Expr::Var("e".into())),
                Stmt::Try {
                    try_body: vec![Stmt::Assign("nested_in_catch".into(), Expr::Lit(true))],
                    catch_var: Some("e2".into()),
                    catch_body: vec![Stmt::Assign("nested_catch".into(), Expr::Var("e2".into()))],
                    finally_body: vec![Stmt::Assign("nested_finally".into(), Expr::Lit(true))],
                },
            ],
            finally_body: vec![],
        }];

        let cfg = ControlFlowGraph::from_stmts(&stmts);
        println!("\n{}", cfg);

        // Verify all assignments are present
        let has_in_catch = cfg.blocks.values().any(|b| {
            b.instructions
                .iter()
                .any(|i| matches!(i, Instruction::Assign(v, _) if v == "in_catch"))
        });
        let has_nested_finally = cfg.blocks.values().any(|b| {
            b.instructions
                .iter()
                .any(|i| matches!(i, Instruction::Assign(v, _) if v == "nested_finally"))
        });

        assert!(has_in_catch, "Should have in_catch assignment");
        assert!(has_nested_finally, "Should have nested_finally in catch block");
    }

    #[test]
    fn test_multiple_finally() {
        // try {
        //   try {
        //     x = true;
        //   } finally {
        //     finally1 = true;
        //   }
        //   try {
        //     y = true;
        //   } finally {
        //     finally2 = true;
        //   }
        // } finally {
        //   outer_finally = true;
        // }
        let stmts = vec![Stmt::Try {
            try_body: vec![
                Stmt::Try {
                    try_body: vec![Stmt::Assign("x".into(), Expr::Lit(true))],
                    catch_var: None,
                    catch_body: vec![],
                    finally_body: vec![Stmt::Assign("finally1".into(), Expr::Lit(true))],
                },
                Stmt::Try {
                    try_body: vec![Stmt::Assign("y".into(), Expr::Lit(true))],
                    catch_var: None,
                    catch_body: vec![],
                    finally_body: vec![Stmt::Assign("finally2".into(), Expr::Lit(true))],
                },
            ],
            catch_var: None,
            catch_body: vec![],
            finally_body: vec![Stmt::Assign("outer_finally".into(), Expr::Lit(true))],
        }];

        let cfg = ControlFlowGraph::from_stmts(&stmts);
        println!("\n{}", cfg);

        // Verify all three finally blocks exist
        let has_finally1 = cfg.blocks.values().any(|b| {
            b.instructions
                .iter()
                .any(|i| matches!(i, Instruction::Assign(v, _) if v == "finally1"))
        });
        let has_finally2 = cfg.blocks.values().any(|b| {
            b.instructions
                .iter()
                .any(|i| matches!(i, Instruction::Assign(v, _) if v == "finally2"))
        });
        let has_outer_finally = cfg.blocks.values().any(|b| {
            b.instructions
                .iter()
                .any(|i| matches!(i, Instruction::Assign(v, _) if v == "outer_finally"))
        });

        assert!(has_finally1, "Should have finally1 block");
        assert!(has_finally2, "Should have finally2 block");
        assert!(has_outer_finally, "Should have outer_finally block");
    }

    #[test]
    fn test_finally_without_catch() {
        // try {
        //   x = true;
        // } finally {
        //   y = true;
        // }
        let stmts = vec![Stmt::Try {
            try_body: vec![Stmt::Assign("x".into(), Expr::Lit(true))],
            catch_var: None,
            catch_body: vec![],
            finally_body: vec![Stmt::Assign("y".into(), Expr::Lit(true))],
        }];

        let cfg = ControlFlowGraph::from_stmts(&stmts);
        println!("\n{}", cfg);

        // Verify finally block exists even without catch
        let has_finally = cfg
            .blocks
            .values()
            .any(|b| b.instructions.iter().any(|i| matches!(i, Instruction::Assign(v, _) if v == "y")));
        assert!(has_finally, "Should have finally block even without catch");

        // Verify no catch instruction exists
        let has_catch = cfg
            .blocks
            .values()
            .flat_map(|b| &b.instructions)
            .any(|i| matches!(i, Instruction::Catch(_)));
        assert!(!has_catch, "Should not have catch instruction when no catch block");
    }

    #[test]
    fn test_exception_flow_with_finally() {
        // Verify exception propagates through finally blocks:
        // try {
        //   x = true;
        //   throw x;
        // } catch (e) {
        //   y = e;
        // } finally {
        //   z = true;
        // }
        let stmts = vec![Stmt::Try {
            try_body: vec![Stmt::Assign("x".into(), Expr::Lit(true)), Stmt::Throw(Expr::Var("x".into()))],
            catch_var: Some("e".into()),
            catch_body: vec![Stmt::Assign("y".into(), Expr::Var("e".into()))],
            finally_body: vec![Stmt::Assign("z".into(), Expr::Lit(true))],
        }];

        let cfg = ControlFlowGraph::from_stmts(&stmts);
        println!("\n{}", cfg);

        // Find throw block
        let throw_block_id = cfg
            .blocks
            .iter()
            .find(|(_, b)| b.instructions.iter().any(|i| matches!(i, Instruction::Throw(_))))
            .map(|(id, _)| *id);
        assert!(throw_block_id.is_some(), "Should have throw instruction");

        // Verify throw block has trap context
        let throw_block = cfg.get_block(throw_block_id.unwrap()).unwrap();
        assert!(throw_block.trap_context.is_some(), "Throw block should have trap context");

        // Verify trap context points to catch and finally
        let trap_ctx = throw_block.trap_context.as_ref().unwrap();
        assert!(trap_ctx.catch_target.is_some(), "Should have catch target");
        assert!(trap_ctx.finally_target.is_some(), "Should have finally target");

        // Verify catch and finally blocks exist and have correct instructions
        let catch_block = cfg.get_block(trap_ctx.catch_target.unwrap()).unwrap();
        assert!(
            catch_block.instructions.iter().any(|i| matches!(i, Instruction::Catch(_))),
            "Catch block should have Catch instruction"
        );

        let finally_block = cfg.get_block(trap_ctx.finally_target.unwrap()).unwrap();
        assert!(
            finally_block
                .instructions
                .iter()
                .any(|i| matches!(i, Instruction::Assign(v, _) if v == "z")),
            "Finally block should have z assignment"
        );
    }
}
