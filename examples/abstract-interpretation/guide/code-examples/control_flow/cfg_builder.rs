//! Chapter 2: Control Flow Graph Builder
//!
//! This example shows how to build and analyze control flow graphs using Basic Blocks.
//! CFGs are fundamental for abstract interpretation.

use std::collections::HashMap;
use std::fmt;

/// Basic block identifier
pub type BlockId = usize;

/// A basic block: a sequence of instructions ending with a terminator
#[derive(Debug, Clone)]
pub struct BasicBlock {
    pub id: BlockId,
    pub instructions: Vec<Instruction>,
    pub terminator: Terminator,
}

/// Instructions within a basic block
#[derive(Debug, Clone)]
pub enum Instruction {
    Assign(String, String), // x = expr (simplified as string)
    Assert(String),         // assert(expr)
}

/// Terminator: how a basic block ends
#[derive(Debug, Clone)]
pub enum Terminator {
    Goto(BlockId),
    Branch {
        condition: String,
        true_target: BlockId,
        false_target: BlockId,
    },
    Return,
}

/// Control Flow Graph
#[derive(Debug)]
pub struct CFG {
    pub blocks: HashMap<BlockId, BasicBlock>,
    pub entry: BlockId,
}

impl CFG {
    pub fn new() -> Self {
        Self {
            blocks: HashMap::new(),
            entry: 0,
        }
    }

    /// Add a basic block
    pub fn add_block(&mut self, block: BasicBlock) {
        self.blocks.insert(block.id, block);
    }

    /// Get all paths from entry to exit (Return)
    pub fn enumerate_paths(&self) -> Vec<Vec<BlockId>> {
        let mut paths = Vec::new();
        let mut current_path = vec![self.entry];
        self.dfs_paths(self.entry, &mut current_path, &mut paths);
        paths
    }

    fn dfs_paths(&self, current: BlockId, path: &mut Vec<BlockId>, all_paths: &mut Vec<Vec<BlockId>>) {
        let block = self.blocks.get(&current).expect("Block not found");

        match &block.terminator {
            Terminator::Return => {
                all_paths.push(path.clone());
            }
            Terminator::Goto(next) => {
                if !path.contains(next) {
                    // Avoid cycles
                    path.push(*next);
                    self.dfs_paths(*next, path, all_paths);
                    path.pop();
                }
            }
            Terminator::Branch {
                true_target, false_target, ..
            } => {
                for next in [true_target, false_target] {
                    if !path.contains(next) {
                        // Avoid cycles
                        path.push(*next);
                        self.dfs_paths(*next, path, all_paths);
                        path.pop();
                    }
                }
            }
        }
    }
}

impl fmt::Display for CFG {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "CFG with {} blocks:", self.blocks.len())?;
        // Sort blocks for consistent output
        let mut ids: Vec<_> = self.blocks.keys().collect();
        ids.sort();

        for id in ids {
            let block = &self.blocks[id];
            writeln!(f, "  Block {}:", id)?;
            for instr in &block.instructions {
                match instr {
                    Instruction::Assign(var, expr) => writeln!(f, "    {} = {}", var, expr)?,
                    Instruction::Assert(expr) => writeln!(f, "    assert({})", expr)?,
                }
            }
            match &block.terminator {
                Terminator::Goto(target) => writeln!(f, "    goto {}", target)?,
                Terminator::Branch {
                    condition,
                    true_target,
                    false_target,
                } => writeln!(f, "    if {} then goto {} else goto {}", condition, true_target, false_target)?,
                Terminator::Return => writeln!(f, "    return")?,
            }
        }
        Ok(())
    }
}

fn main() {
    println!("=== Control Flow Graph Example (Basic Blocks) ===\n");

    // Build CFG for:
    // if x > 0 {
    //     result = x
    // } else {
    //     result = -x
    // }
    // return

    let mut cfg = CFG::new();

    // Block 0: Entry + Branch
    cfg.add_block(BasicBlock {
        id: 0,
        instructions: vec![],
        terminator: Terminator::Branch {
            condition: "x > 0".to_string(),
            true_target: 1,
            false_target: 2,
        },
    });

    // Block 1: Then branch
    cfg.add_block(BasicBlock {
        id: 1,
        instructions: vec![Instruction::Assign("result".to_string(), "x".to_string())],
        terminator: Terminator::Goto(3), // Join
    });

    // Block 2: Else branch
    cfg.add_block(BasicBlock {
        id: 2,
        instructions: vec![Instruction::Assign("result".to_string(), "-x".to_string())],
        terminator: Terminator::Goto(3), // Join
    });

    // Block 3: Join + Return
    cfg.add_block(BasicBlock {
        id: 3,
        instructions: vec![],
        terminator: Terminator::Return,
    });

    println!("{}", cfg);

    let paths = cfg.enumerate_paths();
    println!("Number of paths: {}", paths.len());
    println!("Paths (Block IDs):");
    for (i, path) in paths.iter().enumerate() {
        println!("  Path {}: {:?}", i + 1, path);
    }
    println!();

    // Demonstrate path explosion with nested conditionals
    println!("=== Path Explosion Demo ===\n");

    let mut cfg2 = CFG::new();
    // Build: if c1 { if c2 { ... } }
    let n = 5; // Number of nested conditions

    // We will create a chain of blocks.
    // Block i branches to i+1 (true) and n+i (false, which then goes to exit)
    // This is a bit simplified to show explosion.

    // Actually, let's build a full tree for maximum explosion
    // Level 0: 1 block
    // Level 1: 2 blocks
    // ...
    // But that requires 2^n blocks.

    // Let's build the "diamond" structure which is common in sequential ifs:
    // if c1 { ... }
    // if c2 { ... }
    // This creates 2^n paths with only 2*n blocks.

    for i in 0..n {
        // Block 2*i: Branch
        cfg2.add_block(BasicBlock {
            id: 2 * i,
            instructions: vec![],
            terminator: Terminator::Branch {
                condition: format!("c{}", i + 1),
                true_target: 2 * i + 1,  // Then block
                false_target: 2 * i + 2, // Next merge block (skip then)
            },
        });

        // Block 2*i + 1: Then body
        cfg2.add_block(BasicBlock {
            id: 2 * i + 1,
            instructions: vec![Instruction::Assign("x".to_string(), format!("val{}", i + 1))],
            terminator: Terminator::Goto(2 * i + 2), // Go to merge
        });

        // Block 2*i + 2 is the start of the next condition (or exit)
    }

    // Final block
    cfg2.add_block(BasicBlock {
        id: 2 * n,
        instructions: vec![],
        terminator: Terminator::Return,
    });

    println!("CFG with {} sequential conditionals:", n);
    println!("  Number of blocks: {}", cfg2.blocks.len());

    let paths2 = cfg2.enumerate_paths();
    println!("  Number of paths: 2^{} = {}", n, paths2.len());

    println!("\n  => Need symbolic representation to avoid enumeration!");
}
