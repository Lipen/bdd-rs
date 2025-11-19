//! Chapter 2: Control Flow Graph Builder
//!
//! This example shows how to build and analyze control flow graphs.
//! CFGs are fundamental for abstract interpretation.

use std::collections::{HashMap, HashSet};
use std::fmt;

/// Basic block identifier
pub type BlockId = usize;

/// CFG node types
#[derive(Debug, Clone)]
pub enum Node {
    /// Entry point
    Entry,
    /// Statement: variable assignment
    Assign(String, String),
    /// Conditional branch
    Condition(String),
    /// Exit point
    Exit,
}

/// Control Flow Graph
#[derive(Debug)]
pub struct CFG {
    blocks: HashMap<BlockId, Node>,
    edges: HashMap<BlockId, Vec<(BlockId, EdgeLabel)>>,
    entry: BlockId,
    exits: HashSet<BlockId>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum EdgeLabel {
    Unconditional,
    True,
    False,
}

impl CFG {
    pub fn new() -> Self {
        let mut cfg = Self {
            blocks: HashMap::new(),
            edges: HashMap::new(),
            entry: 0,
            exits: HashSet::new(),
        };
        cfg.blocks.insert(0, Node::Entry);
        cfg
    }

    /// Add a basic block
    pub fn add_block(&mut self, id: BlockId, node: Node) {
        self.blocks.insert(id, node);
    }

    /// Add an edge between blocks
    pub fn add_edge(&mut self, from: BlockId, to: BlockId, label: EdgeLabel) {
        self.edges.entry(from).or_insert_with(Vec::new).push((to, label));
    }

    /// Mark a block as an exit
    pub fn mark_exit(&mut self, id: BlockId) {
        self.exits.insert(id);
    }

    /// Get all paths from entry to exit
    pub fn enumerate_paths(&self) -> Vec<Vec<BlockId>> {
        let mut paths = Vec::new();
        let mut current_path = vec![self.entry];
        self.dfs_paths(self.entry, &mut current_path, &mut paths);
        paths
    }

    fn dfs_paths(&self, current: BlockId, path: &mut Vec<BlockId>, all_paths: &mut Vec<Vec<BlockId>>) {
        if self.exits.contains(&current) {
            all_paths.push(path.clone());
            return;
        }

        if let Some(successors) = self.edges.get(&current) {
            for (next, _) in successors {
                if !path.contains(next) {
                    // Avoid cycles for now
                    path.push(*next);
                    self.dfs_paths(*next, path, all_paths);
                    path.pop();
                }
            }
        }
    }

    /// Count paths (exponential in branches)
    pub fn count_paths(&self) -> usize {
        self.enumerate_paths().len()
    }
}

impl fmt::Display for CFG {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "CFG with {} blocks:", self.blocks.len())?;
        for (id, node) in &self.blocks {
            write!(f, "  Block {}: {:?}", id, node)?;
            if let Some(edges) = self.edges.get(id) {
                write!(f, " -> ")?;
                for (target, label) in edges {
                    write!(f, "{}({:?}) ", target, label)?;
                }
            }
            writeln!(f)?;
        }
        Ok(())
    }
}

fn main() {
    println!("=== Control Flow Graph Example ===\n");

    // Build CFG for:
    // if x > 0 {
    //     result = x
    // } else {
    //     result = -x
    // }
    let mut cfg = CFG::new();

    cfg.add_block(1, Node::Condition("x > 0".to_string()));
    cfg.add_block(2, Node::Assign("result".to_string(), "x".to_string()));
    cfg.add_block(3, Node::Assign("result".to_string(), "-x".to_string()));
    cfg.add_block(4, Node::Exit);

    cfg.add_edge(0, 1, EdgeLabel::Unconditional); // Entry -> Condition
    cfg.add_edge(1, 2, EdgeLabel::True); // Condition -> Then
    cfg.add_edge(1, 3, EdgeLabel::False); // Condition -> Else
    cfg.add_edge(2, 4, EdgeLabel::Unconditional); // Then -> Exit
    cfg.add_edge(3, 4, EdgeLabel::Unconditional); // Else -> Exit

    cfg.mark_exit(4);

    println!("{}", cfg);

    let paths = cfg.enumerate_paths();
    println!("Number of paths: {}", paths.len());
    println!("Paths:");
    for (i, path) in paths.iter().enumerate() {
        println!("  Path {}: {:?}", i + 1, path);
    }
    println!();

    // Demonstrate path explosion with nested conditionals
    println!("=== Path Explosion Demo ===\n");

    let mut cfg2 = CFG::new();
    // Build: if c1 { if c2 { if c3 { ... } } }
    let n = 5; // Number of nested conditions

    for i in 1..=n {
        cfg2.add_block(i, Node::Condition(format!("c{}", i)));
        cfg2.add_block(n + i, Node::Assign("x".to_string(), format!("branch{}", i)));
    }

    cfg2.add_block(2 * n + 1, Node::Exit);

    // Wire up nested structure
    cfg2.add_edge(0, 1, EdgeLabel::Unconditional);
    for i in 1..n {
        cfg2.add_edge(i, i + 1, EdgeLabel::True);
        cfg2.add_edge(i, n + i, EdgeLabel::False);
        cfg2.add_edge(n + i, 2 * n + 1, EdgeLabel::Unconditional);
    }
    cfg2.add_edge(n, n + n, EdgeLabel::True);
    cfg2.add_edge(n, n + n, EdgeLabel::False);
    cfg2.add_edge(2 * n, 2 * n + 1, EdgeLabel::Unconditional);

    cfg2.mark_exit(2 * n + 1);

    println!("CFG with {} nested conditionals:", n);
    println!("  Number of blocks: {}", cfg2.blocks.len());
    println!("  Number of paths: 2^{} = {}", n, 1 << n);
    println!();
    println!("Path explosion:");
    for i in 1..=10 {
        println!("  {} conditionals => {} paths", i, 1 << i);
    }
    println!("\n  => Need symbolic representation to avoid enumeration!");
}
