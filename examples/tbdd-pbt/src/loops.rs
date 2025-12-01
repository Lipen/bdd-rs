//! Loop handling for T-BDD.
//!
//! This module provides loop detection for CFGs. Loops are handled during
//! path enumeration by tracking iteration counts, not by cloning the CFG.
//!
//! ## Overview
//!
//! Loops create infinite path spaces. T-BDD handles this through:
//! 1. **Detection** — Find back edges and natural loops
//! 2. **Bounded Exploration** — Track iteration counts during path enumeration
//!
//! ## Example
//!
//! ```rust,ignore
//! use tbdd_pbt::loops::LoopDetector;
//!
//! let cfg = build_cfg_with_loop();
//! let loops = LoopDetector::detect(&cfg);
//!
//! for loop_info in &loops {
//!     println!("Loop at {}, depth {}", loop_info.header, loop_info.nesting_depth);
//! }
//!
//! // Enumerate paths with loop bound of 3
//! let paths = cfg.enumerate_paths_bounded(&loops, 3);
//! ```

use std::collections::{HashMap, HashSet, VecDeque};

use crate::cfg::{BlockId, ControlFlowGraph};

/// Information about a detected loop.
#[derive(Debug, Clone)]
pub struct LoopInfo {
    /// The loop header (entry point, target of back edge).
    pub header: BlockId,
    /// The tail block (source of back edge).
    pub tail: BlockId,
    /// All blocks in the loop body (excluding header).
    pub body: HashSet<BlockId>,
    /// Blocks that exit the loop.
    pub exit_targets: Vec<BlockId>,
    /// Nesting depth (0 = outermost).
    pub nesting_depth: usize,
    /// Parent loop header (if nested).
    pub parent: Option<BlockId>,
}

impl LoopInfo {
    /// Check if a block is part of this loop (header or body).
    pub fn contains(&self, block: BlockId) -> bool {
        block == self.header || self.body.contains(&block)
    }

    /// Check if an edge is a back edge for this loop.
    pub fn is_back_edge(&self, from: BlockId, to: BlockId) -> bool {
        self.contains(from) && to == self.header
    }
}

/// Detector for natural loops in a CFG.
///
/// Uses dominator analysis to find back edges, then computes loop bodies
/// via backward reachability.
pub struct LoopDetector {
    dominators: HashMap<BlockId, HashSet<BlockId>>,
    loops: Vec<LoopInfo>,
}

impl LoopDetector {
    /// Detect all natural loops in a CFG.
    pub fn detect(cfg: &ControlFlowGraph) -> Vec<LoopInfo> {
        let mut detector = Self {
            dominators: HashMap::new(),
            loops: Vec::new(),
        };

        detector.compute_dominators(cfg);
        detector.find_back_edges(cfg);
        detector.compute_loop_bodies(cfg);
        detector.compute_nesting();

        detector.loops
    }

    /// Compute dominators using iterative dataflow.
    fn compute_dominators(&mut self, cfg: &ControlFlowGraph) {
        let all_blocks: HashSet<BlockId> = cfg.blocks.iter().map(|b| b.id).collect();

        // Initialize
        for block in &cfg.blocks {
            if block.id == cfg.entry {
                self.dominators.insert(cfg.entry, HashSet::from([cfg.entry]));
            } else {
                self.dominators.insert(block.id, all_blocks.clone());
            }
        }

        // Iterate until fixed point
        let mut changed = true;
        while changed {
            changed = false;

            for block in &cfg.blocks {
                if block.id == cfg.entry {
                    continue;
                }

                let preds = cfg.predecessors(block.id);
                if preds.is_empty() {
                    continue;
                }

                // Dom(B) = {B} ∪ (∩ Dom(pred) for pred in predecessors)
                let mut new_dom: HashSet<BlockId> = self.dominators[&preds[0]].clone();
                for pred in &preds[1..] {
                    new_dom = new_dom.intersection(&self.dominators[pred]).copied().collect();
                }
                new_dom.insert(block.id);

                if new_dom != self.dominators[&block.id] {
                    self.dominators.insert(block.id, new_dom);
                    changed = true;
                }
            }
        }
    }

    /// Find back edges (edge to a dominator).
    fn find_back_edges(&mut self, cfg: &ControlFlowGraph) {
        for block in &cfg.blocks {
            for succ in cfg.successors(block.id) {
                if let Some(doms) = self.dominators.get(&block.id) {
                    if doms.contains(&succ) && succ != block.id {
                        // Back edge: block -> succ (succ dominates block)
                        self.loops.push(LoopInfo {
                            header: succ,
                            tail: block.id,
                            body: HashSet::new(),
                            exit_targets: Vec::new(),
                            nesting_depth: 0,
                            parent: None,
                        });
                    }
                }
            }
        }
    }

    /// Compute loop bodies via backward reachability from tail.
    fn compute_loop_bodies(&mut self, cfg: &ControlFlowGraph) {
        for loop_info in &mut self.loops {
            let mut body = HashSet::new();
            let mut worklist = VecDeque::new();

            // Start from tail, find all blocks reachable backward without crossing header
            body.insert(loop_info.header);
            if loop_info.tail != loop_info.header {
                body.insert(loop_info.tail);
                worklist.push_back(loop_info.tail);
            }

            while let Some(block) = worklist.pop_front() {
                for pred in cfg.predecessors(block) {
                    if !body.contains(&pred) {
                        body.insert(pred);
                        worklist.push_back(pred);
                    }
                }
            }

            // Find exit targets (successors outside the loop)
            for &block in &body {
                for succ in cfg.successors(block) {
                    if !body.contains(&succ) && !loop_info.exit_targets.contains(&succ) {
                        loop_info.exit_targets.push(succ);
                    }
                }
            }

            // Header is not part of body (body = blocks between header and tail)
            body.remove(&loop_info.header);
            loop_info.body = body;
        }
    }

    /// Compute nesting relationships between loops.
    fn compute_nesting(&mut self) {
        // Sort by body size (smaller = more deeply nested)
        self.loops.sort_by_key(|l| l.body.len());

        let headers: Vec<BlockId> = self.loops.iter().map(|l| l.header).collect();

        for i in 0..self.loops.len() {
            for j in (i + 1)..self.loops.len() {
                // Check if loop i is nested in loop j
                let i_header = self.loops[i].header;
                let j_contains_i = self.loops[j].body.contains(&i_header) || self.loops[j].header == i_header;

                if j_contains_i && self.loops[i].parent.is_none() {
                    self.loops[i].parent = Some(headers[j]);
                    self.loops[i].nesting_depth = self.loops[j].nesting_depth + 1;
                }
            }
        }
    }
}

/// Find which loop (if any) a block belongs to.
pub fn find_containing_loop<'a>(block: BlockId, loops: &'a [LoopInfo]) -> Option<&'a LoopInfo> {
    // Return innermost (smallest) loop containing this block
    loops.iter().filter(|l| l.contains(block)).min_by_key(|l| l.body.len())
}

/// Check if an edge is a back edge for any loop.
pub fn is_back_edge(from: BlockId, to: BlockId, loops: &[LoopInfo]) -> bool {
    loops.iter().any(|l| l.is_back_edge(from, to))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::cfg::CfgBuilder;
    use crate::predicate::Predicate;

    fn build_simple_loop() -> ControlFlowGraph {
        let mut builder = CfgBuilder::new();

        let entry = builder.entry();
        let header = builder.new_block("header");
        let body = builder.new_block("body");
        let exit = builder.new_block("exit");

        builder.add_goto(entry, header);
        builder.add_branch(header, Predicate::lt("i", 10), body, exit);
        builder.add_goto(body, header);
        builder.add_return(exit);

        builder.build()
    }

    #[test]
    fn test_loop_detection() {
        let cfg = build_simple_loop();
        let loops = LoopDetector::detect(&cfg);

        assert_eq!(loops.len(), 1);
        assert_eq!(loops[0].header, BlockId(1)); // header block
        assert!(loops[0].body.contains(&BlockId(2))); // body block
        assert_eq!(loops[0].exit_targets, vec![BlockId(3)]); // exit block
    }

    #[test]
    fn test_back_edge_detection() {
        let cfg = build_simple_loop();
        let loops = LoopDetector::detect(&cfg);

        // body -> header is a back edge
        assert!(is_back_edge(BlockId(2), BlockId(1), &loops));
        // entry -> header is not a back edge
        assert!(!is_back_edge(BlockId(0), BlockId(1), &loops));
    }

    #[test]
    fn test_nested_loops() {
        let mut builder = CfgBuilder::new();

        let entry = builder.entry();
        let outer_header = builder.new_block("outer_header");
        let inner_header = builder.new_block("inner_header");
        let inner_body = builder.new_block("inner_body");
        let outer_body = builder.new_block("outer_body");
        let exit = builder.new_block("exit");

        builder.add_goto(entry, outer_header);
        builder.add_branch(outer_header, Predicate::lt("i", 10), inner_header, exit);
        builder.add_branch(inner_header, Predicate::lt("j", 10), inner_body, outer_body);
        builder.add_goto(inner_body, inner_header);
        builder.add_goto(outer_body, outer_header);
        builder.add_return(exit);

        let cfg = builder.build();
        let loops = LoopDetector::detect(&cfg);

        assert_eq!(loops.len(), 2);

        // Inner loop should be nested (has parent)
        let inner = loops.iter().find(|l| l.header == BlockId(2)).unwrap();
        assert!(inner.parent.is_some());
        assert_eq!(inner.nesting_depth, 1);

        // Outer loop should be at depth 0
        let outer = loops.iter().find(|l| l.header == BlockId(1)).unwrap();
        assert!(outer.parent.is_none());
        assert_eq!(outer.nesting_depth, 0);
    }

    #[test]
    fn test_find_containing_loop() {
        let cfg = build_simple_loop();
        let loops = LoopDetector::detect(&cfg);

        // Header is in the loop
        assert!(find_containing_loop(BlockId(1), &loops).is_some());
        // Body is in the loop
        assert!(find_containing_loop(BlockId(2), &loops).is_some());
        // Exit is not in the loop
        assert!(find_containing_loop(BlockId(3), &loops).is_none());
        // Entry is not in the loop
        assert!(find_containing_loop(BlockId(0), &loops).is_none());
    }
}
