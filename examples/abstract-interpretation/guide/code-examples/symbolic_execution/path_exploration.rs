//! Path Exploration Strategies for Symbolic Execution
//!
//! **Guide Reference:** Part I, Chapter 6 - "Symbolic Execution" & Part III, Chapter 18 - "Performance"
//!
//! This example demonstrates different strategies for exploring program paths
//! in symbolic execution, addressing the **path explosion problem**.
//!
//! ## The Path Explosion Problem
//!
//! Programs with `n` conditionals can have up to `2^n` paths.
//! Exploring all paths quickly becomes intractable:
//! - 10 branches: 1,024 paths
//! - 20 branches: 1,048,576 paths
//! - 30 branches: 1,073,741,824 paths (1 billion!)
//!
//! ## Exploration Strategies
//!
//! ### 1. Depth-First Search (DFS)
//! - Explores deeply before backtracking
//! - Memory efficient (stack-based)
//! - May get stuck in deep paths
//! - Good for finding deep bugs quickly
//!
//! ### 2. Breadth-First Search (BFS)
//! - Explores all paths at depth `d` before `d+1`
//! - Fair coverage across paths
//! - High memory usage (exponential worklist)
//! - Good for finding shallow bugs
//!
//! ### 3. Bounded Depth
//! - Limits exploration to depth `k`
//! - Ensures termination with completeness guarantee
//! - May miss deep bugs beyond bound
//! - Practical trade-off for large programs
//!
//! ## Advanced Strategies (Not Implemented Here)
//!
//! - **Random Path Selection**: Heuristic for coverage
//! - **Concolic Testing**: Mix concrete and symbolic execution
//! - **Prioritized Worklist**: Target specific code/bugs
//! - **State Merging**: Combine similar paths with BDDs
//!
//! ## Practical Considerations
//!
//! Real-world symbolic execution tools use:
//! - **Timeouts**: Bound execution time per path
//! - **State Pruning**: Discard unlikely or redundant states
//! - **Incremental Solving**: Reuse constraint solving work
//! - **Parallel Exploration**: Distribute across cores/machines
//!
//! ## Expected Output
//!
//! Run with: `cargo run --example path_exploration`
//!
//! Compares DFS, BFS, and bounded strategies on programs with
//! varying numbers of conditionals, showing coverage and performance trade-offs.

use std::collections::{HashSet, VecDeque};
use std::rc::Rc;

use ananke_bdd::bdd::Bdd;
use ananke_bdd::reference::Ref;
use num_bigint::BigUint;

/// Path in the program (sequence of branch decisions)
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Path {
    decisions: Vec<bool>, // true = then, false = else
}

impl Path {
    pub fn new() -> Self {
        Self { decisions: Vec::new() }
    }

    pub fn extend(&self, decision: bool) -> Self {
        let mut new_path = self.clone();
        new_path.decisions.push(decision);
        new_path
    }

    pub fn len(&self) -> usize {
        self.decisions.len()
    }
}

/// Path exploration strategies
pub enum Strategy {
    /// Depth-First Search
    DFS,
    /// Breadth-First Search
    BFS,
    /// Bounded depth (limit exploration depth)
    Bounded(usize),
}

/// Path explorer with different strategies
pub struct PathExplorer {
    explored: HashSet<Path>,
    worklist: VecDeque<Path>,
    strategy: Strategy,
}

impl PathExplorer {
    pub fn new(strategy: Strategy) -> Self {
        Self {
            explored: HashSet::new(),
            worklist: VecDeque::new(),
            strategy,
        }
    }

    /// Explore program with given number of conditionals
    pub fn explore(&mut self, num_conditionals: usize) -> usize {
        self.explored.clear();
        self.worklist.clear();
        self.worklist.push_back(Path::new());

        let mut paths_explored = 0;

        while let Some(path) = self.pop_path() {
            if self.explored.contains(&path) {
                continue;
            }

            // Check depth bound
            if let Strategy::Bounded(max_depth) = self.strategy {
                if path.len() >= max_depth {
                    self.explored.insert(path);
                    paths_explored += 1;
                    continue;
                }
            }

            // If path is complete
            if path.len() >= num_conditionals {
                self.explored.insert(path);
                paths_explored += 1;
                continue;
            }

            // Fork: explore both branches
            let then_path = path.extend(true);
            let else_path = path.extend(false);

            match self.strategy {
                Strategy::DFS => {
                    // Push else first (so then is popped first)
                    self.worklist.push_back(else_path);
                    self.worklist.push_back(then_path);
                }
                Strategy::BFS | Strategy::Bounded(_) => {
                    // Enqueue both
                    self.worklist.push_back(then_path);
                    self.worklist.push_back(else_path);
                }
            }

            self.explored.insert(path);
            paths_explored += 1;
        }

        paths_explored
    }

    fn pop_path(&mut self) -> Option<Path> {
        match self.strategy {
            Strategy::DFS => self.worklist.pop_back(),
            Strategy::BFS | Strategy::Bounded(_) => self.worklist.pop_front(),
        }
    }
}

/// Symbolic path condition using BDD
pub struct SymbolicPathCondition {
    bdd: Rc<Bdd>,
    condition: Ref,
}

impl SymbolicPathCondition {
    pub fn new(bdd: Rc<Bdd>) -> Self {
        let condition = bdd.mk_true();
        Self { bdd, condition }
    }

    /// Add branch condition (var = true for then, false for else)
    pub fn add_branch(&mut self, var_id: u32, direction: bool) {
        let var = self.bdd.mk_var(var_id);
        let constraint = if direction { var } else { self.bdd.apply_not(var) };
        self.condition = self.bdd.apply_and(self.condition, constraint);
    }

    /// Check if path condition is feasible
    pub fn is_feasible(&self) -> bool {
        self.condition != self.bdd.mk_false()
    }

    /// Count satisfying assignments (possible inputs)
    pub fn count_solutions(&self, num_vars: usize) -> BigUint {
        self.bdd.sat_count(self.condition, num_vars)
    }
}

fn main() {
    println!("=== Path Exploration Strategies ===\n");

    // Example 1: DFS vs BFS
    println!("Example 1: DFS vs BFS");
    println!("  Program with 5 nested conditionals\n");

    let mut dfs_explorer = PathExplorer::new(Strategy::DFS);
    let paths_dfs = dfs_explorer.explore(5);
    println!("  DFS explored: {} states (32 complete paths)", paths_dfs);

    let mut bfs_explorer = PathExplorer::new(Strategy::BFS);
    let paths_bfs = bfs_explorer.explore(5);
    println!("  BFS explored: {} states (32 complete paths)", paths_bfs);

    println!("  Both explore all 2^5 = 32 complete paths\n");

    // Example 2: Bounded exploration
    println!("Example 2: Bounded Depth Search");
    println!("  Limit exploration to depth 3\n");

    let mut bounded_explorer = PathExplorer::new(Strategy::Bounded(3));
    let paths_bounded = bounded_explorer.explore(10);
    println!("  Bounded(3) on 10 conditionals: {} states explored", paths_bounded);
    println!("  Avoids full exponential blow-up\n");

    // Example 3: Path explosion
    println!("Example 3: Path Explosion");
    println!("  n conditionals => 2^n paths\n");

    for n in 1..=12 {
        let total_paths = 1u64 << n;
        println!("  {} conditionals => {} paths", n, total_paths);
        if n == 10 {
            println!("       (feasible to explore)");
        } else if n == 20 {
            println!("       (1 million paths)");
        }
    }
    println!();

    // Example 4: Symbolic representation
    println!("Example 4: Symbolic Path Conditions");
    println!("  Represent all paths with BDD\n");

    let bdd = Rc::new(Bdd::default());

    // Build path condition for: (c1 ∧ c2) ∨ (¬c1 ∧ c3)
    let c1 = bdd.mk_var(1);
    let c2 = bdd.mk_var(2);
    let c3 = bdd.mk_var(3);

    let path1 = bdd.apply_and(c1, c2);
    let path2 = bdd.apply_and(bdd.apply_not(c1), c3);
    let all_paths = bdd.apply_or(path1, path2);

    let solutions = bdd.sat_count(all_paths, 3);
    println!("  Formula: (c1 ∧ c2) ∨ (¬c1 ∧ c3)");
    println!("  Satisfying assignments: {}", solutions);
    println!("  Represents multiple paths symbolically!\n");

    // Example 5: Feasibility checking
    println!("Example 5: Path Feasibility");
    let mut pc1 = SymbolicPathCondition::new(bdd.clone());
    pc1.add_branch(1, true); // c1 = true
    pc1.add_branch(2, true); // c2 = true
    println!("  Path condition: c1 ∧ c2");
    println!("  Feasible: {}", pc1.is_feasible());
    println!("  Solutions: {}", pc1.count_solutions(2));

    let mut pc2 = SymbolicPathCondition::new(bdd.clone());
    pc2.add_branch(1, true); // c1 = true
    pc2.add_branch(1, false); // c1 = false (contradiction!)
    println!("\n  Path condition: c1 ∧ ¬c1");
    println!("  Feasible: {}", pc2.is_feasible());
    println!("  Solutions: {}", pc2.count_solutions(2));
    println!("  => Infeasible path detected!\n");

    println!("=== Strategy Comparison ===");
    println!("DFS:");
    println!("  ✓ Memory efficient (stack-based)");
    println!("  ✗ May get stuck in deep paths");
    println!();
    println!("BFS:");
    println!("  ✓ Finds shortest paths first");
    println!("  ✗ High memory usage (queue grows)");
    println!();
    println!("Bounded:");
    println!("  ✓ Limits explosion");
    println!("  ✗ May miss deep bugs");
    println!();
    println!("Symbolic (BDD-based):");
    println!("  ✓ Represents many paths compactly");
    println!("  ✓ Fast feasibility checking");
    println!("  ✓ Efficient join/meet operations");
}
