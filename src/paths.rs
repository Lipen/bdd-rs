//! Iterator over satisfying paths in a BDD.
//!
//! This module provides an efficient iterator for enumerating all satisfying
//! assignments (paths to TRUE) in a BDD. Each path represents a conjunction
//! of literals that makes the Boolean function true.
//!
//! # Example
//!
//! ```
//! use bdd_rs::bdd::Bdd;
//!
//! let bdd = Bdd::default();
//! let x = bdd.mk_var(1);
//! let y = bdd.mk_var(2);
//!
//! // f = x XOR y (true when exactly one is true)
//! let f = bdd.apply_xor(x, y);
//!
//! // Enumerate all satisfying paths
//! let paths: Vec<_> = bdd.paths(f).collect();
//! assert_eq!(paths.len(), 2);  // {x=T, y=F} and {x=F, y=T}
//!
//! // Each path is a Vec<Lit>
//! for path in &paths {
//!     println!("Satisfying assignment: {:?}", path);
//! }
//! ```
//!
//! # Performance
//!
//! The iterator uses an efficient stack-based traversal that avoids
//! unnecessary allocations. Path vectors are only created when yielding
//! a complete satisfying assignment.
//!
//! Note: The number of paths can be exponential in the number of variables,
//! so use with caution on large BDDs.

use crate::bdd::Bdd;
use crate::reference::Ref;
use crate::types::Lit;

impl Bdd {
    /// Returns an iterator over all satisfying paths (paths to TRUE) in the BDD.
    ///
    /// Each path is a `Vec<Lit>` representing a conjunction of literals that
    /// makes the Boolean function evaluate to true. The literals are ordered
    /// by their position in the BDD (following the variable ordering).
    ///
    /// # Returns
    ///
    /// An iterator yielding `Vec<Lit>` for each satisfying assignment.
    ///
    /// # Examples
    ///
    /// ```
    /// use bdd_rs::bdd::Bdd;
    /// use bdd_rs::types::Lit;
    ///
    /// let bdd = Bdd::default();
    ///
    /// // Create a simple conjunction: x1 AND NOT x2
    /// let f = bdd.mk_cube([1, -2]);
    ///
    /// let paths: Vec<_> = bdd.paths(f).collect();
    /// assert_eq!(paths.len(), 1);
    /// assert_eq!(paths[0], vec![Lit::from(1), Lit::from(-2)]);
    /// ```
    ///
    /// ```
    /// use bdd_rs::bdd::Bdd;
    ///
    /// let bdd = Bdd::default();
    ///
    /// // Constant TRUE has exactly one path (the empty path)
    /// let paths: Vec<_> = bdd.paths(bdd.one()).collect();
    /// assert_eq!(paths.len(), 1);
    /// assert!(paths[0].is_empty());
    ///
    /// // Constant FALSE has no satisfying paths
    /// let paths: Vec<_> = bdd.paths(bdd.zero()).collect();
    /// assert_eq!(paths.len(), 0);
    /// ```
    pub fn paths(&self, f: Ref) -> BddPaths<'_> {
        BddPaths::new(self, f)
    }

    /// Returns an iterator over all paths to FALSE in the BDD.
    ///
    /// This is equivalent to `bdd.paths(-f)` but more explicit about intent.
    ///
    /// # Examples
    ///
    /// ```
    /// use bdd_rs::bdd::Bdd;
    ///
    /// let bdd = Bdd::default();
    /// let x = bdd.mk_var(1);
    ///
    /// // x has one path to TRUE (x=T) and one path to FALSE (x=F)
    /// assert_eq!(bdd.paths(x).count(), 1);
    /// assert_eq!(bdd.paths_to_false(x).count(), 1);
    /// ```
    pub fn paths_to_false(&self, f: Ref) -> BddPaths<'_> {
        BddPaths::new(self, -f)
    }
}

/// Iterator state for exploring a single node.
#[derive(Debug, Clone, Copy)]
enum Branch {
    /// About to explore the high (then) branch
    High,
    /// About to explore the low (else) branch
    Low,
}

/// Frame on the exploration stack.
#[derive(Debug)]
struct StackFrame {
    /// The BDD node reference being explored
    node: Ref,
    /// Which branch to explore next (None if both explored)
    next_branch: Option<Branch>,
}

/// An iterator over satisfying paths in a BDD.
///
/// Created by [`Bdd::paths()`]. See its documentation for details.
///
/// # Implementation Notes
///
/// Uses depth-first traversal with backtracking. The current path is maintained
/// in a single vector that grows/shrinks as we traverse, avoiding the need to
/// clone path prefixes at each branch point.
pub struct BddPaths<'a> {
    bdd: &'a Bdd,
    /// Stack of nodes being explored (for backtracking)
    stack: Vec<StackFrame>,
    /// Current path being built (reused across iterations)
    current_path: Vec<Lit>,
}

impl<'a> BddPaths<'a> {
    /// Creates a new path iterator for the given BDD.
    pub fn new(bdd: &'a Bdd, f: Ref) -> Self {
        BddPaths {
            bdd,
            stack: vec![StackFrame {
                node: f,
                next_branch: Some(Branch::High),
            }],
            current_path: Vec::new(),
        }
    }
}

impl Iterator for BddPaths<'_> {
    type Item = Vec<Lit>;

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            // Get the current frame, or return None if stack is empty
            let frame = self.stack.last_mut()?;
            let node = frame.node;
            let next_branch = frame.next_branch;

            // Terminal cases - check first before exploring branches
            if self.bdd.is_one(node) {
                // Found a satisfying path - return a copy
                let result = self.current_path.clone();
                // Pop this terminal frame
                self.stack.pop();
                // Pop the literal that led us here (unless we're at root)
                if !self.stack.is_empty() {
                    self.current_path.pop();
                }
                return Some(result);
            }

            if self.bdd.is_zero(node) {
                // Dead end - backtrack
                self.stack.pop();
                // Pop the literal that led us here (unless we're at root)
                if !self.stack.is_empty() {
                    self.current_path.pop();
                }
                continue;
            }

            // Decision node - explore branches based on state
            let var = self.bdd.variable(node.id());

            match next_branch {
                Some(Branch::High) => {
                    // First, explore high branch (var = true)
                    frame.next_branch = Some(Branch::Low);
                    let high_child = self.bdd.high_node(node);
                    self.current_path.push(Lit::pos(var));
                    self.stack.push(StackFrame {
                        node: high_child,
                        next_branch: Some(Branch::High),
                    });
                }
                Some(Branch::Low) => {
                    // Now explore low branch (var = false)
                    // The high literal was already popped when we backtracked from high child
                    frame.next_branch = None; // Mark as fully explored
                    let low_child = self.bdd.low_node(node);
                    self.current_path.push(Lit::neg(var));
                    self.stack.push(StackFrame {
                        node: low_child,
                        next_branch: Some(Branch::High),
                    });
                }
                None => {
                    // Both branches explored - backtrack
                    self.stack.pop();
                    // Pop the literal that led us to this node (unless we're at root)
                    if !self.stack.is_empty() {
                        self.current_path.pop();
                    }
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn path_to_string(path: &[Lit]) -> String {
        path.iter().map(|lit| lit.to_string()).collect::<Vec<_>>().join(", ")
    }

    fn mk_path(lits: impl IntoIterator<Item = i32>) -> Vec<Lit> {
        lits.into_iter().map(|x| Lit::from(x)).collect()
    }

    #[test]
    fn test_paths_single_cube() {
        let bdd = Bdd::default();
        let f = bdd.mk_cube([1, -2, 3]);

        let paths: Vec<_> = bdd.paths(f).collect();
        println!("Found {} paths", paths.len());
        for path in &paths {
            println!("  [{}]", path_to_string(path));
        }

        assert_eq!(paths.len(), 1);
        let expected = mk_path([1, -2, 3]);
        assert_eq!(paths[0], expected);
    }

    #[test]
    fn test_paths_two_cubes() {
        let bdd = Bdd::default();
        let c1 = bdd.mk_cube([1, -2, 3]);
        let c2 = bdd.mk_cube([1, 2, -3]);
        let f = bdd.apply_or(c1, c2);

        let paths: Vec<_> = bdd.paths(f).collect();
        println!("Found {} paths", paths.len());
        for path in &paths {
            println!("  [{}]", path_to_string(path));
        }

        assert_eq!(paths.len(), 2);

        let expected1 = mk_path([1, -2, 3]);
        let expected2 = mk_path([1, 2, -3]);

        assert!(paths.contains(&expected1));
        assert!(paths.contains(&expected2));
    }

    #[test]
    fn test_paths_constant_one() {
        let bdd = Bdd::default();

        let paths: Vec<_> = bdd.paths(bdd.one()).collect();
        println!("Found {} paths", paths.len());
        for path in &paths {
            println!("  [{}]", path_to_string(path));
        }

        assert_eq!(paths.len(), 1);
        assert!(paths[0].is_empty());
    }

    #[test]
    fn test_paths_constant_zero() {
        let bdd = Bdd::default();

        let paths: Vec<_> = bdd.paths(bdd.zero()).collect();
        println!("Found {} paths", paths.len());
        for path in &paths {
            println!("  [{}]", path_to_string(path));
        }

        assert_eq!(paths.len(), 0);
    }

    #[test]
    fn test_paths_single_variable() {
        let bdd = Bdd::default();
        let x = bdd.mk_var(1);

        // Paths to TRUE for x: just {x=true}
        let paths: Vec<_> = bdd.paths(x).collect();
        assert_eq!(paths.len(), 1);
        assert_eq!(paths[0], mk_path([1]));

        // Paths to TRUE for NOT x: just {x=false}
        let paths: Vec<_> = bdd.paths(-x).collect();
        assert_eq!(paths.len(), 1);
        assert_eq!(paths[0], mk_path([-1]));
    }

    #[test]
    fn test_paths_xor() {
        let bdd = Bdd::default();
        let x = bdd.mk_var(1);
        let y = bdd.mk_var(2);
        let xor = bdd.apply_xor(x, y);

        let paths: Vec<_> = bdd.paths(xor).collect();
        println!("Found {} paths", paths.len());
        for path in &paths {
            println!("  [{}]", path_to_string(path));
        }

        // XOR has exactly 2 satisfying assignments
        assert_eq!(paths.len(), 2);

        let expected1 = mk_path([1, -2]);
        let expected2 = mk_path([-1, 2]);

        assert!(paths.contains(&expected1));
        assert!(paths.contains(&expected2));
    }

    #[test]
    fn test_paths_to_false() {
        let bdd = Bdd::default();
        let x = bdd.mk_var(1);
        let y = bdd.mk_var(2);
        let and = bdd.apply_and(x, y);

        // Paths to FALSE for (x AND y): {x=F}, {x=T, y=F}
        let paths: Vec<_> = bdd.paths_to_false(and).collect();
        println!("Found {} paths", paths.len());
        for path in &paths {
            println!("  [{}]", path_to_string(path));
        }

        assert_eq!(paths.len(), 2);
    }

    #[test]
    fn test_paths_or() {
        let bdd = Bdd::default();
        let x = bdd.mk_var(1);
        let y = bdd.mk_var(2);
        let or = bdd.apply_or(x, y);

        let paths: Vec<_> = bdd.paths(or).collect();
        println!("Found {} paths", paths.len());
        for path in &paths {
            println!("  [{}]", path_to_string(path));
        }

        // OR BDD structure: x --high--> TRUE, x --low--> y --high--> TRUE, y --low--> FALSE
        // So we get 2 paths in the BDD (x=T covers both x=T,y=T and x=T,y=F)
        assert_eq!(paths.len(), 2);

        // Verify the paths
        let expected1 = mk_path([1]); // x=T (y is don't care)
        let expected2 = mk_path([-1, 2]); // x=F, y=T
        assert!(paths.contains(&expected1));
        assert!(paths.contains(&expected2));
    }

    #[test]
    fn test_paths_negated_function() {
        let bdd = Bdd::default();
        let f = bdd.mk_cube([-1, -2, -3]);

        // Count paths to TRUE for f and NOT f
        let paths_f: Vec<_> = bdd.paths(f).collect();
        let paths_not_f: Vec<_> = bdd.paths(-f).collect();

        // f has 1 path (all negative): x1=F, x2=F, x3=F
        assert_eq!(paths_f.len(), 1);

        // NOT f = x1 OR x2 OR x3
        // BDD paths: x1=T, or x1=F,x2=T, or x1=F,x2=F,x3=T
        // That's 3 BDD paths (not 7 satisfying assignments)
        assert_eq!(paths_not_f.len(), 3);
    }

    #[test]
    fn test_paths_equivalence_with_dimacs() {
        // Verify that the new Lit-based API is equivalent to the old i32 approach
        let bdd = Bdd::default();
        let f = bdd.mk_cube([1, -2, 3]);

        let paths: Vec<_> = bdd.paths(f).collect();

        // Convert to DIMACS-style for comparison
        let dimacs_paths: Vec<Vec<i32>> = paths.iter().map(|path| path.iter().map(|lit| lit.to_dimacs()).collect()).collect();

        assert_eq!(dimacs_paths, vec![vec![1, -2, 3]]);
    }
}
