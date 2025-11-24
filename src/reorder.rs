//! Variable ordering and reordering for BDDs.
//!
//! # Theory: Variable Ordering
//!
//! The size of a BDD representing a Boolean function is highly sensitive to the order
//! in which variables appear in the decision diagram. For some functions, different orderings
//! can cause the BDD size to vary from linear to exponential in the number of variables.
//!
//! ## Why Ordering Matters
//!
//! Consider the function `f = (x₁ ∧ y₁) ∨ (x₂ ∧ y₂) ∨ ... ∨ (xₙ ∧ yₙ)`:
//!
//! - **Good ordering** (x₁, y₁, x₂, y₂, ..., xₙ, yₙ): O(n) nodes
//!   Related variables are close together, enabling more sharing
//!
//! - **Bad ordering** (x₁, x₂, ..., xₙ, y₁, y₂, ..., yₙ): O(2ⁿ) nodes
//!   Related variables are far apart, preventing sharing
//!
//! ## Finding Optimal Orderings
//!
//! Finding the optimal variable ordering is NP-complete. Instead, we use heuristic
//! algorithms that iteratively improve the ordering by local transformations.
//!
//! # Rudell's Sifting Algorithm
//!
//! **Sifting** is a dynamic reordering algorithm that moves each variable through
//! all possible positions to find its locally optimal placement.
//!
//! ## Algorithm Overview
//!
//! For each variable v (in some order):
//! 1. Record the current BDD size
//! 2. Move v to the top position (by swapping with adjacent variables)
//! 3. Move v down through all positions, tracking size at each position
//! 4. Place v at the position that gave the minimum BDD size
//! 5. Move to the next variable
//!
//! ## Complexity
//!
//! - **Time**: O(n² · m · log m) where n = #variables, m = #nodes
//!   - Each variable is sifted once: O(n)
//!   - Each sift involves O(n) swaps
//!   - Each swap rebuilds affected nodes: O(m · log m)
//!
//! - **Space**: O(m) for storing the BDD
//!
//! ## Practical Considerations
//!
//! 1. **Order of sifting**: Sift variables in decreasing order of support size
//!    (variables appearing in more nodes are sifted first)
//!
//! 2. **Early termination**: Stop if size increases by more than a threshold
//!
//! 3. **Symmetric variables**: Variables that can be freely swapped without
//!    changing BDD size can be grouped
//!
//! # Window Permutation
//!
//! An alternative to sifting that considers small windows of k consecutive variables
//! and tries all k! permutations to find the best local ordering.
//!
//! - **Window size 2**: Equivalent to bubble sort
//! - **Window size 3**: Tries all 6 permutations
//! - **Larger windows**: More thorough but exponentially more expensive
//!
//! # References
//!
//! - R. Rudell. "Dynamic variable ordering for ordered binary decision diagrams."
//!   ICCAD 1993. DOI: 10.1109/ICCAD.1993.580054
//!
//! - C. Meinel & T. Theobald. "Algorithms and Data Structures in VLSI Design."
//!   Springer, 1998. Chapter 4.
//!
//! - R. Bryant. "Graph-Based Algorithms for Boolean Function Manipulation."
//!   IEEE Trans. Computers, 1986.

use std::collections::{HashMap, HashSet};

use log::debug;

use crate::bdd::Bdd;
use crate::reference::Ref;

/// Statistics collected during reordering.
#[derive(Debug, Clone, Default)]
pub struct ReorderStats {
    /// Number of variable swaps performed
    pub swaps: usize,
    /// Initial BDD size (number of nodes)
    pub initial_size: usize,
    /// Final BDD size after reordering
    pub final_size: usize,
    /// Best size seen during reordering
    pub best_size: usize,
    /// Number of variables reordered
    pub variables_processed: usize,
}

impl ReorderStats {
    /// Calculate the size reduction ratio.
    pub fn reduction_ratio(&self) -> f64 {
        if self.initial_size == 0 {
            return 0.0;
        }
        1.0 - (self.final_size as f64 / self.initial_size as f64)
    }

    /// Calculate the percentage reduction.
    pub fn reduction_percent(&self) -> f64 {
        self.reduction_ratio() * 100.0
    }
}

impl Bdd {
    /// Swap two adjacent variables in the variable ordering.
    ///
    /// This is the fundamental operation for dynamic variable reordering.
    /// Swapping variables x and y (where x comes immediately before y) modifies
    /// the BDD structure to reflect the new ordering.
    ///
    /// # Algorithm
    ///
    /// For each node with variable x, we create new nodes with variable y
    /// that preserve the same Boolean function. The transformation is:
    ///
    /// ```text
    ///     x                    y
    ///    / \                  / \
    ///   L   H      =>        L'  H'
    ///  /|  /|               /|  /|
    /// y y  y y             x x  x x
    /// ```
    ///
    /// # Arguments
    ///
    /// * `roots` - Set of BDD roots to update after swapping
    /// * `level` - The level of the first variable to swap (0-indexed)
    ///
    /// # Panics
    ///
    /// Panics if `level` is out of bounds or if the variables at `level` and `level+1`
    /// are not adjacent in the current ordering.
    ///
    /// # Examples
    ///
    /// ```
    /// use bdd_rs::bdd::Bdd;
    ///
    /// let bdd = Bdd::default();
    /// let x = bdd.mk_var(1);
    /// let y = bdd.mk_var(2);
    /// let f = bdd.apply_and(x, y);
    ///
    /// // Swap variables at levels 0 and 1
    /// let mut roots = vec![f];
    /// bdd.swap_adjacent_variables(&mut roots, 0);
    /// ```
    pub fn swap_adjacent_variables(&self, roots: &mut [Ref], level: u32) {
        // Get variables at the two levels
        let var_x = level + 1; // Variables are 1-indexed
        let var_y = var_x + 1;

        debug!("Swapping variables {} and {}", var_x, var_y);

        // For each root, compute the swapped version
        for root in roots.iter_mut() {
            *root = self.swap_variables_in_bdd(*root, var_x, var_y);
        }

        debug!("Swap complete");
    }

    /// Swap two adjacent variables in a single BDD.
    ///
    /// This uses the Shannon expansion approach:
    /// To swap x and y in f, we compute:
    /// f' = ITE(y, ITE(x, f[x←1,y←1], f[x←0,y←1]), ITE(x, f[x←1,y←0], f[x←0,y←0]))
    fn swap_variables_in_bdd(&self, f: Ref, var_x: u32, var_y: u32) -> Ref {
        // Get the four cofactors
        let f00 = self.cofactor_cube(f, &[-(var_x as i32), -(var_y as i32)]);
        let f01 = self.cofactor_cube(f, &[-(var_x as i32), var_y as i32]);
        let f10 = self.cofactor_cube(f, &[var_x as i32, -(var_y as i32)]);
        let f11 = self.cofactor_cube(f, &[var_x as i32, var_y as i32]);

        // Build the swapped BDD: y on top, x below
        // When y=0: ITE(x, f10, f00)
        // When y=1: ITE(x, f11, f01)
        let y_var = self.mk_var(var_y);
        let x_var = self.mk_var(var_x);

        let when_y0 = self.apply_ite(x_var, f10, f00);
        let when_y1 = self.apply_ite(x_var, f11, f01);

        self.apply_ite(y_var, when_y1, when_y0)
    }

    /// Sift a single variable to find its optimal position.
    ///
    /// This is the core operation of Rudell's sifting algorithm. The variable
    /// is moved through all possible positions (from top to bottom), and the
    /// BDD size is measured at each position. Finally, the variable is placed
    /// at the position that minimized the BDD size.
    ///
    /// # Algorithm
    ///
    /// 1. Move the variable to the top (level 0) by repeated swaps
    /// 2. Record size at each position as we move down
    /// 3. Find the position with minimum size
    /// 4. Move the variable back to that optimal position
    ///
    /// # Arguments
    ///
    /// * `roots` - The BDD roots to optimize
    /// * `var` - The variable to sift
    /// * `num_vars` - Total number of variables
    ///
    /// # Returns
    ///
    /// The number of swaps performed and the size reduction achieved
    pub fn sift_variable(&self, roots: &mut [Ref], var: u32, num_vars: u32) -> (usize, i64) {
        if num_vars <= 1 {
            return (0, 0);
        }

        let initial_size = self.count_nodes(roots) as i64;
        let mut swaps = 0;

        // Find current level of the variable
        let mut current_level = var - 1; // Convert to 0-indexed level

        // Record sizes at each level
        let mut sizes: Vec<(u32, usize)> = Vec::new();
        sizes.push((current_level, initial_size as usize));

        debug!("Sifting variable {} (initially at level {})", var, current_level);

        // Move variable up to level 0
        while current_level > 0 {
            self.swap_adjacent_variables(roots, current_level - 1);
            current_level -= 1;
            swaps += 1;

            let size = self.count_nodes(roots);
            sizes.push((current_level, size));
            debug!("  After swap to level {}: size = {}", current_level, size);
        }

        // Now move it down through all positions
        while current_level < num_vars - 1 {
            self.swap_adjacent_variables(roots, current_level);
            current_level += 1;
            swaps += 1;

            let size = self.count_nodes(roots);
            sizes.push((current_level, size));
            debug!("  After swap to level {}: size = {}", current_level, size);
        }

        // Find the level with minimum size
        let (best_level, best_size) = sizes.iter().min_by_key(|(_, size)| size).copied().unwrap();

        debug!("  Best position: level {} with size {}", best_level, best_size);

        // Move variable back to the best position
        while current_level > best_level {
            self.swap_adjacent_variables(roots, current_level - 1);
            current_level -= 1;
            swaps += 1;
        }

        let final_size = self.count_nodes(roots) as i64;
        let size_reduction = initial_size - final_size;

        debug!(
            "Sifting complete: {} swaps, size: {} -> {} (reduction: {})",
            swaps, initial_size, final_size, size_reduction
        );

        (swaps, size_reduction)
    }

    /// Perform Rudell's sifting algorithm on all variables.
    ///
    /// This iterates through all variables (in decreasing order of usage count)
    /// and sifts each one to find its locally optimal position. This process
    /// can significantly reduce BDD size for many functions.
    ///
    /// # Algorithm
    ///
    /// 1. Compute usage counts for all variables
    /// 2. Sort variables by usage count (descending)
    /// 3. For each variable (in sorted order):
    ///    a. Sift the variable through all positions
    ///    b. Place it at the position with minimum BDD size
    ///
    /// # Arguments
    ///
    /// * `roots` - The BDD roots to optimize
    ///
    /// # Returns
    ///
    /// Statistics about the reordering process
    pub fn sift_all_variables(&self, roots: &mut [Ref]) -> ReorderStats {
        let initial_size = self.count_nodes(roots);
        debug!("Starting sifting with initial size: {}", initial_size);

        // Get all variables that appear in the BDDs
        let mut all_vars = HashSet::new();
        for &root in roots.iter() {
            all_vars.extend(self.support_variables(root));
        }

        if all_vars.is_empty() {
            return ReorderStats {
                initial_size,
                final_size: initial_size,
                best_size: initial_size,
                ..Default::default()
            };
        }

        let num_vars = *all_vars.iter().max().unwrap();

        // Get usage counts to determine sifting order
        let usage_counts = self.variable_usage_counts(roots);

        // Sort variables by usage count (descending)
        let mut vars_to_sift: Vec<u32> = all_vars.into_iter().collect();
        vars_to_sift.sort_by(|a, b| {
            let count_a = usage_counts.get(a).copied().unwrap_or(0);
            let count_b = usage_counts.get(b).copied().unwrap_or(0);
            count_b.cmp(&count_a) // Descending order
        });

        debug!("Sifting {} variables in order: {:?}", vars_to_sift.len(), vars_to_sift);

        let mut total_swaps = 0;
        let mut best_size = initial_size;

        // Sift each variable
        for &var in &vars_to_sift {
            debug!("Sifting variable {}", var);
            let (swaps, _reduction) = self.sift_variable(roots, var, num_vars);
            total_swaps += swaps;

            let current_size = self.count_nodes(roots);
            if current_size < best_size {
                best_size = current_size;
            }
        }

        let final_size = self.count_nodes(roots);

        debug!(
            "Sifting complete: size {} -> {} ({:.1}% reduction), {} swaps, {} variables",
            initial_size,
            final_size,
            100.0 * (1.0 - (final_size as f64 / initial_size as f64)),
            total_swaps,
            vars_to_sift.len()
        );

        ReorderStats {
            swaps: total_swaps,
            initial_size,
            final_size,
            best_size,
            variables_processed: vars_to_sift.len(),
        }
    }

    /// Count the total number of nodes in a set of BDDs.
    ///
    /// This efficiently counts the total number of unique nodes reachable
    /// from the given set of roots, avoiding double-counting shared nodes.
    /// This matches the behavior of `size()` - counting unique node indices
    /// including the ONE terminal but not counting separate visits.
    ///
    /// # Arguments
    ///
    /// * `roots` - BDD roots to count nodes for
    ///
    /// # Returns
    ///
    /// The total number of unique nodes (including ONE terminal)
    pub fn count_nodes(&self, roots: &[Ref]) -> usize {
        let mut visited = HashSet::new();
        visited.insert(self.one.index());

        for &root in roots {
            let mut stack = vec![root.index()];

            while let Some(idx) = stack.pop() {
                if visited.insert(idx) {
                    let node = self.node(idx);
                    let low = node.low.index();
                    if low != 1 {
                        stack.push(low);
                    }
                    let high = node.high.index();
                    if high != 1 {
                        stack.push(high);
                    }
                }
            }
        }

        visited.len()
    }

    /// Get the variables that appear in a BDD.
    ///
    /// # Arguments
    ///
    /// * `root` - BDD root to analyze
    ///
    /// # Returns
    ///
    /// A sorted vector of variable indices that appear in the BDD
    pub fn support_variables(&self, root: Ref) -> Vec<u32> {
        let mut vars = HashSet::new();
        let mut stack = vec![root];
        let mut visited = HashSet::new();

        while let Some(node_ref) = stack.pop() {
            if visited.contains(&node_ref) || self.is_terminal(node_ref) {
                continue;
            }
            visited.insert(node_ref);

            let node = self.node(node_ref.index());
            vars.insert(node.variable);

            stack.push(node.low);
            stack.push(node.high);
        }

        let mut result: Vec<u32> = vars.into_iter().collect();
        result.sort_unstable();
        result
    }

    /// Get the maximum variable index that appears in the BDD.
    ///
    /// Returns `None` if the BDD is a terminal.
    pub fn max_variable(&self, root: Ref) -> Option<u32> {
        self.support_variables(root).into_iter().max()
    }

    /// Count how many nodes use each variable.
    ///
    /// This information is useful for determining the order in which to
    /// sift variables (larger counts are often sifted first).
    ///
    /// # Arguments
    ///
    /// * `roots` - BDD roots to analyze
    ///
    /// # Returns
    ///
    /// A map from variable index to the number of nodes using that variable
    pub fn variable_usage_counts(&self, roots: &[Ref]) -> HashMap<u32, usize> {
        let mut counts: HashMap<u32, usize> = HashMap::new();
        let mut visited = HashSet::new();
        let mut stack = Vec::new();

        // Add all roots
        for &root in roots {
            if !visited.contains(&root) {
                stack.push(root);
                visited.insert(root);
            }
        }

        while let Some(node_ref) = stack.pop() {
            if self.is_terminal(node_ref) {
                continue;
            }

            let node = self.node(node_ref.index());
            *counts.entry(node.variable).or_insert(0) += 1;

            if !visited.contains(&node.low) {
                stack.push(node.low);
                visited.insert(node.low);
            }

            if !visited.contains(&node.high) {
                stack.push(node.high);
                visited.insert(node.high);
            }
        }

        counts
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_count_nodes_simple() {
        let bdd = Bdd::default();
        let x = bdd.mk_var(1);
        let y = bdd.mk_var(2);

        // x has 2 nodes: one internal node + one terminal
        assert_eq!(bdd.count_nodes(&[x]), 2);

        // y has 2 nodes
        assert_eq!(bdd.count_nodes(&[y]), 2);

        // Both together share the terminal
        assert_eq!(bdd.count_nodes(&[x, y]), 3);
    }

    #[test]
    fn test_count_nodes_and() {
        let bdd = Bdd::default();
        let x = bdd.mk_var(1);
        let y = bdd.mk_var(2);
        let and = bdd.apply_and(x, y);

        // x ∧ y has 3 nodes: x-node, y-node, terminal
        assert_eq!(bdd.count_nodes(&[and]), 3);
    }

    #[test]
    fn test_support_variables() {
        let bdd = Bdd::default();
        let x = bdd.mk_var(1);
        let y = bdd.mk_var(2);
        let z = bdd.mk_var(3);

        assert_eq!(bdd.support_variables(x), vec![1]);
        assert_eq!(bdd.support_variables(y), vec![2]);

        // f = x ∧ y has support {1,2}
        let f = bdd.apply_and(x, y);
        assert_eq!(bdd.support_variables(f), vec![1, 2]);

        // g = x ∧ (y ∨ z) has support {1,2,3}
        let g = bdd.apply_and(x, bdd.apply_or(y, z));
        assert_eq!(bdd.support_variables(g), vec![1, 2, 3]);
    }

    #[test]
    fn test_variable_usage_counts() {
        let bdd = Bdd::default();
        let x = bdd.mk_var(1);
        let y = bdd.mk_var(2);
        let and = bdd.apply_and(x, y);

        let counts = bdd.variable_usage_counts(&[and]);
        assert_eq!(counts.get(&1), Some(&1));
        assert_eq!(counts.get(&2), Some(&1));
    }

    #[test]
    fn test_swap_adjacent_simple() {
        let bdd = Bdd::default();
        let x = bdd.mk_var(1);
        let y = bdd.mk_var(2);
        let f = bdd.apply_and(x, y);

        println!("Original f = {}, size = {}", f, bdd.count_nodes(&[f]));
        println!("x = {}, y = {}", x, y);

        let mut roots = vec![f];
        let size_before = bdd.count_nodes(&roots);

        // Test before swap
        for (assignment, expected) in &[
            (vec![(1, false), (2, false)], false),
            (vec![(1, false), (2, true)], false),
            (vec![(1, true), (2, false)], false),
            (vec![(1, true), (2, true)], true),
        ] {
            let cube: Vec<i32> = assignment
                .iter()
                .map(|&(var, val)| if val { var as i32 } else { -(var as i32) })
                .collect();
            let result = bdd.cofactor_cube(roots[0], &cube);
            let result_bool = bdd.is_one(result);
            println!("Before swap: {:?} -> {}", assignment, result_bool);
            assert_eq!(result_bool, *expected, "Before swap failed for {:?}", assignment);
        }

        // Swap variables 1 and 2
        bdd.swap_adjacent_variables(&mut roots, 0);

        println!("After swap: f = {}, size = {}", roots[0], bdd.count_nodes(&roots));

        let size_after = bdd.count_nodes(&roots);

        // Size should remain the same for x ∧ y
        assert_eq!(size_before, size_after);

        // Function should still be semantically equivalent
        let assignments = [
            (vec![(1, false), (2, false)], false),
            (vec![(1, false), (2, true)], false),
            (vec![(1, true), (2, false)], false),
            (vec![(1, true), (2, true)], true),
        ];

        for (assignment, expected) in assignments {
            let cube: Vec<i32> = assignment
                .iter()
                .map(|&(var, val)| if val { var as i32 } else { -(var as i32) })
                .collect();
            let result = bdd.cofactor_cube(roots[0], &cube);
            let result_bool = bdd.is_one(result);
            println!("After swap: {:?} -> {}", assignment, result_bool);
            assert_eq!(result_bool, expected, "After swap failed for {:?}", assignment);
        }
    }

    #[test]
    fn test_swap_changes_structure() {
        let bdd = Bdd::default();
        let x = bdd.mk_var(1);
        let y = bdd.mk_var(2);
        let z = bdd.mk_var(3);

        // Create (x ∧ y) ∨ (x ∧ z) = x ∧ (y ∨ z)
        let f = bdd.apply_or(bdd.apply_and(x, y), bdd.apply_and(x, z));

        let mut roots = vec![f];
        let size_before = bdd.count_nodes(&roots);

        // Swap y and z
        bdd.swap_adjacent_variables(&mut roots, 1);

        let size_after = bdd.count_nodes(&roots);

        // Size might change due to reordering
        println!("Before: {}, After: {}", size_before, size_after);

        // Verify function is preserved
        let test_cases = [
            (vec![(1, false), (2, false), (3, false)], false),
            (vec![(1, false), (2, false), (3, true)], false),
            (vec![(1, false), (2, true), (3, false)], false),
            (vec![(1, false), (2, true), (3, true)], false),
            (vec![(1, true), (2, false), (3, false)], false),
            (vec![(1, true), (2, false), (3, true)], true),
            (vec![(1, true), (2, true), (3, false)], true),
            (vec![(1, true), (2, true), (3, true)], true),
        ];

        for (assignment, expected) in test_cases {
            let cube: Vec<i32> = assignment
                .iter()
                .map(|&(var, val)| if val { var as i32 } else { -(var as i32) })
                .collect();
            let result = bdd.cofactor_cube(roots[0], &cube);
            let result_bool = bdd.is_one(result);
            assert_eq!(result_bool, expected, "Failed for assignment {:?}", assignment);
        }
    }

    #[test]
    fn test_sift_single_variable() {
        let bdd = Bdd::default();
        let x = bdd.mk_var(1);
        let y = bdd.mk_var(2);
        let z = bdd.mk_var(3);

        // Create a function where ordering matters
        // f = (x ∧ y) ∨ (x ∧ z)
        let f = bdd.apply_or(bdd.apply_and(x, y), bdd.apply_and(x, z));

        let mut roots = vec![f];
        let size_before = bdd.count_nodes(&roots);

        // Sift variable 2 (y)
        let (swaps, reduction) = bdd.sift_variable(&mut roots, 2, 3);

        println!(
            "Sifted variable 2: {} swaps, size: {} -> {} (reduction: {})",
            swaps,
            size_before,
            bdd.count_nodes(&roots),
            reduction
        );

        // Verify function is preserved
        let test_cases = [
            (vec![(1, false), (2, false), (3, false)], false),
            (vec![(1, true), (2, true), (3, false)], true),
            (vec![(1, true), (2, false), (3, true)], true),
            (vec![(1, true), (2, true), (3, true)], true),
        ];

        for (assignment, expected) in test_cases {
            let cube: Vec<i32> = assignment
                .iter()
                .map(|&(var, val)| if val { var as i32 } else { -(var as i32) })
                .collect();
            let result = bdd.cofactor_cube(roots[0], &cube);
            let result_bool = bdd.is_one(result);
            assert_eq!(result_bool, expected, "Failed for assignment {:?}", assignment);
        }
    }

    #[test]
    fn test_sift_all_variables() {
        let bdd = Bdd::default();

        // Create variables
        let x1 = bdd.mk_var(1);
        let x2 = bdd.mk_var(2);
        let x3 = bdd.mk_var(3);
        let x4 = bdd.mk_var(4);

        // Create a function with a suboptimal ordering
        // f = (x1 ∧ x2) ∨ (x3 ∧ x4)
        // With ordering 1,2,3,4 this requires 5 nodes
        // But with ordering 1,3,2,4 it might be smaller
        let f = bdd.apply_or(bdd.apply_and(x1, x2), bdd.apply_and(x3, x4));

        let mut roots = vec![f];
        let size_before = bdd.count_nodes(&roots);

        println!("Before sifting: size = {}", size_before);

        // Perform sifting
        let stats = bdd.sift_all_variables(&mut roots);

        println!("After sifting: size = {}", stats.final_size);
        println!(
            "Reduction: {:.1}%",
            100.0 * (1.0 - (stats.final_size as f64 / stats.initial_size as f64))
        );
        println!("Swaps: {}", stats.swaps);

        // Size should not increase
        assert!(stats.final_size <= stats.initial_size);

        // Verify function is preserved
        let test_cases = [
            (vec![(1, false), (2, false), (3, false), (4, false)], false),
            (vec![(1, true), (2, true), (3, false), (4, false)], true),
            (vec![(1, false), (2, false), (3, true), (4, true)], true),
            (vec![(1, true), (2, true), (3, true), (4, true)], true),
        ];

        for (assignment, expected) in test_cases {
            let cube: Vec<i32> = assignment
                .iter()
                .map(|&(var, val)| if val { var as i32 } else { -(var as i32) })
                .collect();
            let result = bdd.cofactor_cube(roots[0], &cube);
            let result_bool = bdd.is_one(result);
            assert_eq!(result_bool, expected, "Failed for assignment {:?}", assignment);
        }
    }

    #[test]
    fn test_reorder_stats() {
        let stats = ReorderStats {
            swaps: 10,
            initial_size: 100,
            final_size: 80,
            best_size: 75,
            variables_processed: 5,
        };

        assert!((stats.reduction_ratio() - 0.2).abs() < 1e-10);
        assert!((stats.reduction_percent() - 20.0).abs() < 1e-8);
    }
}
