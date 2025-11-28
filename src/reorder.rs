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
use crate::types::{Level, NodeId, Var};

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
    /// Swap two variables in a BDD using Shannon expansion.
    ///
    /// This function swaps variables `var_x` and `var_y` in the BDD `f`, returning a new BDD
    /// where the roles of these variables are exchanged.
    /// Unlike [`swap_adjacent_inplace`](Self::swap_adjacent_inplace), this works for any pair
    /// of variables (not just adjacent ones) and operates on a single BDD
    /// rather than modifying the global variable ordering.
    ///
    /// # Algorithm
    ///
    /// Uses Shannon expansion to compute the four cofactors and rebuild:
    /// ```text
    /// f' = ITE(y, ITE(x, f[x←1,y←1], f[x←0,y←1]), ITE(x, f[x←1,y←0], f[x←0,y←0]))
    /// ```
    ///
    /// # Complexity
    ///
    /// O(n²) where n = number of nodes, due to cofactor computations.
    /// For adjacent variables, prefer [`swap_adjacent_inplace`](Self::swap_adjacent_inplace)
    /// which is O(k), where k = nodes at the two levels.
    ///
    /// # Arguments
    ///
    /// * `f` - The BDD to transform
    /// * `var_x` - First variable to swap
    /// * `var_y` - Second variable to swap
    ///
    /// # Returns
    ///
    /// A new BDD with variables `var_x` and `var_y` swapped
    ///
    /// # Examples
    ///
    /// ```
    /// use bdd_rs::bdd::Bdd;
    /// use bdd_rs::types::Var;
    ///
    /// let bdd = Bdd::default();
    /// let x = bdd.mk_var(1);
    /// let y = bdd.mk_var(2);
    ///
    /// // f = x ∧ y
    /// let f = bdd.apply_and(x, y);
    ///
    /// // Swap x and y - result is still equivalent to x ∧ y
    /// let swapped = bdd.swap_variables_shannon(f, Var::new(1), Var::new(2));
    ///
    /// // The function is semantically unchanged (conjunction is commutative)
    /// assert_eq!(bdd.apply_xor(f, swapped), bdd.zero);
    /// ```
    pub fn swap_variables_shannon(&self, f: Ref, var_x: Var, var_y: Var) -> Ref {
        if var_x == var_y {
            return f;
        }

        // Get the four cofactors
        let f00 = self.cofactor_cube(f, [var_x.neg(), var_y.neg()]);
        let f01 = self.cofactor_cube(f, [var_x.neg(), var_y.pos()]);
        let f10 = self.cofactor_cube(f, [var_x.pos(), var_y.neg()]);
        let f11 = self.cofactor_cube(f, [var_x.pos(), var_y.pos()]);

        // Build the swapped BDD: swap the roles of x and y
        // Original: when x=a, y=b, we get f[x←a, y←b]
        // Swapped:  when x=a, y=b, we want f[x←b, y←a]
        let x_var = self.mk_var(var_x);
        let y_var = self.mk_var(var_y);

        // When y=0: we want values where original y=0, so use f_0 (from x perspective)
        // When y=1: we want values where original y=1, so use f_1
        // But we're swapping, so:
        // - f'(x=0,y=0) = f(x=0,y=0) = f00
        // - f'(x=0,y=1) = f(x=1,y=0) = f10  (swap: x gets y's value, y gets x's value)
        // - f'(x=1,y=0) = f(x=0,y=1) = f01
        // - f'(x=1,y=1) = f(x=1,y=1) = f11
        let when_y0 = self.apply_ite(x_var, f01, f00); // x=1->f01, x=0->f00
        let when_y1 = self.apply_ite(x_var, f11, f10); // x=1->f11, x=0->f10

        self.apply_ite(y_var, when_y1, when_y0)
    }

    /// Perform Rudell's sifting algorithm on all variables.
    ///
    /// This is the main entry point for dynamic variable reordering. It iterates
    /// through all variables (in decreasing order of usage count) and sifts each
    /// one to find its locally optimal position. This process can significantly
    /// reduce BDD size for many functions.
    ///
    /// Internally uses [`swap_adjacent_inplace`](Self::swap_adjacent_inplace) for efficient
    /// O(k) adjacent variable swaps, where k = number of nodes at the two levels.
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
    ///
    /// # Examples
    ///
    /// ```
    /// use bdd_rs::bdd::Bdd;
    ///
    /// let bdd = Bdd::default();
    /// let x1 = bdd.mk_var(1);
    /// let x2 = bdd.mk_var(2);
    /// let x3 = bdd.mk_var(3);
    /// let x4 = bdd.mk_var(4);
    /// let f = bdd.apply_or(bdd.apply_and(x1, x2), bdd.apply_and(x3, x4));
    ///
    /// let mut roots = vec![f];
    /// let stats = bdd.sift_all_variables(&mut roots);
    /// println!("Reduced by {:.1}%", stats.reduction_percent());
    /// ```
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

        // Get usage counts to determine sifting order
        let usage_counts = self.variable_usage_counts(roots);

        // Sort variables by usage count (descending), with variable ID as tiebreaker
        let mut vars_to_sift: Vec<Var> = all_vars.into_iter().collect();
        vars_to_sift.sort_by(|a, b| {
            let count_a = usage_counts.get(a).copied().unwrap_or(0);
            let count_b = usage_counts.get(b).copied().unwrap_or(0);
            count_b
                .cmp(&count_a) // Descending by count
                .then_with(|| a.id().cmp(&b.id())) // Ascending by variable ID for determinism
        });

        debug!("Sifting {} variables in order: {:?}", vars_to_sift.len(), vars_to_sift);

        let mut total_swaps = 0;
        let mut best_size = initial_size;

        // Sift each variable
        for &var in &vars_to_sift {
            debug!("Sifting variable {}", var);
            let (swaps, _reduction) = self.sift_variable(roots, var);
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

    /// Sift a single variable to find its optimal position.
    ///
    /// This is the core operation of Rudell's sifting algorithm. The variable
    /// is moved through all possible positions (from top to bottom), and the
    /// BDD size is measured at each position. Finally, the variable is placed
    /// at the position that minimized the BDD size.
    ///
    /// Uses [`swap_adjacent_inplace`](Self::swap_adjacent_inplace) for efficient O(k) swaps.
    /// For reordering all variables, use [`sift_all_variables`](Self::sift_all_variables).
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
    /// * `var` - The variable to sift (1-indexed variable ID)
    ///
    /// # Returns
    ///
    /// The number of swaps performed and the size reduction achieved
    pub fn sift_variable(&self, roots: &mut [Ref], var: Var) -> (usize, i64) {
        let Some(mut current_level) = self.get_level(var) else {
            debug!("Variable {} not in ordering, skipping sift", var);
            return (0, 0);
        };

        let num_levels = self.num_levels();
        if num_levels <= 1 {
            return (0, 0);
        }

        let initial_size = self.count_nodes(roots) as i64;
        let mut swaps = 0;

        // Record sizes at each level
        let mut sizes: Vec<(usize, usize)> = Vec::new();
        sizes.push((current_level.index(), initial_size as usize));

        debug!("Sifting variable {} (initially at level {})", var, current_level);

        // Move variable up to level 0
        while current_level.index() > 0 {
            let prev = current_level.prev().expect("Should have previous level");
            let mapping = self.swap_adjacent_inplace(prev).expect("swap should succeed");
            self.remap_roots(roots, &mapping);
            current_level = prev;
            swaps += 1;

            let size = self.count_nodes(roots);
            sizes.push((current_level.index(), size));
            debug!("  After swap to level {}: size = {}", current_level, size);
        }

        // Now move it down through all positions
        while current_level.index() < num_levels - 1 {
            let mapping = self.swap_adjacent_inplace(current_level).expect("swap should succeed");
            self.remap_roots(roots, &mapping);
            current_level = current_level.next();
            swaps += 1;

            let size = self.count_nodes(roots);
            sizes.push((current_level.index(), size));
            debug!("  After swap to level {}: size = {}", current_level, size);
        }

        // Find the level with minimum size
        let (best_level, best_size) = sizes.iter().min_by_key(|(_, size)| size).copied().unwrap();
        debug!("  Best position: level {} with size {}", best_level, best_size);

        // Move variable back to the best position
        while current_level.index() > best_level {
            let prev = current_level.prev().expect("Should have previous level");
            let mapping = self.swap_adjacent_inplace(prev).expect("swap should succeed");
            self.remap_roots(roots, &mapping);
            current_level = prev;
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

    /// Applies a node index → Ref mapping to a single reference.
    ///
    /// If the reference's index is in the mapping, returns the mapped value
    /// (preserving negation). Otherwise returns the reference unchanged.
    ///
    /// This is a public wrapper around the internal `apply_mapping` used during swaps.
    pub fn remap_ref(&self, r: Ref, mapping: &HashMap<NodeId, Ref>) -> Ref {
        self.apply_mapping(r, mapping)
    }

    /// Applies a node index → Ref mapping to a slice of roots, mutating them in place.
    ///
    /// For each root, if its index is in the mapping, the root is updated to the
    /// mapped value (preserving negation).
    ///
    /// # Arguments
    ///
    /// * `roots` - Mutable slice of BDD roots to update
    /// * `mapping` - Mapping from old node indices to new references
    ///
    /// # Example
    ///
    /// ```
    /// use bdd_rs::bdd::Bdd;
    /// use bdd_rs::types::Level;
    ///
    /// let bdd = Bdd::default();
    /// let x = bdd.mk_var(1);
    /// let y = bdd.mk_var(2);
    /// let f = bdd.apply_and(x, y);
    ///
    /// let mut roots = vec![f];
    /// let mapping = bdd.swap_adjacent_inplace(Level::new(0)).unwrap();
    /// bdd.remap_roots(&mut roots, &mapping);
    /// // roots[0] now points to the updated BDD
    /// ```
    pub fn remap_roots(&self, roots: &mut [Ref], mapping: &HashMap<NodeId, Ref>) {
        for root in roots.iter_mut() {
            *root = self.apply_mapping(*root, mapping);
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
        visited.insert(self.one.id());

        for &root in roots {
            let mut stack = vec![root.id()];

            while let Some(idx) = stack.pop() {
                if visited.insert(idx) {
                    let node_ref = Ref::positive(idx);
                    if self.is_terminal(node_ref) {
                        continue;
                    }
                    let low = self.low_node(node_ref);
                    let high = self.high_node(node_ref);
                    if !self.is_terminal(low) {
                        stack.push(low.id());
                    }
                    if !self.is_terminal(high) {
                        stack.push(high.id());
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
    /// A vector of variables that appear in the BDD, sorted by their level in the ordering
    pub fn support_variables(&self, root: Ref) -> Vec<Var> {
        let mut vars = HashSet::new();
        let mut stack = vec![root];
        let mut visited = HashSet::new();

        while let Some(node_ref) = stack.pop() {
            if visited.contains(&node_ref) || self.is_terminal(node_ref) {
                continue;
            }
            visited.insert(node_ref);

            let node = self.node(node_ref.id());
            vars.insert(node.variable);

            stack.push(node.low);
            stack.push(node.high);
        }

        let mut result: Vec<Var> = vars.into_iter().collect();
        // Sort by level in the ordering (not by variable ID)
        result.sort_unstable_by_key(|v| self.get_level(*v).map(|l| l.index()).unwrap_or(usize::MAX));
        result
    }

    /// Get the maximum variable (by level) that appears in the BDD.
    ///
    /// Returns `None` if the BDD is a terminal.
    ///
    /// Note: "maximum" refers to the variable closest to the terminals (highest level).
    pub fn max_variable(&self, root: Ref) -> Option<Var> {
        self.support_variables(root)
            .into_iter()
            // .max_by_key(|v| self.get_level(*v).unwrap())
            .max_by_key(|v| self.get_level(*v).map(|l| l.index()).unwrap_or(0))
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
    /// A map from variable to the number of nodes using that variable
    pub fn variable_usage_counts(&self, roots: &[Ref]) -> HashMap<Var, usize> {
        let mut counts: HashMap<Var, usize> = HashMap::new();
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

            let node = self.node(node_ref.id());
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

    /// Move a variable to a target level using adjacent swaps.
    ///
    /// This moves the variable currently at `from_level` to `to_level` by performing
    /// a sequence of adjacent swaps. All intermediate variables are shifted accordingly.
    ///
    /// # Arguments
    ///
    /// * `roots` - BDD roots to update after the move
    /// * `var` - The variable to move
    /// * `target_level` - The target level for the variable
    ///
    /// # Returns
    ///
    /// The number of swaps performed
    ///
    /// # Examples
    ///
    /// ```
    /// use bdd_rs::bdd::Bdd;
    /// use bdd_rs::types::{Var, Level};
    ///
    /// let bdd = Bdd::default();
    /// let x1 = bdd.mk_var(1);
    /// let x2 = bdd.mk_var(2);
    /// let x3 = bdd.mk_var(3);
    /// let f = bdd.apply_and(x1, bdd.apply_or(x2, x3));
    ///
    /// let mut roots = vec![f];
    ///
    /// // Move variable 1 from level 0 to level 2
    /// let swaps = bdd.move_variable_to_level(&mut roots, Var::new(1), Level::new(2));
    /// assert_eq!(swaps, 2);  // Two adjacent swaps needed
    /// ```
    pub fn move_variable_to_level(&self, roots: &mut [Ref], var: Var, target_level: Level) -> usize {
        let Some(mut current_level) = self.get_level(var) else {
            debug!("Variable {} not in ordering, cannot move", var);
            return 0;
        };

        if current_level == target_level {
            return 0;
        }

        let mut swaps = 0;

        if current_level < target_level {
            // Move down (towards terminals)
            while current_level < target_level {
                let mapping = self.swap_adjacent_inplace(current_level).expect("swap should succeed");
                self.remap_roots(roots, &mapping);
                current_level = current_level.next();
                swaps += 1;
            }
        } else {
            // Move up (towards root)
            while current_level > target_level {
                let prev = current_level.prev().expect("Should have previous level");
                let mapping = self.swap_adjacent_inplace(prev).expect("swap should succeed");
                self.remap_roots(roots, &mapping);
                current_level = prev;
                swaps += 1;
            }
        }

        swaps
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::types::Level;

    /// Helper to verify a BDD function is preserved after transformation.
    fn verify_function(bdd: &Bdd, root: Ref, vars: &[u32], expected_fn: impl Fn(&[bool]) -> bool) {
        let var_objs: Vec<Var> = vars.iter().map(|&v| Var::new(v)).collect();
        let failures = bdd.verify_truth_table(root, &var_objs, expected_fn);
        if !failures.is_empty() {
            println!("Truth table failures:");
            for (assignment, expected, actual) in &failures {
                let named: Vec<_> = vars.iter().zip(assignment).map(|(v, b)| format!("x{}={}", v, b)).collect();
                println!("  {} => expected {}, got {}", named.join(", "), expected, actual);
            }
            println!("\nBDD structure:");
            println!("{}", bdd.debug_string(root));
            println!("{}", bdd.debug_ordering());
            panic!("Function verification failed with {} errors", failures.len());
        }
    }

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

        assert_eq!(bdd.support_variables(x), vec![Var::new(1)]);
        assert_eq!(bdd.support_variables(y), vec![Var::new(2)]);

        // f = x ∧ y has support {1,2}
        let f = bdd.apply_and(x, y);
        assert_eq!(bdd.support_variables(f), vec![Var::new(1), Var::new(2)]);

        // g = x ∧ (y ∨ z) has support {1,2,3}
        let g = bdd.apply_and(x, bdd.apply_or(y, z));
        assert_eq!(bdd.support_variables(g), vec![Var::new(1), Var::new(2), Var::new(3)]);
    }

    #[test]
    fn test_variable_usage_counts() {
        let bdd = Bdd::default();
        let x = bdd.mk_var(1);
        let y = bdd.mk_var(2);
        let and = bdd.apply_and(x, y);

        let counts = bdd.variable_usage_counts(&[and]);
        assert_eq!(counts.get(&Var::new(1)), Some(&1));
        assert_eq!(counts.get(&Var::new(2)), Some(&1));
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

        // Debug: print original BDD structure
        println!("Original BDD structure:");
        if !bdd.is_terminal(roots[0]) {
            let node = bdd.node(roots[0].id());
            println!(
                "  Root @{}: var={}, low={}, high={}",
                roots[0].id(),
                node.variable,
                bdd.low_node(roots[0]),
                bdd.high_node(roots[0])
            );

            if !bdd.is_terminal(bdd.low_node(roots[0])) {
                let low_ref = bdd.low_node(roots[0]);
                let low_node = bdd.node(low_ref.id());
                println!(
                    "    Low child @{}: var={}, low={}, high={}",
                    low_ref.id(),
                    low_node.variable,
                    bdd.low_node(low_ref),
                    bdd.high_node(low_ref)
                );
            }

            if !bdd.is_terminal(bdd.high_node(roots[0])) {
                let high_ref = bdd.high_node(roots[0]);
                let high_node = bdd.node(high_ref.id());
                println!(
                    "    High child @{}: var={}, low={}, high={}",
                    high_ref.id(),
                    high_node.variable,
                    bdd.low_node(high_ref),
                    bdd.high_node(high_ref)
                );
            }
        }

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
            let result = bdd.cofactor_cube(roots[0], cube.iter().copied());
            let result_bool = bdd.is_one(result);
            println!("Before swap: {:?} -> {}", assignment, result_bool);
            assert_eq!(result_bool, *expected, "Before swap failed for {:?}", assignment);
        }

        println!("Before swap: {:?}", bdd);

        // Swap variables 1 and 2
        let mapping = bdd.swap_adjacent_inplace(Level::new(0)).unwrap();
        bdd.remap_roots(&mut roots, &mapping);

        println!("After swap: {:?}", bdd);
        println!("After swap: f = {}, size = {}", roots[0], bdd.count_nodes(&roots));

        // Debug: print BDD structure
        println!("BDD structure after swap:");
        if !bdd.is_terminal(roots[0]) {
            let node = bdd.node(roots[0].id());
            println!(
                "  Root: var={}, low={}, high={}",
                node.variable,
                bdd.low_node(roots[0]),
                bdd.high_node(roots[0])
            );

            if !bdd.is_terminal(bdd.low_node(roots[0])) {
                let low_node = bdd.node(bdd.low_node(roots[0]).id());
                println!(
                    "    Low child: var={}, low={}, high={}",
                    low_node.variable,
                    bdd.low_node(bdd.low_node(roots[0])),
                    bdd.high_node(bdd.low_node(roots[0]))
                );
            }

            if !bdd.is_terminal(bdd.high_node(roots[0])) {
                let high_node = bdd.node(bdd.high_node(roots[0]).id());
                println!(
                    "    High child: var={}, low={}, high={}",
                    high_node.variable,
                    bdd.low_node(bdd.high_node(roots[0])),
                    bdd.high_node(bdd.high_node(roots[0]))
                );
            }
        }

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
            let result = bdd.cofactor_cube(roots[0], cube.iter().copied());
            let result_bool = bdd.is_one(result);
            println!(
                "After swap: {:?} -> {} (result ref: {}, is_one: {}, is_zero: {})",
                assignment,
                result_bool,
                result,
                bdd.is_one(result),
                bdd.is_zero(result)
            );
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
        let mapping = bdd.swap_adjacent_inplace(Level::new(1)).unwrap();
        bdd.remap_roots(&mut roots, &mapping);

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
            let result = bdd.cofactor_cube(roots[0], cube.iter().copied());
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

        // Expected truth table for f = (x ∧ y) ∨ (x ∧ z)
        let expected_fn = |assignment: &[bool]| -> bool {
            let x = assignment[0];
            let y = assignment[1];
            let z = assignment[2];
            (x && y) || (x && z)
        };

        // Verify before sift
        verify_function(&bdd, roots[0], &[1, 2, 3], expected_fn);

        // Sift variable 2 (y)
        let (swaps, reduction) = bdd.sift_variable(&mut roots, Var::new(2));

        println!(
            "Sifted variable 2: {} swaps, size: {} -> {} (reduction: {})",
            swaps,
            size_before,
            bdd.count_nodes(&roots),
            reduction
        );

        // Verify after sift
        verify_function(&bdd, roots[0], &[1, 2, 3], expected_fn);
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
            let result = bdd.cofactor_cube(roots[0], cube.iter().copied());
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

    #[test]
    fn test_swap_variables_shannon_commutative() {
        // For commutative functions like AND, swapping variables preserves equivalence
        let bdd = Bdd::default();
        let x = bdd.mk_var(1);
        let y = bdd.mk_var(2);

        let f = bdd.apply_and(x, y);
        let swapped = bdd.swap_variables_shannon(f, Var::new(1), Var::new(2));

        // x ∧ y with swapped variables should still equal x ∧ y
        let diff = bdd.apply_xor(f, swapped);
        assert!(bdd.is_zero(diff), "Commutative function should be unchanged by swap");
    }

    #[test]
    fn test_swap_variables_shannon_implication() {
        // For non-commutative functions like implication, swapping changes the result
        let bdd = Bdd::default();
        let x = bdd.mk_var(1);
        let y = bdd.mk_var(2);

        // f = x → y = ¬x ∨ y
        let f = bdd.apply_or(-x, y);

        // After swapping x and y, we should get y → x = ¬y ∨ x
        let swapped = bdd.swap_variables_shannon(f, Var::new(1), Var::new(2));
        let expected = bdd.apply_or(-y, x);

        let diff = bdd.apply_xor(swapped, expected);
        assert!(bdd.is_zero(diff), "Swapped implication should equal reversed implication");
    }

    #[test]
    fn test_swap_variables_shannon_three_vars() {
        let bdd = Bdd::default();
        let x = bdd.mk_var(1);
        let y = bdd.mk_var(2);
        let z = bdd.mk_var(3);

        // f = (x ∧ y) ∨ z
        let f = bdd.apply_or(bdd.apply_and(x, y), z);

        // Swap x and z: result should be (z ∧ y) ∨ x
        let swapped = bdd.swap_variables_shannon(f, Var::new(1), Var::new(3));
        let expected = bdd.apply_or(bdd.apply_and(z, y), x);

        let diff = bdd.apply_xor(swapped, expected);
        assert!(bdd.is_zero(diff), "Three-variable swap failed");
    }

    #[test]
    fn test_swap_variables_shannon_self_swap() {
        let bdd = Bdd::default();
        let x = bdd.mk_var(1);
        let y = bdd.mk_var(2);
        let f = bdd.apply_and(x, y);

        // Swapping a variable with itself should return the same BDD
        let swapped = bdd.swap_variables_shannon(f, Var::new(1), Var::new(1));
        assert_eq!(f, swapped, "Self-swap should return identical BDD");
    }

    #[test]
    fn test_swap_variables_shannon_truth_table() {
        // Verify swap by checking all input combinations
        let bdd = Bdd::default();
        let x = bdd.mk_var(1);
        let y = bdd.mk_var(2);

        // f(x,y) = x ∧ ¬y (x AND NOT y)
        let f = bdd.apply_and(x, -y);
        let swapped = bdd.swap_variables_shannon(f, Var::new(1), Var::new(2));

        // After swapping, f'(x,y) should equal f(y,x) = y ∧ ¬x
        let test_cases = [
            // (x, y, expected_swapped = y ∧ ¬x)
            (false, false, false), // f'(0,0) = f(0,0) = 0 ∧ ¬0 = false
            (false, true, true),   // f'(0,1) = f(1,0) = 1 ∧ ¬0 = true
            (true, false, false),  // f'(1,0) = f(0,1) = 0 ∧ ¬1 = false
            (true, true, false),   // f'(1,1) = f(1,1) = 1 ∧ ¬1 = false
        ];

        for (x_val, y_val, expected) in test_cases {
            let cube: Vec<i32> = vec![if x_val { 1 } else { -1 }, if y_val { 2 } else { -2 }];
            let result = bdd.cofactor_cube(swapped, cube.iter().copied());
            let result_bool = bdd.is_one(result);
            assert_eq!(
                result_bool, expected,
                "Swap truth table failed for x={}, y={}: got {}, expected {}",
                x_val, y_val, result_bool, expected
            );
        }
    }

    #[test]
    fn test_move_variable_to_level_down() {
        let bdd = Bdd::default();
        let x1 = bdd.mk_var(1);
        let x2 = bdd.mk_var(2);
        let x3 = bdd.mk_var(3);
        let f = bdd.apply_and(x1, bdd.apply_or(x2, x3));

        let mut roots = vec![f];

        // Variable 1 is at level 0, move it to level 2
        assert_eq!(bdd.get_level(Var::new(1)), Some(Level::new(0)));

        let swaps = bdd.move_variable_to_level(&mut roots, Var::new(1), Level::new(2));
        assert_eq!(swaps, 2, "Should need 2 swaps to move from level 0 to 2");

        // Check that variable 1 is now at level 2
        assert_eq!(bdd.get_level(Var::new(1)), Some(Level::new(2)));

        // Verify function is preserved
        let test_cases = [
            (vec![(1, true), (2, false), (3, false)], false),
            (vec![(1, true), (2, true), (3, false)], true),
            (vec![(1, true), (2, false), (3, true)], true),
            (vec![(1, false), (2, true), (3, true)], false),
        ];

        for (assignment, expected) in test_cases {
            let cube: Vec<i32> = assignment
                .iter()
                .map(|&(var, val)| if val { var as i32 } else { -(var as i32) })
                .collect();
            let result = bdd.cofactor_cube(roots[0], cube.iter().copied());
            assert_eq!(bdd.is_one(result), expected, "Failed for {:?}", assignment);
        }
    }

    #[test]
    fn test_move_variable_to_level_up() {
        let bdd = Bdd::default();
        let x1 = bdd.mk_var(1);
        let x2 = bdd.mk_var(2);
        let x3 = bdd.mk_var(3);

        // f = x1 AND (x2 OR x3)
        let f = bdd.apply_and(x1, bdd.apply_or(x2, x3));
        let mut roots = vec![f];

        // Expected truth table for x1 AND (x2 OR x3)
        let expected_fn = |assignment: &[bool]| -> bool {
            let x1 = assignment[0];
            let x2 = assignment[1];
            let x3 = assignment[2];
            x1 && (x2 || x3)
        };

        println!("=== Before move ===");
        println!("{}", bdd.debug_string(roots[0]));
        println!("{}", bdd.debug_ordering());
        println!("{}", bdd.dump_state());

        // Verify before move
        verify_function(&bdd, roots[0], &[1, 2, 3], expected_fn);

        // Variable 3 is at level 2, move it to level 0
        // This should do: swap(L1, L2) then swap(L0, L1)
        assert_eq!(bdd.get_level(Var::new(3)), Some(Level::new(2)));

        println!("\n=== Step 1: swap levels 1 and 2 ===");
        let mapping = bdd.swap_adjacent_inplace(Level::new(1)).unwrap();
        bdd.remap_roots(&mut roots, &mapping);
        println!("{}", bdd.debug_string(roots[0]));
        println!("{}", bdd.debug_ordering());
        println!("{}", bdd.dump_state());
        verify_function(&bdd, roots[0], &[1, 2, 3], expected_fn);
        println!("\n=== Step 2: swap levels 0 and 1 ===");
        let mapping = bdd.swap_adjacent_inplace(Level::new(0)).unwrap();
        bdd.remap_roots(&mut roots, &mapping);
        println!("{}", bdd.debug_string(roots[0]));
        println!("{}", bdd.debug_ordering());
        println!("{}", bdd.dump_state());

        // Check that variable 3 is now at level 0
        assert_eq!(bdd.get_level(Var::new(3)), Some(Level::new(0)));

        // Verify after move
        verify_function(&bdd, roots[0], &[1, 2, 3], expected_fn);
    }

    #[test]
    fn test_move_variable_to_level_no_op() {
        let bdd = Bdd::default();
        let x = bdd.mk_var(1);
        let y = bdd.mk_var(2);
        let f = bdd.apply_and(x, y);

        let mut roots = vec![f];

        // Moving to current level should be a no-op
        let swaps = bdd.move_variable_to_level(&mut roots, Var::new(1), Level::new(0));
        assert_eq!(swaps, 0, "Moving to current level should require 0 swaps");
    }

    #[test]
    fn test_move_variable_non_adjacent_swap() {
        // Test moving a variable across multiple positions (the old swap_any_variables use case)
        let bdd = Bdd::default();
        let x1 = bdd.mk_var(1);
        let x2 = bdd.mk_var(2);
        let x3 = bdd.mk_var(3);
        let x4 = bdd.mk_var(4);

        // Create (x1 ∧ x3) ∨ (x2 ∧ x4)
        let f = bdd.apply_or(bdd.apply_and(x1, x3), bdd.apply_and(x2, x4));
        let mut roots = vec![f];

        println!(
            "Before move: ordering = {:?}",
            (1..=4).map(|i| bdd.get_level(Var::new(i))).collect::<Vec<_>>()
        );

        // Move x1 (level 0) to level 2 (where x3 was)
        let swaps = bdd.move_variable_to_level(&mut roots, Var::new(1), Level::new(2));
        assert_eq!(swaps, 2);

        println!(
            "After move: ordering = {:?}",
            (1..=4).map(|i| bdd.get_level(Var::new(i))).collect::<Vec<_>>()
        );

        // Verify function is preserved
        let test_cases = [
            (vec![(1, true), (2, false), (3, true), (4, false)], true), // x1∧x3
            (vec![(1, false), (2, true), (3, false), (4, true)], true), // x2∧x4
            (vec![(1, true), (2, false), (3, false), (4, true)], false),
            (vec![(1, false), (2, false), (3, false), (4, false)], false),
            (vec![(1, true), (2, true), (3, true), (4, true)], true),
        ];

        for (assignment, expected) in test_cases {
            let cube: Vec<i32> = assignment
                .iter()
                .map(|&(var, val)| if val { var as i32 } else { -(var as i32) })
                .collect();
            let result = bdd.cofactor_cube(roots[0], cube.iter().copied());
            assert_eq!(bdd.is_one(result), expected, "Failed for {:?}", assignment);
        }
    }
}
