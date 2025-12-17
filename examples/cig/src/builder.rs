//! CIG builder: constructs CIG from Boolean functions.
//!
//! The builder analyzes the separability structure of a Boolean function
//! and constructs the canonical interaction graph.

use std::sync::Arc;

use crate::cig::{Cig, CigNode, UniqueTable};
use crate::interaction::InteractionFunction;
use crate::partition::Partition;
use crate::separability::{find_interaction_partition, Operator};
use crate::truth_table::TruthTable;
use crate::variable::{Var, VarSet};

/// Builder for constructing CIGs from Boolean functions.
pub struct CigBuilder {
    /// Unique table for hash-consing nodes.
    unique_table: UniqueTable,
}

impl Default for CigBuilder {
    fn default() -> Self {
        Self::new()
    }
}

impl CigBuilder {
    /// Create a new CIG builder.
    pub fn new() -> Self {
        CigBuilder {
            unique_table: UniqueTable::new(),
        }
    }

    /// Build a CIG from a truth table.
    pub fn build(&mut self, f: &TruthTable) -> Cig {
        let root = self.build_recursive(f);
        Cig::new(root)
    }

    /// Build a CIG node recursively.
    fn build_recursive(&mut self, f: &TruthTable) -> Arc<CigNode> {
        // Handle constant functions
        if f.is_zero() {
            return self.unique_table.zero();
        }
        if f.is_one() {
            return self.unique_table.one();
        }

        // Get essential variables
        let vars = f.essential_vars();

        // Single variable: return leaf
        if vars.len() == 1 {
            let var = vars.iter().next().unwrap();
            // Check if it's the variable or its negation
            // We need to evaluate at an assignment where var=true
            let mut assignment = vec![false; f.num_vars() as usize];
            assignment[var.position()] = true;
            if f.eval(&assignment) {
                return self.unique_table.leaf(var);
            } else {
                // Negated variable: represented as internal node with negation
                let leaf = self.unique_table.leaf(var);
                let neg_interaction = InteractionFunction::from_expr(1, |x| !x[0]);
                return self.unique_table.internal(neg_interaction, vec![leaf]);
            }
        }

        // Find the interaction partition
        let partition = find_interaction_partition(f);

        if partition.num_blocks() == 1 {
            // Fully irreducible: all variables interact
            return self.build_irreducible(f, &vars);
        }

        // Separable: build children for each block and combine
        self.build_separable(f, &partition)
    }

    /// Build a node for an irreducible function.
    fn build_irreducible(&mut self, f: &TruthTable, vars: &VarSet) -> Arc<CigNode> {
        // For an irreducible function, we create an internal node
        // with children being the variables, and the interaction
        // function being the function itself.

        let var_list: Vec<Var> = vars.iter().collect();
        let children: Vec<Arc<CigNode>> = var_list
            .iter()
            .map(|&v| self.unique_table.leaf(v))
            .collect();

        // The interaction function is f itself (reindexed)
        let n = var_list.len() as u32;
        let interaction = InteractionFunction::from_expr(n, |x| {
            // Map x to full assignment
            let mut full = vec![false; f.num_vars() as usize];
            for (i, &var) in var_list.iter().enumerate() {
                full[var.position()] = x[i];
            }
            f.eval(&full)
        });

        // Sort children by variable index for canonicity
        let mut indexed_children: Vec<_> = children
            .into_iter()
            .enumerate()
            .map(|(i, c)| (var_list[i], c))
            .collect();
        indexed_children.sort_by_key(|(v, _)| v.index());

        let sorted_children: Vec<_> = indexed_children.into_iter().map(|(_, c)| c).collect();

        self.unique_table.internal(interaction, sorted_children)
    }

    /// Build a node for a separable function.
    fn build_separable(&mut self, f: &TruthTable, partition: &Partition) -> Arc<CigNode> {
        let blocks = partition.blocks();

        if blocks.len() == 2 {
            // Binary separation: find the operator and subfunctions
            return self.build_binary_separable(f, &blocks[0], &blocks[1]);
        }

        // Multi-way separation: recursively combine pairs
        // For now, we do a simple left-to-right combination
        self.build_multiway_separable(f, blocks)
    }

    /// Build a binary separable node.
    fn build_binary_separable(
        &mut self,
        f: &TruthTable,
        a_vars: &VarSet,
        b_vars: &VarSet,
    ) -> Arc<CigNode> {
        // Find the separating operator
        let result = test_separability_on_function(f, a_vars, b_vars);

        if !result.is_separable {
            // Shouldn't happen if partition is correct
            panic!("Expected separable function");
        }

        let op = result.operator.unwrap();
        let g = result.g.unwrap();
        let h = result.h.unwrap();

        // Recursively build children
        let child_a = self.build_from_subfunction(&g, a_vars);
        let child_b = self.build_from_subfunction(&h, b_vars);

        // Create interaction function
        let interaction = InteractionFunction::from_operator(op);

        // Order children canonically by hash
        let (c1, c2) = if child_a.canonical_hash() <= child_b.canonical_hash() {
            (child_a, child_b)
        } else {
            (child_b, child_a)
        };

        self.unique_table.internal(interaction, vec![c1, c2])
    }

    /// Build from a subfunction on a specific variable set.
    fn build_from_subfunction(&mut self, g: &TruthTable, vars: &VarSet) -> Arc<CigNode> {
        // g is already a function on |vars| variables
        // We need to map it back to the original variable indices

        // Handle trivial cases
        if g.is_zero() {
            return self.unique_table.zero();
        }
        if g.is_one() {
            return self.unique_table.one();
        }

        let var_list: Vec<Var> = vars.iter().collect();

        // Check if it's just a single variable
        if var_list.len() == 1 {
            let var = var_list[0];
            // g is on 1 variable: either identity or negation
            if g.eval(&[false]) != g.eval(&[true]) {
                if g.eval(&[true]) {
                    return self.unique_table.leaf(var);
                } else {
                    // Negation
                    let leaf = self.unique_table.leaf(var);
                    let neg = InteractionFunction::from_expr(1, |x| !x[0]);
                    return self.unique_table.internal(neg, vec![leaf]);
                }
            }
        }

        // Create a truth table that maps to original variable positions
        let n = var_list.iter().map(|v| v.index()).max().unwrap();
        let f_remapped = TruthTable::from_expr(n, |x| {
            // Extract values for our variables
            let sub_vals: Vec<bool> = var_list.iter().map(|v| x[v.position()]).collect();
            g.eval(&sub_vals)
        });

        self.build_recursive(&f_remapped)
    }

    /// Build a multi-way separable node.
    fn build_multiway_separable(&mut self, f: &TruthTable, blocks: &[VarSet]) -> Arc<CigNode> {
        if blocks.len() == 1 {
            return self.build_irreducible(f, &blocks[0]);
        }

        // Split into first block vs rest
        let first = &blocks[0];
        let rest_vars: VarSet = blocks[1..].iter().fold(VarSet::empty(), |acc, b| acc.union(b));

        self.build_binary_separable(f, first, &rest_vars)
    }

    /// Get statistics about the builder.
    pub fn stats(&self) -> crate::cig::UniqueTableStats {
        self.unique_table.stats()
    }
}

/// Helper to test separability for CIG construction.
fn test_separability_on_function(
    f: &TruthTable,
    a_vars: &VarSet,
    b_vars: &VarSet,
) -> SeparabilityResult {
    let a_list: Vec<Var> = a_vars.iter().collect();
    let b_list: Vec<Var> = b_vars.iter().collect();

    let a_size = 1usize << a_list.len();
    let b_size = 1usize << b_list.len();

    let n = f.num_vars() as usize;

    // Build characteristic matrix
    let mut matrix = vec![vec![false; b_size]; a_size];
    let mut assignment = vec![false; n];

    for i in 0..a_size {
        for j in 0..b_size {
            for (k, &var) in a_list.iter().enumerate() {
                assignment[var.position()] = (i >> k) & 1 == 1;
            }
            for (k, &var) in b_list.iter().enumerate() {
                assignment[var.position()] = (j >> k) & 1 == 1;
            }
            matrix[i][j] = f.eval(&assignment);
        }
    }

    // Try each operator
    for op in Operator::all() {
        if let Some((u, v)) = check_rank_1(&matrix, op) {
            let g = TruthTable::from_expr(a_list.len() as u32, |x| {
                let idx = x.iter().enumerate().fold(0, |acc, (i, &b)| {
                    acc | ((b as usize) << i)
                });
                u.get(idx).copied().unwrap_or(false)
            });

            let h = TruthTable::from_expr(b_list.len() as u32, |x| {
                let idx = x.iter().enumerate().fold(0, |acc, (i, &b)| {
                    acc | ((b as usize) << i)
                });
                v.get(idx).copied().unwrap_or(false)
            });

            return SeparabilityResult {
                is_separable: true,
                operator: Some(op),
                g: Some(g),
                h: Some(h),
            };
        }
    }

    SeparabilityResult {
        is_separable: false,
        operator: None,
        g: None,
        h: None,
    }
}

struct SeparabilityResult {
    is_separable: bool,
    operator: Option<Operator>,
    g: Option<TruthTable>,
    h: Option<TruthTable>,
}

fn check_rank_1(matrix: &[Vec<bool>], op: Operator) -> Option<(Vec<bool>, Vec<bool>)> {
    match op {
        Operator::And => check_and_rank_1(matrix),
        Operator::Or => check_or_rank_1(matrix),
        Operator::Xor => check_xor_rank_1(matrix),
    }
}

fn check_and_rank_1(matrix: &[Vec<bool>]) -> Option<(Vec<bool>, Vec<bool>)> {
    if matrix.is_empty() || matrix[0].is_empty() {
        return Some((vec![], vec![]));
    }

    let rows = matrix.len();
    let cols = matrix[0].len();

    let mut u = vec![false; rows];
    let mut v = vec![false; cols];

    for (i, row) in matrix.iter().enumerate() {
        for (j, &val) in row.iter().enumerate() {
            if val {
                u[i] = true;
                v[j] = true;
            }
        }
    }

    for (i, row) in matrix.iter().enumerate() {
        for (j, &val) in row.iter().enumerate() {
            if u[i] && v[j] && !val {
                return None;
            }
        }
    }

    Some((u, v))
}

fn check_or_rank_1(matrix: &[Vec<bool>]) -> Option<(Vec<bool>, Vec<bool>)> {
    if matrix.is_empty() || matrix[0].is_empty() {
        return Some((vec![], vec![]));
    }

    let rows = matrix.len();
    let cols = matrix[0].len();

    let mut u = vec![true; rows];
    let mut v = vec![true; cols];

    for (i, row) in matrix.iter().enumerate() {
        for (j, &val) in row.iter().enumerate() {
            if !val {
                u[i] = false;
                v[j] = false;
            }
        }
    }

    for (i, row) in matrix.iter().enumerate() {
        for (j, &val) in row.iter().enumerate() {
            if !u[i] && !v[j] && val {
                return None;
            }
        }
    }

    Some((u, v))
}

fn check_xor_rank_1(matrix: &[Vec<bool>]) -> Option<(Vec<bool>, Vec<bool>)> {
    if matrix.is_empty() || matrix[0].is_empty() {
        return Some((vec![], vec![]));
    }

    let rows = matrix.len();
    let _cols = matrix[0].len();

    let mut u = vec![false; rows];
    let v: Vec<bool> = matrix[0].clone();

    for (i, row) in matrix.iter().enumerate() {
        u[i] = row[0] ^ v[0];
    }

    for (i, row) in matrix.iter().enumerate() {
        for (j, &val) in row.iter().enumerate() {
            if (u[i] ^ v[j]) != val {
                return None;
            }
        }
    }

    Some((u, v))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::truth_table::named;

    #[test]
    fn test_build_constant() {
        let mut builder = CigBuilder::new();

        let zero = TruthTable::zero(3);
        let cig_zero = builder.build(&zero);
        assert!(cig_zero.root().is_constant());
        assert_eq!(cig_zero.root().as_constant(), Some(false));

        let one = TruthTable::one(3);
        let cig_one = builder.build(&one);
        assert!(cig_one.root().is_constant());
        assert_eq!(cig_one.root().as_constant(), Some(true));
    }

    #[test]
    fn test_build_variable() {
        let mut builder = CigBuilder::new();

        let x1 = TruthTable::var(3, Var(1));
        let cig = builder.build(&x1);

        assert!(cig.root().is_leaf());
        assert_eq!(cig.root().as_leaf(), Some(Var(1)));
    }

    #[test]
    fn test_build_xor() {
        let mut builder = CigBuilder::new();

        // x₁ ⊕ x₂
        let f = TruthTable::from_expr(2, |x| x[0] ^ x[1]);
        let cig = builder.build(&f);

        // Should be separable
        assert!(cig.root().is_internal());

        println!("XOR CIG:\n{}", cig);
    }

    #[test]
    fn test_build_majority() {
        let mut builder = CigBuilder::new();

        let f = named::majority3();
        let cig = builder.build(&f);

        // Majority is irreducible
        assert!(cig.root().is_internal());
        assert_eq!(cig.root().num_children(), 3);
        assert_eq!(cig.interaction_width(), 3);

        println!("MAJ₃ CIG:\n{}", cig);
    }

    #[test]
    fn test_build_composed() {
        let mut builder = CigBuilder::new();

        // (x₁ ⊕ x₂) ∧ (x₃ ⊕ x₄)
        let f = TruthTable::from_expr(4, |x| (x[0] ^ x[1]) && (x[2] ^ x[3]));
        let cig = builder.build(&f);

        println!("Composed CIG:\n{}", cig);
        println!("Size: {}", cig.size());
        println!("Depth: {}", cig.depth());
        println!("Width: {}", cig.interaction_width());
    }

    #[test]
    fn test_equivalence() {
        let mut builder = CigBuilder::new();

        // Two equivalent functions built differently
        let f1 = TruthTable::from_expr(2, |x| x[0] && x[1]);
        let f2 = TruthTable::from_expr(2, |x| !(!x[0] || !x[1])); // De Morgan

        let cig1 = builder.build(&f1);
        let cig2 = builder.build(&f2);

        assert!(cig1.equivalent(&cig2));
    }
}
