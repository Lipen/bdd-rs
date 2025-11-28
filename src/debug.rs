//! Debug utilities for inspecting BDD structure.
//!
//! This module provides helpers for exploring and debugging BDDs.
//! These are primarily useful in tests and during development.

use std::collections::HashSet;
use std::fmt::Write;

use crate::bdd::Bdd;
use crate::reference::Ref;
use crate::types::Var;

/// Detailed information about a single BDD node.
#[derive(Debug, Clone)]
pub struct NodeInfo {
    /// The reference to this node
    pub node_ref: Ref,
    /// Variable at this node (None for terminals)
    pub variable: Option<Var>,
    /// Level of the variable in current ordering (None for terminals)
    pub level: Option<usize>,
    /// Low child reference
    pub low: Option<Ref>,
    /// High child reference
    pub high: Option<Ref>,
    /// Is this the ONE terminal
    pub is_one: bool,
    /// Is this the ZERO terminal
    pub is_zero: bool,
}

impl std::fmt::Display for NodeInfo {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.is_one {
            write!(f, "ONE")
        } else if self.is_zero {
            write!(f, "ZERO")
        } else {
            write!(
                f,
                "{}(var={}, level={}, low={}, high={})",
                self.node_ref,
                self.variable.map_or("?".to_string(), |v| v.to_string()),
                self.level.map_or("?".to_string(), |l| l.to_string()),
                self.low.map_or("?".to_string(), |r| r.to_string()),
                self.high.map_or("?".to_string(), |r| r.to_string()),
            )
        }
    }
}

/// A tree representation of a BDD for debugging.
#[derive(Debug, Clone)]
pub struct BddTree {
    pub root: Ref,
    pub nodes: Vec<NodeInfo>,
}

impl std::fmt::Display for BddTree {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "BDD Tree (root = {}):", self.root)?;
        for node in &self.nodes {
            writeln!(f, "  {}", node)?;
        }
        Ok(())
    }
}

impl Bdd {
    /// Get detailed information about a single node.
    pub fn node_info(&self, node_ref: Ref) -> NodeInfo {
        if self.is_one(node_ref) {
            return NodeInfo {
                node_ref,
                variable: None,
                level: None,
                low: None,
                high: None,
                is_one: true,
                is_zero: false,
            };
        }

        if self.is_zero(node_ref) {
            return NodeInfo {
                node_ref,
                variable: None,
                level: None,
                low: None,
                high: None,
                is_one: false,
                is_zero: true,
            };
        }

        let node = self.node(node_ref.id());
        let variable = node.variable;
        let level = self.get_level(variable).map(|l| l.index());

        NodeInfo {
            node_ref,
            variable: Some(variable),
            level,
            low: Some(self.low_node(node_ref)),
            high: Some(self.high_node(node_ref)),
            is_one: false,
            is_zero: false,
        }
    }

    /// Get a tree representation of a BDD for debugging.
    ///
    /// Returns all nodes reachable from the root in BFS order.
    pub fn debug_tree(&self, root: Ref) -> BddTree {
        let mut nodes = Vec::new();
        let mut visited = HashSet::new();
        let mut stack = vec![root];

        while let Some(node_ref) = stack.pop() {
            if visited.contains(&node_ref) {
                continue;
            }
            visited.insert(node_ref);

            let info = self.node_info(node_ref);
            nodes.push(info.clone());

            if !self.is_terminal(node_ref) {
                if let Some(low) = info.low {
                    stack.push(low);
                }
                if let Some(high) = info.high {
                    stack.push(high);
                }
            }
        }

        // Sort by level for easier reading
        nodes.sort_by_key(|n| {
            if n.is_one || n.is_zero {
                usize::MAX
            } else {
                n.level.unwrap_or(usize::MAX - 1)
            }
        });

        BddTree { root, nodes }
    }

    /// Print a compact representation of a BDD.
    ///
    /// Format: `root -> var@level(low, high)`
    pub fn debug_string(&self, root: Ref) -> String {
        let mut result = String::new();
        let tree = self.debug_tree(root);

        writeln!(&mut result, "BDD {} (size={}):", root, tree.nodes.len()).unwrap();
        for node in &tree.nodes {
            writeln!(&mut result, "  {}", node).unwrap();
        }
        result
    }

    /// Print the current variable ordering.
    pub fn debug_ordering(&self) -> String {
        let mut result = String::from("Ordering: [");
        for level_idx in 0..self.num_levels() {
            if level_idx > 0 {
                result.push_str(", ");
            }
            if let Some(var) = self.get_variable_at_level(crate::types::Level::new(level_idx)) {
                write!(&mut result, "{}@L{}", var, level_idx).unwrap();
            }
        }
        result.push(']');
        result
    }

    /// Verify that a BDD evaluates correctly for all variable assignments.
    ///
    /// Returns a list of assignments where evaluation doesn't match expected.
    pub fn verify_truth_table(&self, root: Ref, vars: &[Var], expected_fn: impl Fn(&[bool]) -> bool) -> Vec<(Vec<bool>, bool, bool)> {
        let mut failures = Vec::new();
        let n = vars.len();

        for bits in 0..(1 << n) {
            let assignment: Vec<bool> = (0..n).map(|i| (bits >> i) & 1 == 1).collect();

            // Build cofactor cube
            let cube: Vec<i32> = vars
                .iter()
                .zip(&assignment)
                .map(|(var, &val)| {
                    let v = var.id() as i32;
                    if val {
                        v
                    } else {
                        -v
                    }
                })
                .collect();

            let result = self.cofactor_cube(root, cube.iter().copied());
            let actual = self.is_one(result);
            let expected = expected_fn(&assignment);

            if actual != expected {
                failures.push((assignment, expected, actual));
            }
        }

        failures
    }

    /// Dump complete BDD state for debugging.
    pub fn dump_state(&self) -> String {
        let mut result = String::new();

        writeln!(&mut result, "=== BDD State ===").unwrap();
        writeln!(&mut result, "{}", self.debug_ordering()).unwrap();

        writeln!(&mut result, "Nodes: count={}", self.num_nodes(),).unwrap();

        // Print nodes at each level
        writeln!(&mut result, "Nodes by level:").unwrap();
        for level_idx in 0..self.num_levels() {
            let level = crate::types::Level::new(level_idx);
            let nodes = self.get_nodes_at_level(level);
            if !nodes.is_empty() {
                let var = self.get_variable_at_level(level);
                writeln!(&mut result, "  Level {} (var {:?}): {:?}", level_idx, var, nodes).unwrap();
            }
        }

        result
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_node_info() {
        let bdd = Bdd::default();
        let x = bdd.mk_var(1);

        let info = bdd.node_info(x);
        assert_eq!(info.variable, Some(Var::new(1)));
        assert_eq!(info.level, Some(0));
        assert!(!info.is_one);
        assert!(!info.is_zero);
    }

    #[test]
    fn test_debug_tree() {
        let bdd = Bdd::default();
        let x = bdd.mk_var(1);
        let y = bdd.mk_var(2);
        let f = bdd.apply_and(x, y);

        let tree = bdd.debug_tree(f);
        assert_eq!(tree.root, f);
        // Should have: root node (x1), y node (x2), ONE terminal, ZERO terminal
        // ZERO is reachable via ~@1 (negation of ONE)
        assert_eq!(tree.nodes.len(), 4);
    }

    #[test]
    fn test_verify_truth_table() {
        let bdd = Bdd::default();
        let x = bdd.mk_var(1);
        let y = bdd.mk_var(2);
        let f = bdd.apply_and(x, y);

        let vars = vec![Var::new(1), Var::new(2)];
        let failures = bdd.verify_truth_table(f, &vars, |assignment| {
            // AND: both must be true
            assignment[0] && assignment[1]
        });

        assert!(failures.is_empty(), "Truth table verification failed: {:?}", failures);
    }

    #[test]
    fn test_debug_string() {
        let bdd = Bdd::default();
        let x = bdd.mk_var(1);
        let s = bdd.debug_string(x);
        // Variable node should show var=x1 (Display format for Var)
        assert!(s.contains("var=x1"), "Expected var=x1 in: {}", s);
        assert!(s.contains("level=0"), "Expected level=0 in: {}", s);
    }
}
