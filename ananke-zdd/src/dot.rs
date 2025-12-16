//! Graphviz DOT export for ZDD visualization.

use std::collections::HashSet;
use std::fmt::Write;

use crate::reference::ZddId;
use crate::zdd::ZddManager;

impl ZddManager {
    /// Generates a DOT representation of the ZDD for Graphviz visualization.
    ///
    /// # Example
    ///
    /// ```
    /// use ananke_zdd::zdd::ZddManager;
    ///
    /// let mgr = ZddManager::new();
    /// let x1 = mgr.base(1);
    /// let x2 = mgr.base(2);
    /// let union = mgr.union(x1, x2);
    ///
    /// let dot = mgr.to_dot(union);
    /// println!("{}", dot);
    /// ```
    pub fn to_dot(&self, root: ZddId) -> String {
        let mut dot = String::new();
        writeln!(dot, "digraph ZDD {{").unwrap();
        writeln!(dot, "  rankdir=TB;").unwrap();
        writeln!(dot, "  node [shape=circle];").unwrap();
        writeln!(dot).unwrap();

        // Terminal nodes
        writeln!(dot, "  // Terminals").unwrap();
        writeln!(dot, "  zero [label=\"⊥\", shape=square];").unwrap();
        writeln!(dot, "  one [label=\"⊤\", shape=square];").unwrap();
        writeln!(dot).unwrap();

        // Collect all nodes
        let mut visited = HashSet::new();
        let mut nodes_by_level: Vec<Vec<ZddId>> = Vec::new();
        self.collect_nodes(root, &mut visited, &mut nodes_by_level);

        // Output nodes by level for better layout
        for (level, nodes) in nodes_by_level.iter().enumerate() {
            if !nodes.is_empty() {
                writeln!(dot, "  // Level {}", level).unwrap();
                writeln!(dot, "  {{ rank=same;").unwrap();
                for &id in nodes {
                    let node = self.node(id);
                    writeln!(dot, "    n{} [label=\"{}\"];", id.raw(), node.var).unwrap();
                }
                writeln!(dot, "  }}").unwrap();
            }
        }

        writeln!(dot).unwrap();
        writeln!(dot, "  // Edges").unwrap();

        // Output edges
        for id in visited.iter() {
            if id.is_terminal() {
                continue;
            }
            let node = self.node(*id);
            let lo_target = if node.lo.is_zero() {
                "zero".to_string()
            } else if node.lo.is_one() {
                "one".to_string()
            } else {
                format!("n{}", node.lo.raw())
            };
            let hi_target = if node.hi.is_zero() {
                "zero".to_string()
            } else if node.hi.is_one() {
                "one".to_string()
            } else {
                format!("n{}", node.hi.raw())
            };

            // Lo edge (dashed)
            writeln!(dot, "  n{} -> {} [style=dashed];", id.raw(), lo_target).unwrap();
            // Hi edge (solid)
            writeln!(dot, "  n{} -> {};", id.raw(), hi_target).unwrap();
        }

        writeln!(dot, "}}").unwrap();
        dot
    }

    fn collect_nodes(&self, id: ZddId, visited: &mut HashSet<ZddId>, nodes_by_level: &mut Vec<Vec<ZddId>>) {
        if id.is_terminal() || visited.contains(&id) {
            return;
        }
        visited.insert(id);

        let node = self.node(id);
        let level = self.level(node.var).index();

        while nodes_by_level.len() <= level {
            nodes_by_level.push(Vec::new());
        }
        nodes_by_level[level].push(id);

        self.collect_nodes(node.lo, visited, nodes_by_level);
        self.collect_nodes(node.hi, visited, nodes_by_level);
    }

    /// Generates DOT for multiple ZDDs with labeled roots.
    pub fn to_dot_multi(&self, roots: &[(ZddId, &str)]) -> String {
        let mut dot = String::new();
        writeln!(dot, "digraph ZDD {{").unwrap();
        writeln!(dot, "  rankdir=TB;").unwrap();
        writeln!(dot, "  node [shape=circle];").unwrap();
        writeln!(dot).unwrap();

        // Invisible root nodes for labels
        writeln!(dot, "  // Root labels").unwrap();
        for (i, (_, label)) in roots.iter().enumerate() {
            writeln!(dot, "  root{} [label=\"{}\", shape=none];", i, label).unwrap();
        }
        writeln!(dot).unwrap();

        // Terminals
        writeln!(dot, "  // Terminals").unwrap();
        writeln!(dot, "  zero [label=\"⊥\", shape=square];").unwrap();
        writeln!(dot, "  one [label=\"⊤\", shape=square];").unwrap();
        writeln!(dot).unwrap();

        // Collect all nodes from all roots
        let mut visited = HashSet::new();
        let mut nodes_by_level: Vec<Vec<ZddId>> = Vec::new();
        for (id, _) in roots {
            self.collect_nodes(*id, &mut visited, &mut nodes_by_level);
        }

        // Output nodes
        for (level, nodes) in nodes_by_level.iter().enumerate() {
            if !nodes.is_empty() {
                writeln!(dot, "  // Level {}", level).unwrap();
                writeln!(dot, "  {{ rank=same;").unwrap();
                for &id in nodes {
                    let node = self.node(id);
                    writeln!(dot, "    n{} [label=\"{}\"];", id.raw(), node.var).unwrap();
                }
                writeln!(dot, "  }}").unwrap();
            }
        }

        writeln!(dot).unwrap();

        // Root edges
        writeln!(dot, "  // Root edges").unwrap();
        for (i, (id, _)) in roots.iter().enumerate() {
            let target = if id.is_zero() {
                "zero".to_string()
            } else if id.is_one() {
                "one".to_string()
            } else {
                format!("n{}", id.raw())
            };
            writeln!(dot, "  root{} -> {} [style=bold];", i, target).unwrap();
        }
        writeln!(dot).unwrap();

        // Edges
        writeln!(dot, "  // Edges").unwrap();
        for id in visited.iter() {
            if id.is_terminal() {
                continue;
            }
            let node = self.node(*id);
            let lo_target = if node.lo.is_zero() {
                "zero".to_string()
            } else if node.lo.is_one() {
                "one".to_string()
            } else {
                format!("n{}", node.lo.raw())
            };
            let hi_target = if node.hi.is_zero() {
                "zero".to_string()
            } else if node.hi.is_one() {
                "one".to_string()
            } else {
                format!("n{}", node.hi.raw())
            };

            writeln!(dot, "  n{} -> {} [style=dashed];", id.raw(), lo_target).unwrap();
            writeln!(dot, "  n{} -> {};", id.raw(), hi_target).unwrap();
        }

        writeln!(dot, "}}").unwrap();
        dot
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_dot_empty() {
        let mgr = ZddManager::new();
        let dot = mgr.to_dot(ZddId::ZERO);
        assert!(dot.contains("digraph ZDD"));
        assert!(dot.contains("zero"));
    }

    #[test]
    fn test_dot_base() {
        let mgr = ZddManager::new();
        let x1 = mgr.base(1);
        let dot = mgr.to_dot(x1);
        assert!(dot.contains("x1"));
        assert!(dot.contains("one"));
    }
}
