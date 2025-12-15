//! Graphviz DOT export for SDDs.
//!
//! This module provides visualization of SDDs in Graphviz DOT format.
//! The output can be rendered using `dot -Tpdf file.dot -o file.pdf`.
//!
//! ## Usage
//!
//! The primary way to generate DOT output is through the [`SddManager`] methods:
//!
//! ```rust
//! use ananke_sdd::SddManager;
//!
//! let mgr = SddManager::new(3);
//! let f = mgr.and(mgr.var(1), mgr.var(2));
//!
//! // Generate DOT output
//! let dot = mgr.to_dot(f);
//! println!("{}", dot);
//! ```
//!
//! For custom configuration, use [`SddManager::to_dot_with_config`] with [`DotConfig`].

use crate::sdd::{Sdd, SddId};
use crate::vtree::VtreeId;
use crate::SddManager;

/// Configuration for DOT export.
#[derive(Debug, Clone)]
pub struct DotConfig {
    /// Show terminal nodes (⊤ and ⊥).
    pub show_terminals: bool,
    /// Use horizontal layout (rankdir=LR).
    pub horizontal: bool,
    /// Font size for labels.
    pub font_size: u32,
    /// Node width.
    pub node_width: f32,
    /// Show vtree node IDs.
    pub show_vtree: bool,
    /// Use HTML tables for element nodes (two-cell rectangles with prime/sub).
    /// When true (default): Elements shown as [prime|sub] tables with literals/terminals inlined.
    /// When false: Elements shown as point nodes with edges to prime/sub nodes (reused).
    pub use_html_tables: bool,
}

impl Default for DotConfig {
    fn default() -> Self {
        Self {
            show_terminals: true,
            horizontal: false,
            font_size: 12,
            node_width: 0.5,
            show_vtree: false,
            use_html_tables: true,
        }
    }
}

impl DotConfig {
    /// Create a config with basic mode (no HTML tables, reused nodes).
    pub fn basic() -> Self {
        Self {
            use_html_tables: false,
            ..Default::default()
        }
    }
}

/// Exports an SDD to Graphviz DOT format.
///
/// This is a convenience wrapper around [`SddManager::to_dot`].
#[inline]
pub fn sdd_to_dot(mgr: &SddManager, f: SddId) -> String {
    mgr.to_dot(f)
}

/// Exports an SDD to Graphviz DOT format with custom configuration.
///
/// This is a convenience wrapper around [`SddManager::to_dot_with_config`].
#[inline]
pub fn sdd_to_dot_with_config(mgr: &SddManager, f: SddId, config: &DotConfig) -> String {
    mgr.to_dot_with_config(f, config)
}

/// Exports a vtree to Graphviz DOT format.
///
/// This is a convenience wrapper around [`SddManager::vtree_to_dot`].
#[inline]
pub fn vtree_to_dot(mgr: &SddManager) -> String {
    mgr.vtree_to_dot()
}

// ============================================================================
// SddManager DOT methods
// ============================================================================

impl SddManager {
    /// Exports an SDD to Graphviz DOT format.
    ///
    /// The output can be rendered using `dot -Tpdf file.dot -o file.pdf`.
    ///
    /// # Example
    ///
    /// ```rust
    /// use ananke_sdd::SddManager;
    ///
    /// let mgr = SddManager::new(3);
    /// let f = mgr.and(mgr.var(1), mgr.var(2));
    /// let dot = mgr.to_dot(f);
    /// assert!(dot.contains("digraph"));
    /// ```
    pub fn to_dot(&self, f: SddId) -> String {
        self.to_dot_with_config(f, &DotConfig::default())
    }

    /// Exports an SDD to Graphviz DOT format with custom configuration.
    ///
    /// # Example
    ///
    /// ```rust
    /// use ananke_sdd::SddManager;
    /// use ananke_sdd::dot::DotConfig;
    ///
    /// let mgr = SddManager::new(3);
    /// let f = mgr.and(mgr.var(1), mgr.var(2));
    /// let config = DotConfig {
    ///     show_terminals: true,
    ///     horizontal: true,
    ///     ..Default::default()
    /// };
    /// let dot = mgr.to_dot_with_config(f, &config);
    /// assert!(dot.contains("rankdir=LR"));
    /// ```
    pub fn to_dot_with_config(&self, f: SddId, config: &DotConfig) -> String {
        if config.use_html_tables {
            self.to_dot_html(f, config)
        } else {
            self.to_dot_basic(f, config)
        }
    }

    /// HTML mode: Elements as two-cell tables with literals/terminals inlined.
    fn to_dot_html(&self, f: SddId, config: &DotConfig) -> String {
        use std::collections::HashSet;
        use std::fmt::Write;

        let mut dot = String::new();

        writeln!(dot, "digraph SDD {{").unwrap();

        if config.horizontal {
            writeln!(dot, "  rankdir=LR;").unwrap();
        }

        writeln!(dot, "  node [fontsize={}, width={}];", config.font_size, config.node_width).unwrap();

        // Handle root node if it's a terminal or literal (no decision node to contain it)
        let root_node = self.node(f);
        match &root_node {
            Sdd::False => {
                writeln!(dot, "  n{} [label=\"⊥\", shape=box, style=filled, fillcolor=lightgray];", f.raw()).unwrap();
                writeln!(dot, "}}").unwrap();
                return dot;
            }
            Sdd::True => {
                writeln!(dot, "  n{} [label=\"⊤\", shape=box, style=filled, fillcolor=lightgray];", f.raw()).unwrap();
                writeln!(dot, "}}").unwrap();
                return dot;
            }
            Sdd::Literal(lit) => {
                let label = if lit.is_positive() {
                    format!("x{}", lit.var())
                } else {
                    format!("¬x{}", lit.var())
                };
                writeln!(dot, "  n{} [label=\"{}\", shape=ellipse];", f.raw(), label).unwrap();
                writeln!(dot, "}}").unwrap();
                return dot;
            }
            Sdd::Decision { .. } => {
                // Continue with normal processing
            }
        }

        // Collect all decision nodes (we only create explicit nodes for decisions)
        let mut visited = HashSet::new();
        let mut nodes_to_visit = vec![f];

        while let Some(current) = nodes_to_visit.pop() {
            if visited.contains(&current) {
                continue;
            }
            visited.insert(current);

            let node = self.node(current);

            match &node {
                Sdd::False | Sdd::True | Sdd::Literal(_) => {
                    // In HTML mode, terminals and literals are inlined in table cells.
                    // We don't create separate nodes for them.
                }
                Sdd::Decision { vtree, elements } => {
                    // Decision node as a circle with ID
                    let vtree_label = if config.show_vtree {
                        format!("\\n[v{}]", vtree.raw())
                    } else {
                        String::new()
                    };

                    writeln!(
                        dot,
                        "  n{} [label=\"{}{}\", shape=circle];",
                        current.raw(),
                        current.raw(),
                        vtree_label
                    )
                    .unwrap();

                    // Create element nodes as HTML tables
                    for (i, elem) in elements.iter().enumerate() {
                        let elem_id = format!("n{}_e{}", current.raw(), i);

                        // Get cell content for prime and sub
                        let prime_cell = self.cell_content(elem.prime, &mut nodes_to_visit);
                        let sub_cell = self.cell_content(elem.sub, &mut nodes_to_visit);

                        // HTML table with two cells
                        writeln!(
                            dot,
                            "  {} [label=<<TABLE BORDER=\"0\" CELLBORDER=\"1\" CELLSPACING=\"0\"><TR><TD PORT=\"p\">{}</TD><TD PORT=\"s\">{}</TD></TR></TABLE>>, shape=none];",
                            elem_id, prime_cell, sub_cell
                        )
                        .unwrap();

                        // Edge from decision node to element
                        writeln!(dot, "  n{} -> {};", current.raw(), elem_id).unwrap();

                        // If prime/sub are decision nodes, add edges from cells to them
                        if self.is_decision(elem.prime) {
                            writeln!(dot, "  {}:p -> n{} [style=solid];", elem_id, elem.prime.raw()).unwrap();
                        }
                        if self.is_decision(elem.sub) {
                            writeln!(dot, "  {}:s -> n{} [style=dashed];", elem_id, elem.sub.raw()).unwrap();
                        }
                    }
                }
            }
        }

        writeln!(dot, "}}").unwrap();
        dot
    }

    /// Get the cell content for an SDD node.
    /// Returns HTML content for the cell.
    /// If it's a decision node, returns the ID (will be linked via edge).
    /// If it's a terminal/literal, returns the label (inlined).
    fn cell_content(&self, id: SddId, nodes_to_visit: &mut Vec<SddId>) -> String {
        let node = self.node(id);
        match &node {
            Sdd::False => "⊥".to_string(),
            Sdd::True => "⊤".to_string(),
            Sdd::Literal(lit) => {
                if lit.is_positive() {
                    format!("x{}", lit.var())
                } else {
                    format!("¬x{}", lit.var())
                }
            }
            Sdd::Decision { .. } => {
                // Add to visit list and return ID as label
                nodes_to_visit.push(id);
                format!("○{}", id.raw())
            }
        }
    }

    /// Check if an SDD node is a decision node.
    fn is_decision(&self, id: SddId) -> bool {
        matches!(self.node(id), Sdd::Decision { .. })
    }

    /// Basic mode: Point nodes with edges for prime/sub (reused nodes).
    fn to_dot_basic(&self, f: SddId, config: &DotConfig) -> String {
        use std::collections::HashSet;
        use std::fmt::Write;

        let mut dot = String::new();

        writeln!(dot, "digraph SDD {{").unwrap();

        if config.horizontal {
            writeln!(dot, "  rankdir=LR;").unwrap();
        }

        writeln!(dot, "  node [fontsize={}, width={}];", config.font_size, config.node_width).unwrap();

        // Collect all nodes
        let mut visited = HashSet::new();
        let mut nodes_to_visit = vec![f];

        while let Some(current) = nodes_to_visit.pop() {
            if visited.contains(&current) {
                continue;
            }
            visited.insert(current);

            let node = self.node(current);

            match &node {
                Sdd::False => {
                    if config.show_terminals {
                        writeln!(
                            dot,
                            "  n{} [label=\"⊥\", shape=box, style=filled, fillcolor=lightgray];",
                            current.raw()
                        )
                        .unwrap();
                    }
                }
                Sdd::True => {
                    if config.show_terminals {
                        writeln!(
                            dot,
                            "  n{} [label=\"⊤\", shape=box, style=filled, fillcolor=lightgray];",
                            current.raw()
                        )
                        .unwrap();
                    }
                }
                Sdd::Literal(lit) => {
                    let label = if lit.is_positive() {
                        format!("x{}", lit.var())
                    } else {
                        format!("¬x{}", lit.var())
                    };
                    writeln!(dot, "  n{} [label=\"{}\", shape=ellipse];", current.raw(), label).unwrap();
                }
                Sdd::Decision { vtree, elements } => {
                    // Decision node as a circle
                    let vtree_label = if config.show_vtree {
                        format!(" [v{}]", vtree.raw())
                    } else {
                        String::new()
                    };

                    writeln!(
                        dot,
                        "  n{} [label=\"{}{}\", shape=circle];",
                        current.raw(),
                        current.raw(),
                        vtree_label
                    )
                    .unwrap();

                    // Add element nodes as small points
                    for (i, elem) in elements.iter().enumerate() {
                        let elem_id = format!("n{}_e{}", current.raw(), i);
                        writeln!(dot, "  {} [label=\"\", shape=point, width=0.1];", elem_id).unwrap();

                        // Edge from decision to element
                        writeln!(dot, "  n{} -> {};", current.raw(), elem_id).unwrap();

                        // Prime edge (solid)
                        writeln!(dot, "  {} -> n{} [label=\"p\", style=solid];", elem_id, elem.prime.raw()).unwrap();

                        // Sub edge (dashed)
                        writeln!(dot, "  {} -> n{} [label=\"s\", style=dashed];", elem_id, elem.sub.raw()).unwrap();

                        // Add children to visit list
                        nodes_to_visit.push(elem.prime);
                        nodes_to_visit.push(elem.sub);
                    }
                }
            }
        }

        writeln!(dot, "}}").unwrap();
        dot
    }

    /// Exports the vtree to Graphviz DOT format.
    ///
    /// # Example
    ///
    /// ```rust
    /// use ananke_sdd::SddManager;
    ///
    /// let mgr = SddManager::new(4);
    /// let dot = mgr.vtree_to_dot();
    /// assert!(dot.contains("digraph Vtree"));
    /// ```
    pub fn vtree_to_dot(&self) -> String {
        use std::fmt::Write;

        let vtree = self.vtree();
        let mut dot = String::new();

        writeln!(dot, "digraph Vtree {{").unwrap();
        writeln!(dot, "  node [fontsize=12];").unwrap();

        // Visit all vtree nodes
        for i in 0..vtree.num_nodes() {
            let id = VtreeId::new(i as u32);
            let node = vtree.node(id);

            match node {
                crate::vtree::VtreeNode::Leaf { var } => {
                    writeln!(dot, "  v{} [label=\"x{}\", shape=ellipse];", id.raw(), var).unwrap();
                }
                crate::vtree::VtreeNode::Internal { left, right } => {
                    writeln!(dot, "  v{} [label=\"{}\", shape=circle];", id.raw(), id.raw()).unwrap();
                    writeln!(dot, "  v{} -> v{} [label=\"L\"];", id.raw(), left.raw()).unwrap();
                    writeln!(dot, "  v{} -> v{} [label=\"R\"];", id.raw(), right.raw()).unwrap();
                }
            }
        }

        writeln!(dot, "}}").unwrap();
        dot
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_constant_to_dot() {
        let mgr = SddManager::new(2);
        let dot = sdd_to_dot(&mgr, mgr.true_sdd());
        assert!(dot.contains("digraph"));
        assert!(dot.contains("⊤"));
    }

    #[test]
    fn test_literal_to_dot() {
        let mgr = SddManager::new(2);
        let x1 = mgr.var(1);
        let dot = sdd_to_dot(&mgr, x1);
        assert!(dot.contains("x1"));
    }

    #[test]
    fn test_vtree_to_dot() {
        let mgr = SddManager::new(4);
        let dot = vtree_to_dot(&mgr);
        assert!(dot.contains("digraph Vtree"));
        assert!(dot.contains("x1"));
        assert!(dot.contains("x4"));
    }

    #[test]
    fn test_html_mode() {
        let mgr = SddManager::new(2);
        let f = mgr.and(mgr.var(1), mgr.var(2));
        let dot = mgr.to_dot(f); // Default is HTML mode
        assert!(dot.contains("TABLE"));
        assert!(dot.contains("CELLBORDER"));
        assert!(dot.contains("shape=circle")); // Decision node
    }

    #[test]
    fn test_basic_mode() {
        let mgr = SddManager::new(2);
        let f = mgr.and(mgr.var(1), mgr.var(2));
        let config = DotConfig::basic();
        let dot = mgr.to_dot_with_config(f, &config);
        assert!(!dot.contains("TABLE"));
        assert!(dot.contains("shape=point")); // Element nodes
        assert!(dot.contains("style=solid")); // Prime edges
        assert!(dot.contains("style=dashed")); // Sub edges
    }
}
