//! BDD to DOT (Graphviz) conversion.
//!
//! This module provides functionality to convert Binary Decision Diagrams (BDDs) into DOT format,
//! which can be visualized using Graphviz tools like `dot`, `neato`, or online viewers.
//!
//! # DOT Format
//!
//! The generated DOT output follows these conventions:
//! - **Terminal nodes** (0 and 1) are rendered as squares at the bottom (sink rank)
//! - **Variable nodes** are rendered as circles, grouped by their variable level
//! - **Edges**:
//!   - Solid lines represent high (then) edges
//!   - Dashed lines represent low (else) edges
//!   - Dotted lines with hollow circles represent negated edges
//! - **Root nodes** are rendered as rectangles at the top (source rank)
//!
//! # Examples
//!
//! ```
//! use bdd_rs::bdd::Bdd;
//!
//! let bdd = Bdd::default();
//! let x1 = bdd.mk_var(1);
//! let x2 = bdd.mk_var(2);
//! let f = bdd.apply_and(x1, x2);
//!
//! let dot = bdd.to_dot(&[f]).unwrap();
//! // Write to file and render with: dot -Tpng output.dot -o output.png
//! ```

use std::collections::BTreeMap;

use crate::bdd::Bdd;
use crate::reference::Ref;

/// Configuration options for DOT output generation.
///
/// This struct allows customization of the visual appearance and structure of the generated
/// DOT graph. Use `DotConfig::default()` for standard settings.
///
/// # Examples
///
/// ```
/// use bdd_rs::bdd::Bdd;
/// use bdd_rs::dot::DotConfig;
///
/// let bdd = Bdd::default();
/// let x = bdd.mk_var(1);
/// let config = DotConfig {
///     node_shape: "circle",
///     terminal_shape: "square",
///     root_shape: "rect",
///     high_edge_style: "solid",
///     low_edge_style: "dashed",
///     negated_edge_style: "dotted",
///     use_html_labels: true,
/// };
///
/// let dot = bdd.to_dot_with_config(&[x], &config).unwrap();
/// ```
#[derive(Debug, Clone)]
pub struct DotConfig {
    /// Shape for variable nodes (default: "circle")
    pub node_shape: &'static str,
    /// Shape for terminal nodes (default: "square")
    pub terminal_shape: &'static str,
    /// Shape for root nodes (default: "rect")
    pub root_shape: &'static str,
    /// Style for high (then) edges (default: "solid")
    pub high_edge_style: &'static str,
    /// Style for low (else) edges (default: "dashed")
    pub low_edge_style: &'static str,
    /// Style for negated edges (default: "dotted")
    pub negated_edge_style: &'static str,
    /// Whether to use HTML labels for subscripts (default: true)
    pub use_html_labels: bool,
}

impl Default for DotConfig {
    fn default() -> Self {
        Self {
            node_shape: "circle",
            terminal_shape: "square",
            root_shape: "rect",
            high_edge_style: "solid",
            low_edge_style: "dashed",
            negated_edge_style: "dotted",
            use_html_labels: true,
        }
    }
}

impl Bdd {
    /// Converts a BDD to DOT (Graphviz) format.
    ///
    /// This method generates a DOT representation of the BDD rooted at the given nodes.
    /// The output can be rendered using Graphviz tools like `dot` to create visual diagrams
    /// of the BDD structure.
    ///
    /// # Arguments
    ///
    /// * `roots` - A slice of BDD node references to include in the graph. All reachable
    ///   nodes from these roots will be included in the output.
    ///
    /// # Returns
    ///
    /// * `Ok(String)` - A DOT-formatted string representation of the BDD
    /// * `Err(std::fmt::Error)` - If string formatting fails (rare)
    ///
    /// # Graph Structure
    ///
    /// The generated graph has the following properties:
    ///
    /// - **Nodes**:
    ///   - Terminal nodes (0 and 1) are squares at the bottom (sink rank)
    ///   - Variable nodes are circles, labeled with their variable index
    ///   - Nodes at the same variable level are grouped together (same rank)
    ///   - Root nodes are rectangles at the top (source rank)
    ///
    /// - **Edges**:
    ///   - Solid edges: high/then branches (when variable is true)
    ///   - Dashed edges: low/else branches (when variable is false)
    ///   - Dotted edges with hollow circle: negated pointers
    ///
    /// # Examples
    ///
    /// ```
    /// use bdd_rs::bdd::Bdd;
    ///
    /// let bdd = Bdd::default();
    ///
    /// // Create a simple formula: x1 AND x2
    /// let x1 = bdd.mk_var(1);
    /// let x2 = bdd.mk_var(2);
    /// let f = bdd.apply_and(x1, x2);
    ///
    /// let dot = bdd.to_dot(&[f]).unwrap();
    /// println!("{}", dot);
    ///
    /// // To render the graph:
    /// // std::fs::write("output.dot", dot).unwrap();
    /// // Then run: dot -Tpng output.dot -o output.png
    /// ```
    ///
    /// # Visualizing Multiple Functions
    ///
    /// ```
    /// use bdd_rs::bdd::Bdd;
    ///
    /// let bdd = Bdd::default();
    /// let x = bdd.mk_var(1);
    /// let y = bdd.mk_var(2);
    ///
    /// let and = bdd.apply_and(x, y);
    /// let or = bdd.apply_or(x, y);
    /// let xor = bdd.apply_xor(x, y);
    ///
    /// // Visualize all three functions together (shared nodes will be displayed once)
    /// let dot = bdd.to_dot(&[and, or, xor]).unwrap();
    /// ```
    pub fn to_dot(&self, roots: &[Ref]) -> Result<String, std::fmt::Error> {
        self.to_dot_with_config(roots, &DotConfig::default())
    }

    /// Converts a BDD to DOT format with custom configuration.
    ///
    /// This is a more flexible version of `to_dot` that allows customization of the
    /// visual appearance through a `DotConfig` object.
    ///
    /// # Arguments
    ///
    /// * `roots` - A slice of BDD node references to include in the graph
    /// * `config` - Configuration options for DOT generation
    ///
    /// # Examples
    ///
    /// ```
    /// use bdd_rs::bdd::Bdd;
    /// use bdd_rs::dot::DotConfig;
    ///
    /// let bdd = Bdd::default();
    /// let x = bdd.mk_var(1);
    /// let y = bdd.mk_var(2);
    /// let f = bdd.apply_and(x, y);
    ///
    /// let config = DotConfig {
    ///     node_shape: "ellipse",
    ///     ..DotConfig::default()
    /// };
    ///
    /// let dot = bdd.to_dot_with_config(&[f], &config).unwrap();
    /// ```
    pub fn to_dot_with_config(&self, roots: &[Ref], config: &DotConfig) -> Result<String, std::fmt::Error> {
        use std::fmt::Write as _;

        let mut dot = String::new();
        writeln!(dot, "graph {{")?;
        writeln!(dot, "node [shape={}, fixedsize=true];", config.node_shape)?;

        // Terminal nodes (0 and 1)
        writeln!(dot, "{{ rank=sink")?;
        writeln!(dot, "0 [shape={}, label=\"0\"];", config.terminal_shape)?;
        writeln!(dot, "1 [shape={}, label=\"1\"];", config.terminal_shape)?;
        writeln!(dot, "}}")?;

        // Get all reachable nodes from roots
        let all_nodes = self.descendants(roots.iter().copied());

        // Organize nodes by variable level for better layout
        // This groups nodes at the same level together in the visualization
        let mut levels = BTreeMap::<usize, Vec<u32>>::new();
        // Group nodes by their variable level
        for &id in all_nodes.iter() {
            if id == 1 {
                continue; // Skip terminal node (handled separately)
            }
            let level = self.variable(id).id() as usize;
            levels.entry(level).or_default().push(id);
        }

        // Output nodes grouped by level (for proper ranking)
        for level in levels.values() {
            writeln!(dot, "{{ rank=same")?;
            for &id in level.iter() {
                // Label shows variable index
                let label = if config.use_html_labels {
                    format!("<x<SUB>{}</SUB>>", self.variable(id))
                } else {
                    format!("\"x{}\"", self.variable(id))
                };
                writeln!(dot, "{} [label={}];", id, label)?;
            }
            writeln!(dot, "}}")?;
        }

        // Render edges from each node
        // High edges are solid, low edges are dashed, negated edges are dotted with hollow circle
        for &id in all_nodes.iter() {
            if id == 1 {
                continue; // Terminal node has no outgoing edges
            }

            // High edge (then branch) - configured style
            let high = self.high(id);
            assert!(!high.is_negated()); // BDD canonicity: high edges are never negated
            writeln!(dot, "{} -- {} [style={}];", id, high.index(), config.high_edge_style)?;

            // Low edge (else branch) - configured style or dotted depending on negation
            let low = self.low(id);
            if low.is_negated() {
                if low.index() == 1 {
                    // Negated terminal (points to 0)
                    assert_eq!(low, self.zero);
                    writeln!(dot, "{} -- 0 [style={}];", id, config.low_edge_style)?;
                } else {
                    // Negated non-terminal edge (dotted with hollow circle)
                    writeln!(
                        dot,
                        "{} -- {} [style={}, dir=forward, arrowhead=odot];",
                        id,
                        low.index(),
                        config.negated_edge_style
                    )?;
                }
            } else {
                // Regular low edge
                writeln!(dot, "{} -- {} [style={}];", id, low.index(), config.low_edge_style)?;
            }
        }

        // Render root nodes at the top
        writeln!(dot, "{{ rank=source")?;
        for (i, root) in roots.iter().enumerate() {
            writeln!(dot, "r{} [shape={}, label=\"{}\"];", i, config.root_shape, root)?;
        }
        writeln!(dot, "}}")?;

        // Render edges from roots to their respective BDD nodes
        for (i, &root) in roots.iter().enumerate() {
            if root.is_negated() {
                if root.index() == 1 {
                    // Root points to constant 0
                    writeln!(dot, "r{} -- 0;", i)?;
                } else {
                    // Root points to negated node
                    writeln!(dot, "r{} -- {} [dir=forward, arrowhead=odot];", i, root.index())?;
                }
            } else {
                // Root points to positive node
                writeln!(dot, "r{} -- {};", i, root.index())?;
            }
        }

        writeln!(dot, "}}")?;
        Ok(dot)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Basic test: verify DOT output is generated without errors
    #[test]
    fn test_to_dot_basic() {
        let bdd = Bdd::default();
        let f = bdd.mk_cube([-1, 2, 3]);

        // Should generate valid DOT string without panicking
        let dot = bdd.to_dot(&[f]).unwrap();

        // Check very basic structure only
        assert!(dot.starts_with("graph {"));
        assert!(dot.ends_with("}\n"));
        assert!(!dot.is_empty());
    }

    /// Test with multiple roots
    #[test]
    fn test_to_dot_multiple_roots() {
        let bdd = Bdd::default();
        let x1 = bdd.mk_var(1);
        let x2 = bdd.mk_var(2);
        let f = bdd.apply_and(x1, x2);

        // Should handle multiple roots without errors
        let dot = bdd.to_dot(&[f, bdd.zero, bdd.one]).unwrap();
        assert!(dot.starts_with("graph {"));
        assert!(!dot.is_empty());
    }

    /// Test with constants only
    #[test]
    fn test_to_dot_constants() {
        let bdd = Bdd::default();

        // Should handle terminal nodes
        let dot = bdd.to_dot(&[bdd.zero, bdd.one]).unwrap();
        assert!(dot.starts_with("graph {"));
        assert!(!dot.is_empty());
    }

    /// Test with custom configuration
    #[test]
    fn test_to_dot_with_config() {
        let bdd = Bdd::default();
        let x = bdd.mk_var(1);

        let config = DotConfig {
            use_html_labels: false,
            ..DotConfig::default()
        };

        // Should use custom config without errors
        let dot = bdd.to_dot_with_config(&[x], &config).unwrap();
        assert!(dot.starts_with("graph {"));
        assert!(!dot.is_empty());
    }

    /// Helper test to write DOT file for manual inspection (disabled by default)
    #[test]
    #[ignore]
    fn test_write_dot_file() {
        let bdd = Bdd::default();
        let x1 = bdd.mk_var(1);
        let x2 = bdd.mk_var(2);
        let f = bdd.apply_and(x1, x2);

        let dot = bdd.to_dot(&[f]).unwrap();

        std::fs::write("test_output.dot", &dot).unwrap();
        println!("DOT output:\n{}", dot);

        // Optionally render to image formats
        for format in ["png", "pdf", "svg"] {
            let output = std::process::Command::new("dot")
                .arg(format!("-T{}", format))
                .arg("test_output.dot")
                .arg("-o")
                .arg(format!("test_output.{}", format))
                .output();

            if let Ok(output) = output {
                if output.status.success() {
                    println!("Generated test_output.{}", format);
                }
            }
        }
    }
}
