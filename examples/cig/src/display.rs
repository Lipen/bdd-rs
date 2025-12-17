//! Display utilities for CIG.

use crate::cig::{Cig, CigNode, CigNodeKind};

/// Display a CIG as a tree with Unicode box-drawing characters.
pub fn display_tree(cig: &Cig) -> String {
    let mut output = String::new();
    output.push_str("CIG Structure:\n");
    display_node(&mut output, cig.root(), "", true);
    output
}

fn display_node(output: &mut String, node: &CigNode, prefix: &str, is_last: bool) {
    let connector = if prefix.is_empty() {
        ""
    } else if is_last {
        "└── "
    } else {
        "├── "
    };

    let label = match &node.kind {
        CigNodeKind::Constant(v) => if *v { "⊤ (true)" } else { "⊥ (false)" }.to_string(),
        CigNodeKind::Leaf(v) => format!("{}", v),
        CigNodeKind::Internal { interaction, .. } => format!("{}", interaction),
    };

    output.push_str(&format!("{}{}{}\n", prefix, connector, label));

    if let CigNodeKind::Internal { children, .. } = &node.kind {
        let child_prefix = if prefix.is_empty() {
            "".to_string()
        } else if is_last {
            format!("{}    ", prefix)
        } else {
            format!("{}│   ", prefix)
        };

        for (i, child) in children.iter().enumerate() {
            let is_last_child = i == children.len() - 1;
            display_node(output, child, &child_prefix, is_last_child);
        }
    }
}

/// Display the interaction structure as a compact notation.
pub fn compact_notation(cig: &Cig) -> String {
    node_to_string(cig.root())
}

fn node_to_string(node: &CigNode) -> String {
    match &node.kind {
        CigNodeKind::Constant(v) => if *v { "1" } else { "0" }.to_string(),
        CigNodeKind::Leaf(v) => format!("x{}", v.index()),
        CigNodeKind::Internal { interaction, children } => {
            let child_strs: Vec<String> = children.iter().map(|c| node_to_string(c)).collect();

            // Try to use infix notation for binary operators
            if children.len() == 2 {
                if let Some(op) = interaction.as_binary_operator() {
                    return format!("({} {} {})", child_strs[0], op.symbol(), child_strs[1]);
                }
            }

            // Prefix notation for general case
            format!("{}({})", interaction, child_strs.join(", "))
        }
    }
}

/// Generate a DOT graph representation for visualization.
pub fn to_dot(cig: &Cig) -> String {
    let mut output = String::new();
    output.push_str("digraph CIG {\n");
    output.push_str("  rankdir=TB;\n");
    output.push_str("  node [fontname=\"Helvetica\"];\n\n");

    let mut node_id = 0;
    let mut ids = std::collections::HashMap::new();
    generate_dot_nodes(&mut output, cig.root(), &mut node_id, &mut ids);
    generate_dot_edges(&mut output, cig.root(), &ids);

    output.push_str("}\n");
    output
}

fn generate_dot_nodes(output: &mut String, node: &CigNode, next_id: &mut usize, ids: &mut std::collections::HashMap<u64, usize>) {
    let hash = node.canonical_hash();
    if ids.contains_key(&hash) {
        return;
    }

    let id = *next_id;
    *next_id += 1;
    ids.insert(hash, id);

    let (label, shape, style) = match &node.kind {
        CigNodeKind::Constant(v) => {
            let l = if *v { "⊤" } else { "⊥" };
            (l.to_string(), "square", "filled")
        }
        CigNodeKind::Leaf(v) => (format!("{}", v), "circle", "filled"),
        CigNodeKind::Internal { interaction, children } => {
            for child in children {
                generate_dot_nodes(output, child, next_id, ids);
            }
            (format!("{}", interaction), "ellipse", "")
        }
    };

    let style_attr = if style.is_empty() {
        "".to_string()
    } else {
        format!(", style={}", style)
    };

    output.push_str(&format!("  n{} [label=\"{}\", shape={}{}];\n", id, label, shape, style_attr));
}

fn generate_dot_edges(output: &mut String, node: &CigNode, ids: &std::collections::HashMap<u64, usize>) {
    let parent_id = ids.get(&node.canonical_hash()).unwrap();

    if let CigNodeKind::Internal { children, .. } = &node.kind {
        for (i, child) in children.iter().enumerate() {
            let child_id = ids.get(&child.canonical_hash()).unwrap();
            output.push_str(&format!("  n{} -> n{} [label=\"{}\"];\n", parent_id, child_id, i + 1));
            generate_dot_edges(output, child, ids);
        }
    }
}

/// A simple ASCII art representation.
pub fn ascii_diagram(cig: &Cig) -> String {
    let mut output = String::new();

    fn draw(output: &mut String, node: &CigNode, indent: usize) {
        let prefix = "  ".repeat(indent);
        match &node.kind {
            CigNodeKind::Constant(v) => {
                output.push_str(&format!("{}[{}]\n", prefix, if *v { "T" } else { "F" }));
            }
            CigNodeKind::Leaf(v) => {
                output.push_str(&format!("{}[{}]\n", prefix, v));
            }
            CigNodeKind::Internal { interaction, children } => {
                output.push_str(&format!("{}[{}]\n", prefix, interaction));
                for child in children {
                    draw(output, child, indent + 1);
                }
            }
        }
    }

    draw(&mut output, cig.root(), 0);
    output
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::builder::CigBuilder;
    use crate::truth_table::TruthTable;

    #[test]
    fn test_display_tree() {
        let mut builder = CigBuilder::new();
        let f = TruthTable::from_expr(3, |x| (x[0] ^ x[1]) && x[2]);
        let cig = builder.build(&f);

        let tree = display_tree(&cig);
        println!("{}", tree);
        assert!(tree.contains("CIG Structure:"));
    }

    #[test]
    fn test_compact_notation() {
        let mut builder = CigBuilder::new();
        let f = TruthTable::from_expr(2, |x| x[0] && x[1]);
        let cig = builder.build(&f);

        let notation = compact_notation(&cig);
        println!("Compact: {}", notation);
    }

    #[test]
    fn test_dot_output() {
        let mut builder = CigBuilder::new();
        let f = TruthTable::from_expr(3, |x| (x[0] || x[1]) && x[2]);
        let cig = builder.build(&f);

        let dot = to_dot(&cig);
        assert!(dot.contains("digraph CIG"));
        assert!(dot.contains("->"));
    }
}
