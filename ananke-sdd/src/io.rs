//! File I/O for SDDs and Vtrees.
//!
//! Implements reading and writing of SDD and Vtree files in the libsdd format.
//!
//! # Vtree File Format (.vtree)
//!
//! ```text
//! vtree <node_count>
//! L <id> <var>           # leaf node with variable
//! I <id> <left> <right>  # internal node with children
//! ```
//!
//! Nodes appear bottom-up (children before parents).
//! IDs are in-order positions (0-indexed).
//!
//! # SDD File Format (.sdd)
//!
//! ```text
//! sdd <node_count>
//! F <id>                          # false node
//! T <id>                          # true node
//! L <id> <vtree_id> <literal>     # literal node
//! D <id> <vtree_id> <size> {<prime> <sub>}*  # decision node
//! ```
//!
//! Nodes appear bottom-up (children before parents).

use std::collections::HashMap;
use std::fmt::Write as FmtWrite;
use std::fs;
use std::io;
use std::path::Path;

use crate::manager::SddManager;
use crate::sdd::{Sdd, SddId};
use crate::vtree::{Vtree, VtreeId, VtreeNode};

/// Error type for I/O operations.
#[derive(Debug)]
pub enum IoError {
    /// File I/O error.
    Io(io::Error),
    /// Parse error with message.
    Parse(String),
}

impl From<io::Error> for IoError {
    fn from(e: io::Error) -> Self {
        IoError::Io(e)
    }
}

impl std::fmt::Display for IoError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            IoError::Io(e) => write!(f, "I/O error: {}", e),
            IoError::Parse(msg) => write!(f, "Parse error: {}", msg),
        }
    }
}

impl std::error::Error for IoError {}

// ─── Vtree I/O ───

impl Vtree {
    /// Saves the vtree to a file in libsdd format.
    ///
    /// # Example
    ///
    /// ```no_run
    /// use ananke_sdd::vtree::Vtree;
    ///
    /// let vtree = Vtree::balanced(4);
    /// vtree.save("output.vtree").unwrap();
    /// ```
    pub fn save<P: AsRef<Path>>(&self, path: P) -> Result<(), IoError> {
        let content = self.to_vtree_string();
        fs::write(path, content)?;
        Ok(())
    }

    /// Converts the vtree to libsdd format string.
    pub fn to_vtree_string(&self) -> String {
        let mut output = String::new();

        // Header
        writeln!(output, "c ids of vtree nodes start at 0").unwrap();
        writeln!(output, "c ids of variables start at 1").unwrap();
        writeln!(output, "c vtree nodes appear bottom-up, children before parents").unwrap();
        writeln!(output, "c").unwrap();
        writeln!(output, "c file syntax:").unwrap();
        writeln!(output, "c vtree number-of-nodes-in-vtree").unwrap();
        writeln!(output, "c L id-of-leaf-vtree-node id-of-variable").unwrap();
        writeln!(output, "c I id-of-internal-vtree-node id-of-left-child id-of-right-child").unwrap();
        writeln!(output, "c").unwrap();

        // Node count
        writeln!(output, "vtree {}", self.num_nodes()).unwrap();

        // Print nodes in post-order (children before parents)
        self.write_vtree_node(self.root(), &mut output);

        output
    }

    fn write_vtree_node(&self, id: VtreeId, output: &mut String) {
        match self.node(id) {
            VtreeNode::Leaf { var } => {
                writeln!(output, "L {} {}", self.position(id), var).unwrap();
            }
            VtreeNode::Internal { left, right } => {
                self.write_vtree_node(*left, output);
                self.write_vtree_node(*right, output);
                writeln!(output, "I {} {} {}", self.position(id), self.position(*left), self.position(*right)).unwrap();
            }
        }
    }

    /// Reads a vtree from a file in libsdd format.
    ///
    /// # Example
    ///
    /// ```no_run
    /// use ananke_sdd::vtree::Vtree;
    ///
    /// let vtree = Vtree::load("input.vtree").unwrap();
    /// ```
    pub fn load<P: AsRef<Path>>(path: P) -> Result<Self, IoError> {
        let content = fs::read_to_string(path)?;
        Self::from_vtree_string(&content)
    }

    /// Parses a vtree from libsdd format string.
    pub fn from_vtree_string(content: &str) -> Result<Self, IoError> {
        let mut lines = content.lines().filter(|line| !line.starts_with('c') && !line.is_empty());

        // Parse header
        let header = lines.next().ok_or_else(|| IoError::Parse("Missing header".into()))?;
        let parts: Vec<&str> = header.split_whitespace().collect();
        if parts.len() != 2 || parts[0] != "vtree" {
            return Err(IoError::Parse(format!("Invalid header: {}", header)));
        }
        let node_count: usize = parts[1].parse().map_err(|_| IoError::Parse("Invalid node count".into()))?;

        // Parse nodes
        let mut nodes: Vec<VtreeNode> = Vec::with_capacity(node_count);
        let mut parents: Vec<Option<VtreeId>> = Vec::with_capacity(node_count);
        let mut var_to_vtree: HashMap<u32, VtreeId> = HashMap::new();
        let mut pos_to_idx: HashMap<u32, VtreeId> = HashMap::new();
        let mut num_vars = 0u32;
        let mut root = VtreeId::new(0);

        for line in lines {
            let parts: Vec<&str> = line.split_whitespace().collect();
            if parts.is_empty() {
                continue;
            }

            let node_type = parts[0];
            let pos: u32 = parts[1]
                .parse()
                .map_err(|_| IoError::Parse(format!("Invalid position in: {}", line)))?;

            let idx = VtreeId::new(nodes.len() as u32);
            pos_to_idx.insert(pos, idx);

            match node_type {
                "L" => {
                    let var: u32 = parts[2]
                        .parse()
                        .map_err(|_| IoError::Parse(format!("Invalid variable in: {}", line)))?;
                    nodes.push(VtreeNode::Leaf { var });
                    parents.push(None);
                    var_to_vtree.insert(var, idx);
                    num_vars = num_vars.max(var);
                }
                "I" => {
                    let left_pos: u32 = parts[2]
                        .parse()
                        .map_err(|_| IoError::Parse(format!("Invalid left child in: {}", line)))?;
                    let right_pos: u32 = parts[3]
                        .parse()
                        .map_err(|_| IoError::Parse(format!("Invalid right child in: {}", line)))?;

                    let left = *pos_to_idx
                        .get(&left_pos)
                        .ok_or_else(|| IoError::Parse(format!("Unknown left child: {}", left_pos)))?;
                    let right = *pos_to_idx
                        .get(&right_pos)
                        .ok_or_else(|| IoError::Parse(format!("Unknown right child: {}", right_pos)))?;

                    nodes.push(VtreeNode::Internal { left, right });
                    parents.push(None);
                    parents[left.index()] = Some(idx);
                    parents[right.index()] = Some(idx);
                }
                _ => return Err(IoError::Parse(format!("Unknown node type: {}", node_type))),
            }

            root = idx; // Last node is root
        }

        // Build var_to_vtree vector
        let mut var_to_vtree_vec = vec![VtreeId::new(0); (num_vars + 1) as usize];
        for (var, id) in var_to_vtree {
            var_to_vtree_vec[var as usize] = id;
        }

        // Create vtree using the from_parts constructor
        let vtree = Vtree::from_parts(nodes, parents, root, num_vars, var_to_vtree_vec);

        Ok(vtree)
    }
}

// ─── SDD I/O ───

impl SddManager {
    /// Saves an SDD to a file in libsdd format.
    ///
    /// # Example
    ///
    /// ```no_run
    /// use ananke_sdd::SddManager;
    ///
    /// let mgr = SddManager::new(4);
    /// let f = mgr.and(mgr.var(1), mgr.var(2));
    /// mgr.save_sdd(f, "output.sdd").unwrap();
    /// ```
    pub fn save_sdd<P: AsRef<Path>>(&self, f: SddId, path: P) -> Result<(), IoError> {
        let content = self.sdd_to_string(f);
        fs::write(path, content)?;
        Ok(())
    }

    /// Converts an SDD to libsdd format string.
    pub fn sdd_to_string(&self, f: SddId) -> String {
        let mut output = String::new();
        let mut visited: HashMap<SddId, u32> = HashMap::new();
        let mut node_lines: Vec<String> = Vec::new();
        let mut next_id = 0u32;

        // Header
        writeln!(output, "c ids of sdd nodes start at 0").unwrap();
        writeln!(output, "c sdd nodes appear bottom-up, children before parents").unwrap();
        writeln!(output, "c").unwrap();
        writeln!(output, "c file syntax:").unwrap();
        writeln!(output, "c sdd count-of-sdd-nodes").unwrap();
        writeln!(output, "c F id-of-false-sdd-node").unwrap();
        writeln!(output, "c T id-of-true-sdd-node").unwrap();
        writeln!(output, "c L id-of-literal-sdd-node id-of-vtree literal").unwrap();
        writeln!(
            output,
            "c D id-of-decomposition-sdd-node id-of-vtree number-of-elements {{id-of-prime id-of-sub}}*"
        )
        .unwrap();
        writeln!(output, "c").unwrap();

        // Collect nodes in post-order
        self.collect_sdd_nodes(f, &mut visited, &mut node_lines, &mut next_id);

        // Write count and nodes
        writeln!(output, "sdd {}", node_lines.len()).unwrap();
        for line in node_lines {
            output.push_str(&line);
        }

        output
    }

    fn collect_sdd_nodes(&self, f: SddId, visited: &mut HashMap<SddId, u32>, node_lines: &mut Vec<String>, next_id: &mut u32) -> u32 {
        if let Some(&id) = visited.get(&f) {
            return id;
        }

        // For decision nodes, first collect children
        if !f.is_constant() {
            let node = self.node(f);
            if let Sdd::Decision { elements, .. } = &node {
                for elem in elements {
                    self.collect_sdd_nodes(elem.prime, visited, node_lines, next_id);
                    self.collect_sdd_nodes(elem.sub, visited, node_lines, next_id);
                }
            }
        }

        // Now assign ID and write this node
        let id = *next_id;
        *next_id += 1;
        visited.insert(f, id);

        let line = if f.is_false() {
            format!("F {}\n", id)
        } else if f.is_true() {
            format!("T {}\n", id)
        } else {
            let node = self.node(f);
            match &node {
                Sdd::Literal(lit) => {
                    let vtree_id = self.vtree().var_vtree(lit.var());
                    let lit_val: i32 = if lit.is_positive() { lit.var() as i32 } else { -(lit.var() as i32) };
                    format!("L {} {} {}\n", id, self.vtree().position(vtree_id), lit_val)
                }
                Sdd::Decision { vtree, elements } => {
                    let mut line = format!("D {} {} {}", id, self.vtree().position(*vtree), elements.len());
                    for elem in elements {
                        let prime_id = visited.get(&elem.prime).unwrap();
                        let sub_id = visited.get(&elem.sub).unwrap();
                        write!(line, " {} {}", prime_id, sub_id).unwrap();
                    }
                    line.push('\n');
                    line
                }
                _ => String::new(),
            }
        };

        node_lines.push(line);
        id
    }

    /// Loads an SDD from a file in libsdd format.
    ///
    /// Note: The manager must have been created with a compatible vtree.
    pub fn load_sdd<P: AsRef<Path>>(&self, path: P) -> Result<SddId, IoError> {
        let content = fs::read_to_string(path)?;
        self.sdd_from_string(&content)
    }

    /// Parses an SDD from libsdd format string.
    pub fn sdd_from_string(&self, content: &str) -> Result<SddId, IoError> {
        let mut lines = content.lines().filter(|line| !line.starts_with('c') && !line.is_empty());

        // Parse header
        let header = lines.next().ok_or_else(|| IoError::Parse("Missing header".into()))?;
        let parts: Vec<&str> = header.split_whitespace().collect();
        if parts.len() != 2 || parts[0] != "sdd" {
            return Err(IoError::Parse(format!("Invalid header: {}", header)));
        }
        // Parse node count (not used, but validate it)
        let _node_count: usize = parts[1].parse().map_err(|_| IoError::Parse("Invalid node count".into()))?;

        let mut id_to_sdd: HashMap<u32, SddId> = HashMap::new();
        let mut root = SddId::FALSE;

        for line in lines {
            let parts: Vec<&str> = line.split_whitespace().collect();
            if parts.is_empty() {
                continue;
            }

            let node_type = parts[0];
            let id: u32 = parts[1].parse().map_err(|_| IoError::Parse(format!("Invalid id in: {}", line)))?;

            let sdd_id = match node_type {
                "F" => SddId::FALSE,
                "T" => SddId::TRUE,
                "L" => {
                    // L id vtree_pos literal
                    let literal: i32 = parts[3]
                        .parse()
                        .map_err(|_| IoError::Parse(format!("Invalid literal in: {}", line)))?;
                    if literal > 0 {
                        self.var(literal as u32)
                    } else {
                        self.neg(self.var((-literal) as u32))
                    }
                }
                "D" => {
                    // D id vtree_pos size {prime sub}*
                    let size: usize = parts[3].parse().map_err(|_| IoError::Parse(format!("Invalid size in: {}", line)))?;

                    // Parse elements
                    let mut result = SddId::FALSE;
                    for i in 0..size {
                        let prime_id: u32 = parts[4 + i * 2]
                            .parse()
                            .map_err(|_| IoError::Parse(format!("Invalid prime id in: {}", line)))?;
                        let sub_id: u32 = parts[5 + i * 2]
                            .parse()
                            .map_err(|_| IoError::Parse(format!("Invalid sub id in: {}", line)))?;

                        let prime = *id_to_sdd
                            .get(&prime_id)
                            .ok_or_else(|| IoError::Parse(format!("Unknown prime: {}", prime_id)))?;
                        let sub = *id_to_sdd
                            .get(&sub_id)
                            .ok_or_else(|| IoError::Parse(format!("Unknown sub: {}", sub_id)))?;

                        // Build element: prime ∧ sub
                        let elem = self.and(prime, sub);
                        // Add to result
                        result = self.or(result, elem);
                    }
                    result
                }
                _ => return Err(IoError::Parse(format!("Unknown node type: {}", node_type))),
            };

            id_to_sdd.insert(id, sdd_id);
            root = sdd_id;
        }

        Ok(root)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_vtree_roundtrip() {
        let vtree = Vtree::balanced(4);
        let s = vtree.to_vtree_string();
        let vtree2 = Vtree::from_vtree_string(&s).unwrap();

        assert_eq!(vtree.num_vars(), vtree2.num_vars());
        assert_eq!(vtree.num_nodes(), vtree2.num_nodes());
    }

    #[test]
    fn test_sdd_roundtrip() {
        let mgr = SddManager::new(3);
        let x1 = mgr.var(1);
        let x2 = mgr.var(2);
        let f = mgr.and(x1, x2);

        let s = mgr.sdd_to_string(f);
        let f2 = mgr.sdd_from_string(&s).unwrap();

        // Same model count
        assert_eq!(mgr.model_count(f), mgr.model_count(f2));
    }
}
