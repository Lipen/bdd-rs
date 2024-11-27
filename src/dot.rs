use std::collections::BTreeMap;

use crate::bdd::Bdd;
use crate::reference::Ref;

impl Bdd {
    pub fn to_dot(&self, roots: &[Ref]) -> Result<String, std::fmt::Error> {
        use std::fmt::Write as _;

        let mut dot = String::new();
        writeln!(dot, "graph {{")?;
        writeln!(dot, "node [shape=circle, fixedsize=true];")?;

        // Terminal
        writeln!(dot, "{{ rank=sink")?;
        writeln!(dot, "0 [shape=square, label=\"0\"];")?;
        writeln!(dot, "1 [shape=square, label=\"1\"];")?;
        writeln!(dot, "}}")?;

        // Get all nodes
        let all_nodes = self.descendants(roots.iter().copied());

        // // Nodes
        // for &id in all_nodes.iter() {
        //     if id == 0 {
        //         continue;
        //     }
        //     let label = format!("\\N:v{}", self.variable(id));
        //     writeln!(dot, "{} [label=\"{}\"];", id, label)?;
        // }

        // Nodes per level
        let mut levels = BTreeMap::<usize, Vec<u32>>::new();
        for &id in all_nodes.iter() {
            if id == 1 {
                continue;
            }
            let level = self.variable(id) as usize;
            levels.entry(level).or_default().push(id);
        }
        for level in levels.values() {
            writeln!(dot, "{{ rank=same")?;
            for &id in level.iter() {
                // let label = format!("\"\\N:v{}\"", self.variable(id));
                // let label = format!("v{}", self.variable(id));
                let label = format!("<x<SUB>{}</SUB>>", self.variable(id));
                writeln!(dot, "{} [label={}];", id, label)?;
            }
            writeln!(dot, "}}")?;
        }

        // Edges
        for &id in all_nodes.iter() {
            if id == 1 {
                continue;
            }

            // Note: use " " (space) label to avoid an overlap with "-1" label

            let high = self.high(id);
            assert!(!high.is_negated());
            writeln!(dot, "{} -- {} [label=\" \"];", id, high.index())?;

            let low = self.low(id);
            if low.is_negated() {
                if low.index() == 1 {
                    writeln!(dot, "{} -- 0 [label=\" \", style=dashed];", id)?;
                } else {
                    writeln!(dot, "{} -- {} [label=\"-1\", style=dotted];", id, low.index())?;
                }
            } else {
                writeln!(dot, "{} -- {} [label=\" \", style=dashed];", id, low.index())?;
            }
        }

        // Roots
        writeln!(dot, "{{ rank=source")?;
        for (i, root) in roots.iter().enumerate() {
            writeln!(dot, "r{} [shape=rect, label=\"{}\"];", i, root)?;
        }
        writeln!(dot, "}}")?;

        // Root edges
        for (i, &root) in roots.iter().enumerate() {
            if root.is_negated() {
                if root.index() == 1 {
                    writeln!(dot, "r{} -- 0 [style=dashed];", i)?;
                } else {
                    writeln!(dot, "r{} -- {} [style=dashed];", i, root.index())?;
                }
            } else {
                writeln!(dot, "r{} -- {};", i, root.index())?;
            }
        }

        writeln!(dot, "}}")?;
        Ok(dot)
    }
}
