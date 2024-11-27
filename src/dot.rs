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

            let high = self.high(id);
            assert!(!high.is_negated());
            writeln!(dot, "{} -- {};", id, high.index())?;

            let low = self.low(id);
            if low.is_negated() {
                if low.index() == 1 {
                    assert_eq!(low, self.zero);
                    writeln!(dot, "{} -- 0 [style=dashed];", id)?;
                } else {
                    writeln!(dot, "{} -- {} [style=dotted, dir=forward, arrowhead=odot];", id, low.index())?;
                }
            } else {
                writeln!(dot, "{} -- {} [style=dashed];", id, low.index())?;
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
                    writeln!(dot, "r{} -- 0;", i)?;
                } else {
                    writeln!(dot, "r{} -- {} [dir=forward, arrowhead=odot];", i, root.index())?;
                }
            } else {
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

    //noinspection RsConstantConditionIf
    #[test]
    fn test_to_dot() {
        let bdd = Bdd::default();

        let f = bdd.cube([-1, 2, 3]);
        println!("f = {}", bdd.to_bracket_string(f));

        let dot = bdd.to_dot(&[f, bdd.zero, bdd.one]).unwrap();
        println!("DOT for f:");
        print!("{}", dot);

        if false {
            std::fs::write("bdd.dot", dot).unwrap();
            for format in ["png", "pdf"] {
                std::process::Command::new("dot")
                    .arg(format!("-T{}", format))
                    .arg("-O")
                    .arg("bdd.dot")
                    .status()
                    .unwrap();
            }
        }
    }
}
