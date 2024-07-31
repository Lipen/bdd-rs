use crate::bdd::Bdd;
use crate::reference::Ref;

impl Bdd {
    pub fn paths(&self, f: Ref) -> BddPaths {
        BddPaths::new(self, f)
    }
}

pub struct BddPaths<'a> {
    bdd: &'a Bdd,
    stack: Vec<(Ref, Vec<i32>)>,
}

impl<'a> BddPaths<'a> {
    pub fn new(bdd: &'a Bdd, f: Ref) -> Self {
        let stack = vec![(f, vec![])];
        BddPaths { bdd, stack }
    }
}

impl Iterator for BddPaths<'_> {
    type Item = Vec<i32>;

    fn next(&mut self) -> Option<Self::Item> {
        while let Some((node, path)) = self.stack.pop() {
            if self.bdd.is_zero(node) {
                continue;
            } else if self.bdd.is_one(node) {
                return Some(path);
            } else {
                assert!(!self.bdd.is_terminal(node));
                let v = self.bdd.variable(node.index()) as i32;

                let mut path_high = path.clone();
                path_high.push(v);
                self.stack.push((self.bdd.high_node(node), path_high));

                let mut path_low = path;
                path_low.push(-v);
                self.stack.push((self.bdd.low_node(node), path_low));
            }
        }
        None
    }
}
