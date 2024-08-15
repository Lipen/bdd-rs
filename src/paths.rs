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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_all_paths_1() {
        let bdd = Bdd::default();

        let f = bdd.cube([1, -2, 3]);
        println!("f = {} of size {}", f, bdd.size(f));
        let paths = bdd.paths(f).collect::<Vec<_>>();
        println!("paths: {}", paths.len());
        for path in paths.iter() {
            println!("path = {:?}", path);
        }
        assert_eq!(paths.len(), 1);
        assert_eq!(paths[0], vec![1, -2, 3]);
    }

    #[test]
    fn test_all_paths_2() {
        let bdd = Bdd::default();

        let c1 = bdd.cube([1, -2, 3]);
        let c2 = bdd.cube([1, 2, -3]);
        let f = bdd.apply_or(c1, c2);
        println!("f = {} of size {}", f, bdd.size(f));
        let paths = bdd.paths(f).collect::<Vec<_>>();
        println!("paths: {}", paths.len());
        for path in paths.iter() {
            println!("path = {:?}", path);
        }
        assert_eq!(paths.len(), 2);
        assert!(paths.contains(&vec![1, -2, 3]));
        assert!(paths.contains(&vec![1, 2, -3]));
    }

    #[test]
    fn test_all_paths_one() {
        let bdd = Bdd::default();

        let f = bdd.one;
        println!("f = {} of size {}", f, bdd.size(f));
        let paths = bdd.paths(f).collect::<Vec<_>>();
        println!("paths: {}", paths.len());
        for path in paths.iter() {
            println!("path = {:?}", path);
        }
        assert_eq!(paths.len(), 1);
        assert_eq!(paths[0], vec![]);
    }

    #[test]
    fn test_all_paths_zero() {
        let bdd = Bdd::default();

        let f = bdd.zero;
        println!("f = {} of size {}", f, bdd.size(f));
        let paths = bdd.paths(f).collect::<Vec<_>>();
        println!("paths: {}", paths.len());
        for path in paths.iter() {
            println!("path = {:?}", path);
        }
        assert_eq!(paths.len(), 0);
    }

    #[test]
    fn test_all_paths_to_zero() {
        let bdd = Bdd::default();

        let f = bdd.cube([-1, -2, -3]);
        println!("f = {} of size {}", bdd.to_bracket_string(f), bdd.size(f));
        println!("~f = {} of size {}", bdd.to_bracket_string(-f), bdd.size(-f));
        let paths = bdd.paths(-f).collect::<Vec<_>>();
        println!("paths to one for {}: {}", -f, paths.len());
        for path in paths.iter() {
            println!("path = {:?}", path);
        }

        let paths = bdd.paths(f).collect::<Vec<_>>();
        println!("paths to one for {}: {}", f, paths.len());
        for path in paths.iter() {
            println!("path = {:?}", path);
        }
    }
}
