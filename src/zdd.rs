use std::cell::RefCell;
use std::cmp::min;
use std::collections::{HashMap, HashSet};

use log::debug;

use crate::cache::Cache;
use crate::node::Node;
use crate::reference::Ref;
use crate::storage::Storage;
use crate::utils::OpKey;

pub struct Zdd {
    storage: RefCell<Storage>,
    cache: RefCell<Cache<OpKey, Ref>>,
    count_cache: RefCell<HashMap<Ref, u64>>,
    // terminal: Ref, // Zero
    zero: Ref,
    one: Ref,
}

impl Zdd {
    pub fn new(storage_bits: usize) -> Self {
        let mut storage = Storage::new(storage_bits);

        // let terminal = storage.alloc();
        // assert_eq!(terminal, 1); // Make sure the terminal node is (1).
        // let terminal = Ref::positive(terminal as u32);

        let zero = storage.alloc();
        let zero = Ref::positive(zero as u32);
        let one = storage.alloc();
        let one = Ref::positive(one as u32);

        Self {
            storage: RefCell::new(storage),
            cache: RefCell::new(Cache::new(min(storage_bits, 16))),
            count_cache: RefCell::new(HashMap::new()),
            // terminal,
            zero,
            one,
        }
    }
}

impl Default for Zdd {
    fn default() -> Self {
        Self::new(20)
    }
}

// List of basic operations over ZDD:
//   Here, P and Q are sets of combinations.
//   0 -- `empty` creates an empty ZDD.
//   1 -- the set of only the null combination (00...0) (1-terminal node).
//   P.top -- the variable at the root of the ZDD.
//   P.offset(v) -- selects the subset of the combinations each of which does not include the variable v.
//   P.onset(v) -- selects the subset of the combinations including v, and then delete v from each combination.
//   P.change(v) -- invert the presence of v in each combination.
//   P.union(Q) -- the union of the sets P and Q.
//   P.intersect(Q) -- the intersection of the sets P and Q.
//   P.diff(Q) -- the difference of the sets P and Q.
//   P.count -- the number of combinations in the set P.

impl Zdd {
    pub fn storage(&self) -> std::cell::Ref<'_, Storage> {
        self.storage.borrow()
    }
    fn storage_mut(&self) -> std::cell::RefMut<'_, Storage> {
        self.storage.borrow_mut()
    }

    pub fn cache(&self) -> std::cell::Ref<'_, Cache<OpKey, Ref>> {
        self.cache.borrow()
    }
    fn cache_mut(&self) -> std::cell::RefMut<'_, Cache<OpKey, Ref>> {
        self.cache.borrow_mut()
    }

    pub fn node(&self, index: u32) -> Node {
        *self.storage().node(index as usize)
    }
    pub fn variable(&self, index: u32) -> u32 {
        self.storage().variable(index as usize)
    }
    pub fn low(&self, index: u32) -> Ref {
        self.storage().low(index as usize)
    }
    pub fn high(&self, index: u32) -> Ref {
        self.storage().high(index as usize)
    }
    pub(crate) fn next(&self, index: u32) -> usize {
        self.storage().next(index as usize)
    }
}

impl Zdd {
    pub fn zero(&self) -> Ref {
        // self.terminal
        self.zero
    }
    pub fn one(&self) -> Ref {
        // -self.zero()
        self.one
    }

    pub fn is_zero(&self, node: Ref) -> bool {
        node == self.zero()
    }
    pub fn is_one(&self, node: Ref) -> bool {
        node == self.one()
    }
    pub fn is_terminal(&self, node: Ref) -> bool {
        self.is_zero(node) || self.is_one(node)
    }
}

impl Zdd {
    pub fn mk_node(&self, var: u32, low: Ref, high: Ref) -> Ref {
        assert_ne!(var, 0, "Variable index should not be zero");

        assert!(!low.is_negated());
        assert!(!high.is_negated());

        // debug!("mk_node({}, {}, {})", var, low, high);

        // Zero-suppression
        if self.is_zero(high) {
            return low;
        }

        // if low.is_negated() {
        //     return -self.mk_node(var, -low, high);
        // }
        // assert!(!low.is_negated());

        let i = self.storage_mut().put(Node { variable: var, low, high });
        Ref::positive(i as u32)
    }
}

impl Zdd {
    pub fn offset(&self, node: Ref, var: u32) -> Ref {
        debug!("offset({}, {})", node, var);

        let index = node.index();
        let top = self.variable(index);
        if top == var {
            return self.low(index);
        }
        if top > var {
            return node;
        }

        let key = OpKey::Offset(node, var);
        if let Some(&res) = self.cache().get(&key) {
            return res;
        }

        assert!(top < var);
        let low = self.offset(self.low(index), var);
        let high = self.offset(self.high(index), var);
        let res = self.mk_node(top, low, high);

        self.cache_mut().insert(key, res);
        res
    }

    pub fn onset(&self, node: Ref, var: u32) -> Ref {
        debug!("onset({}, {})", node, var);

        let index = node.index();
        let top = self.variable(index);
        if top == var {
            return self.high(index);
        }
        if top > var {
            return self.zero();
        }

        let key = OpKey::Onset(node, var);
        if let Some(&res) = self.cache().get(&key) {
            return res;
        }

        assert!(top < var);
        let low = self.onset(self.low(index), var);
        let high = self.onset(self.high(index), var);
        let res = self.mk_node(top, low, high);

        self.cache_mut().insert(key, res);
        res
    }

    pub fn change(&self, node: Ref, var: u32) -> Ref {
        debug!("change({}, {})", node, var);

        let index = node.index();
        let top = self.variable(index);
        if top == var {
            return self.mk_node(var, self.high(index), self.low(index));
        }
        if top > var {
            return self.mk_node(var, self.zero(), node);
        }

        let key = OpKey::Change(node, var);
        if let Some(&res) = self.cache().get(&key) {
            return res;
        }

        assert!(top < var);
        let low = self.change(self.low(index), var);
        let high = self.change(self.high(index), var);
        let res = self.mk_node(top, low, high);

        self.cache_mut().insert(key, res);
        res
    }

    pub fn union(&self, f: Ref, g: Ref) -> Ref {
        debug!("union({}, {})", f, g);
        // debug!("union({} = {}, {} = {})", f, self.to_bracket_string(f), g, self.to_bracket_string(g));

        if self.is_zero(f) {
            return g;
        }
        if self.is_zero(g) || f == g {
            return f;
        }

        if self.is_one(f) {
            assert!(!self.is_terminal(g));
            let var = self.variable(g.index());
            let low = self.union(self.one(), self.low(g.index()));
            let high = self.union(self.one(), self.high(g.index()));
            return self.mk_node(var, low, high);
        }

        if self.is_one(g) {
            assert!(!self.is_terminal(f));
            let var = self.variable(f.index());
            let low = self.union(self.low(f.index()), self.one());
            let high = self.union(self.high(f.index()), self.one());
            return self.mk_node(var, low, high);
        }

        assert!(!self.is_terminal(f));
        assert!(!self.is_terminal(g));

        // if f.is_negated() && g.is_negated() {
        //     return -self.union(-f, -g);
        // }
        // if f.is_negated() {
        //     return -self.union(-f, g);
        // }
        // if g.is_negated() {
        //     return -self.union(f, -g);
        // }

        debug!("pre-cache");

        let key = OpKey::Union(f, g);
        if let Some(&res) = self.cache().get(&key) {
            assert!(!res.is_negated());
            return res;
        }

        debug!("computing...");

        let i = self.variable(f.index());
        let j = self.variable(g.index());
        let res = if i < j {
            let low = self.union(self.low(f.index()), g);
            let high = self.high(f.index());
            self.mk_node(i, low, high)
        } else if i > j {
            let low = self.union(f, self.low(g.index()));
            let high = self.high(g.index());
            self.mk_node(j, low, high)
        } else {
            assert_eq!(i, j);
            let low = self.union(self.low(f.index()), self.low(g.index()));
            let high = self.union(self.high(f.index()), self.high(g.index()));
            self.mk_node(i, low, high)
        };

        self.cache_mut().insert(key, res);
        res
    }

    pub fn intersect(&self, f: Ref, g: Ref) -> Ref {
        debug!("intersect({}, {})", f, g);

        if self.is_zero(f) || self.is_zero(g) {
            return self.zero();
        }
        if f == g {
            return f;
        }

        let key = OpKey::Intersect(f, g);
        if let Some(&res) = self.cache().get(&key) {
            assert!(!res.is_negated());
            return res;
        }

        let i = self.variable(f.index());
        let j = self.variable(g.index());
        let res = if i < j {
            self.intersect(self.low(f.index()), g)
        } else if i > j {
            self.intersect(f, self.low(g.index()))
        } else {
            assert_eq!(i, j);
            let low = self.intersect(self.low(f.index()), self.low(g.index()));
            let high = self.intersect(self.high(f.index()), self.high(g.index()));
            self.mk_node(i, low, high)
        };

        self.cache_mut().insert(key, res);
        res
    }

    pub fn diff(&self, f: Ref, g: Ref) -> Ref {
        debug!("diff({}, {})", f, g);

        if self.is_zero(f) || f == g {
            return self.zero();
        }
        if self.is_zero(g) {
            return f;
        }

        let key = OpKey::Diff(f, g);
        if let Some(&res) = self.cache().get(&key) {
            assert!(!res.is_negated());
            return res;
        }

        let i = self.variable(f.index());
        let j = self.variable(g.index());
        let res = if i < j {
            let low = self.diff(self.low(f.index()), g);
            let high = self.high(f.index());
            self.mk_node(i, low, high)
        } else if i > j {
            self.diff(f, self.low(g.index()))
        } else {
            assert_eq!(i, j);
            let low = self.diff(self.low(f.index()), self.low(g.index()));
            let high = self.diff(self.high(f.index()), self.high(g.index()));
            self.mk_node(i, low, high)
        };

        self.cache_mut().insert(key, res);
        res
    }

    pub fn count(&self, f: Ref) -> u64 {
        debug!("count({})", f);

        if self.is_zero(f) {
            return 0;
        }
        if self.is_one(f) {
            return 1;
        }

        if let Some(&res) = self.count_cache.borrow().get(&f) {
            return res;
        }

        let index = f.index();
        let low = self.low(index);
        let high = self.high(index);
        let res = self.count(low) + self.count(high);

        self.count_cache.borrow_mut().insert(f, res);
        res
    }
}

impl Zdd {
    pub fn to_bracket_string(&self, node: Ref) -> String {
        let mut visited = HashSet::new();
        self.node_to_str(node, &mut visited)
    }

    fn node_to_str(&self, node: Ref, visited: &mut HashSet<u32>) -> String {
        if self.is_zero(node) {
            return "∅".to_string();
        } else if self.is_one(node) {
            return "ε".to_string();
        }

        if !visited.insert(node.index()) {
            return format!("{}", node);
        }

        let index = node.index();
        let v = self.variable(index);
        let low = self.low(index);
        let high = self.high(index);

        // TODO: fix the order of 'high' and 'low'. Generally, triplets are (var, low, high), but here it is (var, high, low).
        format!(
            "{}:(x{}, {}, {})",
            node,
            v,
            self.node_to_str(high, visited),
            self.node_to_str(low, visited),
        )
    }
}

impl Zdd {
    pub fn single(&self, vars: impl IntoIterator<Item = u32>) -> Ref {
        let mut vars: Vec<u32> = vars.into_iter().collect();
        vars.sort();
        // debug!("single(vars = {:?})", vars);
        vars.reverse();
        let mut current = self.one();
        for var in vars {
            assert_ne!(var, 0, "Variable index should not be zero");
            current = self.mk_node(var, self.zero(), current);
        }
        current
    }
}

impl Zdd {
    pub fn combinations(&self, node: Ref) -> ZddCombinations {
        ZddCombinations::new(self, node)
    }
}

pub struct ZddCombinations<'a> {
    zdd: &'a Zdd,
    stack: Vec<(Ref, Vec<u32>)>,
}

impl<'a> ZddCombinations<'a> {
    pub fn new(zdd: &'a Zdd, node: Ref) -> Self {
        let stack = vec![(node, vec![])];
        ZddCombinations { zdd, stack }
    }
}

impl<'a> Iterator for ZddCombinations<'a> {
    type Item = Vec<u32>;

    fn next(&mut self) -> Option<Self::Item> {
        while let Some((node, subset)) = self.stack.pop() {
            if self.zdd.is_zero(node) {
                continue;
            } else if self.zdd.is_one(node) {
                return Some(subset);
            } else {
                assert!(!self.zdd.is_terminal(node));

                let index = node.index();
                let v = self.zdd.variable(index);
                let low = self.zdd.low(index);
                let high = self.zdd.high(index);

                self.stack.push((low, subset.clone()));

                let mut subset = subset;
                subset.push(v);
                self.stack.push((high, subset));
            }
        }
        None
    }
}

impl Zdd {
    pub fn cubes(&self, node: Ref, vars: &[u32]) -> ZddCubes {
        ZddCubes::new(self, node, vars.to_vec())
    }
}

pub struct ZddCubes<'a> {
    zdd: &'a Zdd,
    vars: Vec<u32>,
    stack: Vec<(Ref, Vec<(u32, i32)>)>,
}

impl<'a> ZddCubes<'a> {
    pub fn new(zdd: &'a Zdd, node: Ref, vars: Vec<u32>) -> Self {
        let stack = vec![(node, vec![])];
        ZddCubes { zdd, vars, stack }
    }
}

impl<'a> Iterator for ZddCubes<'a> {
    type Item = Vec<i32>;

    fn next(&mut self) -> Option<Self::Item> {
        while let Some((node, cube)) = self.stack.pop() {
            if self.zdd.is_zero(node) {
                continue;
            } else if self.zdd.is_one(node) {
                let map: HashMap<u32, i32> = cube.into_iter().collect();
                let mut cube = Vec::new();
                for var in self.vars.iter() {
                    let v = *var as i32;
                    if let Some(&sign) = map.get(var) {
                        if sign != 0 {
                            cube.push(sign * v);
                        }
                    } else {
                        cube.push(-v);
                    }
                }
                return Some(cube);
            } else {
                assert!(!self.zdd.is_terminal(node));

                let index = node.index();
                let v = self.zdd.variable(index);
                let low = self.zdd.low(index);
                let high = self.zdd.high(index);

                if low != high {
                    let mut cube_low = cube.clone();
                    cube_low.push((v, -1));
                    self.stack.push((low, cube_low));

                    let mut cube_high = cube;
                    cube_high.push((v, 1));
                    self.stack.push((high, cube_high));
                } else {
                    let mut cube = cube;
                    cube.push((v, 0));
                    self.stack.push((low, cube));
                }
            }
        }
        None
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_empty() {
        let zdd = Zdd::default();

        let empty = zdd.zero();
        println!("empty = {} with count {}", empty, zdd.count(empty));
        assert_eq!(zdd.count(empty), 0);
    }

    #[test]
    fn test_single() {
        let zdd = Zdd::default();

        let single = zdd.one();
        println!("single = {} with count {}", single, zdd.count(single));
        assert_eq!(zdd.count(single), 1);
    }

    #[test]
    fn test_single_cube_a() {
        let zdd = Zdd::default();

        // cube `a * ~b * ~c` == combination `{a}`
        let cube = zdd.single([1]);
        println!("cube = {} with count {}", cube, zdd.count(cube));
        println!("cube = {}", zdd.to_bracket_string(cube));
        assert_eq!(zdd.count(cube), 1);
    }

    #[test]
    fn test_single_cube_ac() {
        let zdd = Zdd::default();

        // cube `a * ~b * c` == combination `{ac}`
        let cube = zdd.single([1, 3]);
        println!("cube = {} with count {}", cube, zdd.count(cube));
        println!("cube = {}", zdd.to_bracket_string(cube));
        assert_eq!(zdd.count(cube), 1);
    }

    #[test]
    fn test_union() {
        let zdd = Zdd::default();

        let c1 = zdd.single([1]);
        println!("c1 = {} with count {}", c1, zdd.count(c1));
        println!("c1 = {}", zdd.to_bracket_string(c1));
        let c3 = zdd.single([3]);
        println!("c3 = {} with count {}", c3, zdd.count(c3));
        println!("c3 = {}", zdd.to_bracket_string(c3));
        let c13 = zdd.union(c1, c3);
        println!("c13 = union({}, {}) = {} with count {}", c13, c1, c3, zdd.count(c13));
        println!("c13 = {}", zdd.to_bracket_string(c13));
        assert_eq!(zdd.count(c13), 2);
    }

    #[test]
    fn test_combinations() {
        let zdd = Zdd::default();

        let f = zdd.union(zdd.union(zdd.single([1]), zdd.single([2, 3])), zdd.single([3]));
        println!("f = {} with count {}", f, zdd.count(f));
        println!("f = {}", zdd.to_bracket_string(f));
        assert_eq!(zdd.count(f), 3);

        println!("combinations for {}:", f);
        for c in zdd.combinations(f) {
            println!("  {:?}", c);
        }
        assert_eq!(zdd.combinations(f).count(), 3);

        let vars = vec![1, 2, 3];
        println!("cubes over vars {:?} for {}:", vars, f);
        for c in zdd.cubes(f, &vars) {
            println!("  {:?}", c);
        }
        assert_eq!(zdd.cubes(f, &vars).count(), 2);
    }
}
