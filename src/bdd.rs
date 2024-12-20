use std::cell;
use std::cell::RefCell;
use std::cmp::{min, Ordering};
use std::collections::{HashMap, HashSet, VecDeque};
use std::fmt::Debug;

use log::debug;

use crate::cache::Cache;
use crate::node::Node;
use crate::reference::Ref;
use crate::storage::Storage;
use crate::utils::OpKey;

pub struct Bdd {
    storage: RefCell<Storage>,
    cache: RefCell<Cache<OpKey, Ref>>,
    size_cache: RefCell<Cache<Ref, u64>>,
    pub zero: Ref,
    pub one: Ref,
}

impl Bdd {
    pub fn new(storage_bits: usize) -> Self {
        assert!(storage_bits <= 31, "Storage bits should be in the range 0..=31");

        let cache_bits = min(storage_bits, 16);

        let mut storage = Storage::new(storage_bits);

        // Allocate the terminal node:
        let one = storage.alloc();
        assert_eq!(one, 1); // Make sure the terminal node is (1).
        let one = Ref::positive(one as u32);
        let zero = -one;

        Self {
            storage: RefCell::new(storage),
            cache: RefCell::new(Cache::new(cache_bits)),
            size_cache: RefCell::new(Cache::new(cache_bits)),
            zero,
            one,
        }
    }
}

impl Default for Bdd {
    fn default() -> Self {
        Bdd::new(20)
    }
}

impl Debug for Bdd {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let storage = self.storage.borrow();
        f.debug_struct("Bdd")
            .field("capacity", &storage.capacity())
            .field("size", &storage.size())
            .field("real_size", &storage.real_size())
            .finish()
    }
}

impl Bdd {
    pub fn storage(&self) -> cell::Ref<'_, Storage> {
        self.storage.borrow()
    }
    fn storage_mut(&self) -> cell::RefMut<'_, Storage> {
        self.storage.borrow_mut()
    }
    pub fn cache(&self) -> cell::Ref<'_, Cache<OpKey, Ref>> {
        self.cache.borrow()
    }
    fn cache_mut(&self) -> cell::RefMut<'_, Cache<OpKey, Ref>> {
        self.cache.borrow_mut()
    }
    pub fn size_cache(&self) -> cell::Ref<'_, Cache<Ref, u64>> {
        self.size_cache.borrow()
    }
    fn size_cache_mut(&self) -> cell::RefMut<'_, Cache<Ref, u64>> {
        self.size_cache.borrow_mut()
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
    pub fn next(&self, index: u32) -> usize {
        self.storage().next(index as usize)
    }

    pub fn low_node(&self, node: Ref) -> Ref {
        let low = self.low(node.index());
        if node.is_negated() {
            -low
        } else {
            low
        }
    }
    pub fn high_node(&self, node: Ref) -> Ref {
        let high = self.high(node.index());
        if node.is_negated() {
            -high
        } else {
            high
        }
    }

    pub fn is_zero(&self, node: Ref) -> bool {
        node == self.zero
    }
    pub fn is_one(&self, node: Ref) -> bool {
        node == self.one
    }
    pub fn is_terminal(&self, node: Ref) -> bool {
        self.is_zero(node) || self.is_one(node)
    }

    pub fn mk_node(&self, v: u32, low: Ref, high: Ref) -> Ref {
        // debug!("mk(v = {}, low = {}, high = {})", v, low, high);

        assert_ne!(v, 0, "Variable index should not be zero");

        // Handle canonicity
        if high.is_negated() {
            // debug!("mk: restoring canonicity");
            return -self.mk_node(v, -low, -high);
        }

        // Handle duplicates
        if low == high {
            // debug!("mk: duplicates {} == {}", low, high);
            return low;
        }

        let i = self.storage_mut().put(Node { variable: v, low, high });
        Ref::positive(i as u32)
    }

    pub fn mk_var(&self, v: u32) -> Ref {
        assert_ne!(v, 0, "Variable index should not be zero");
        self.mk_node(v, self.zero, self.one)
    }

    pub fn cube(&self, literals: impl IntoIterator<Item = i32>) -> Ref {
        let mut literals = literals.into_iter().collect::<Vec<_>>();
        literals.sort_by_key(|&v| v.abs());
        debug!("cube(literals = {:?})", literals);
        literals.reverse();
        let mut current = self.one;
        for lit in literals {
            assert_ne!(lit, 0, "Variable index should not be zero");
            current = if lit < 0 {
                self.mk_node(-lit as u32, current, self.zero)
            } else {
                self.mk_node(lit as u32, self.zero, current)
            };
        }
        current
    }

    pub fn clause(&self, literals: impl IntoIterator<Item = i32>) -> Ref {
        let mut literals = literals.into_iter().collect::<Vec<_>>();
        literals.sort_by_key(|&v| v.abs());
        debug!("clause(literals = {:?})", literals);
        literals.reverse();
        let mut current = self.zero;
        for lit in literals {
            assert_ne!(lit, 0, "Variable index should not be zero");
            current = if lit < 0 {
                self.mk_node(-lit as u32, self.one, current)
            } else {
                self.mk_node(lit as u32, current, self.one)
            };
        }
        current
    }

    pub fn top_cofactors(&self, node: Ref, v: u32) -> (Ref, Ref) {
        assert_ne!(v, 0, "Variable index should not be zero");

        if self.is_terminal(node) {
            return (node, node);
        }

        let index = node.index();
        if v < self.variable(index) {
            // 'node' does not depend on 'v'
            return (node, node);
        }
        assert_eq!(v, self.variable(index));
        if node.is_negated() {
            (-self.low(index), -self.high(index))
        } else {
            (self.low(index), self.high(index))
        }
    }

    /// Apply the ITE operation to the arguments.
    ///
    /// ```text
    /// ITE(x, y, z) == (x ∧ y) ∨ (¬x ∧ z) == (x -> y) ∧ (¬x -> z)
    /// ```
    ///
    /// # Examples
    ///
    /// ```
    /// use bdd_rs::bdd::Bdd;
    ///
    /// let bdd = Bdd::default();
    /// let x = bdd.mk_var(1);
    /// let y = bdd.mk_var(2);
    /// let z = bdd.mk_var(3);
    /// let f = bdd.apply_ite(x, y, z);
    /// assert_eq!(f, bdd.mk_node(bdd.variable(x.index()), z, y));
    /// let  x_and_y = bdd.apply_and(x, y);
    /// let  not_x_and_z = bdd.apply_and(-x, z);
    /// assert_eq!(f, bdd.apply_or(x_and_y, not_x_and_z));
    /// ```
    pub fn apply_ite(&self, f: Ref, g: Ref, h: Ref) -> Ref {
        debug!("apply_ite(f = {}, g = {}, h = {})", f, g, h);

        // Base cases:
        //   ite(1,G,H) => G
        //   ite(0,G,H) => H
        if self.is_one(f) {
            debug!("ite(1,G,H) => G");
            return g;
        }
        if self.is_zero(f) {
            debug!("ite(0,G,H) => H");
            return h;
        }

        // From now on, F is known not to be a constant
        assert!(!self.is_terminal(f));

        // More base cases:
        //   ite(F,G,G) => G
        //   ite(F,1,0) => F
        //   ite(F,0,1) => ~F
        //   ite(F,1,~F) => 1
        //   ite(F,F,1) => 1
        //   ite(F,~F,0) => 0
        //   ite(F,0,F) => F
        if g == h {
            debug!("ite(F,G,G) => G");
            return g;
        }
        if self.is_one(g) && self.is_zero(h) {
            debug!("ite(F,1,0) => F");
            return f;
        }
        if self.is_zero(g) && self.is_one(h) {
            debug!("ite(F,0,1) => ~F");
            return -f;
        }
        if self.is_one(g) && h == -f {
            debug!("ite(F,1,~F) => 1");
            return self.one;
        }
        if g == f && self.is_one(h) {
            debug!("ite(F,F,1) => 1");
            return self.one;
        }
        if g == -f && self.is_zero(h) {
            debug!("ite(F,~F,0) => 0");
            return self.zero;
        }
        if self.is_zero(g) && h == f {
            debug!("ite(F,0,F) => F");
            return f;
        }

        // Standard triples:
        //   ite(F,F,H) => ite(F,1,H)
        //   ite(F,G,F) => ite(F,G,0)
        //   ite(F,~F,H) => ite(F,0,H)
        //   ite(F,G,~F) => ite(F,G,1)
        if g == f {
            debug!("ite(F,F,H) => ite(F,1,H)");
            return self.apply_ite(f, self.one, h);
        }
        if h == f {
            debug!("ite(F,G,F) => ite(F,G,0)");
            return self.apply_ite(f, g, self.zero);
        }
        if g == -f {
            debug!("ite(F,~F,H) => ite(F,0,H)");
            return self.apply_ite(f, self.zero, h);
        }
        if h == -f {
            debug!("ite(F,G,~F) => ite(F,G,1)");
            return self.apply_ite(f, g, self.one);
        }

        let i = self.variable(f.index());
        let j = self.variable(g.index());
        let k = self.variable(h.index());
        assert_ne!(i, 0);

        // Equivalent pairs:
        //   ite(F,1,H) == ite(H,1,F) == F ∨ H
        //   ite(F,G,0) == ite(G,F,0) == F ∧ G
        //   ite(F,G,1) == ite(~G,~F,1) == F -> G
        //   ite(F,0,H) == ite(~H,0,~F) == ~F ∧ H
        //   ite(F,G,~G) == ite(G,F,~F)
        // (choose the one with the lowest variable)
        if self.is_one(g) && k < i {
            assert_ne!(k, 0);
            debug!("ite(F,1,H) => ite(H,1,F)");
            return self.apply_ite(h, self.one, f);
        }
        if self.is_zero(h) && j < i {
            assert_ne!(j, 0);
            debug!("ite(F,G,0) => ite(G,F,0)");
            return self.apply_ite(g, f, self.zero);
        }
        if self.is_one(h) && j < i {
            assert_ne!(j, 0);
            debug!("ite(F,G,1) => ite(~G,~F,1)");
            return self.apply_ite(-g, -f, self.one);
        }
        if self.is_zero(g) && k < i {
            assert_ne!(k, 0);
            debug!("ite(F,0,H) => ite(~H,0,~F)");
            return self.apply_ite(-h, self.zero, -f);
        }
        if g == -h && j < i {
            assert_ne!(j, 0);
            debug!("ite(F,G,~G) => ite(G,F,~F)");
            return self.apply_ite(g, f, -f);
        }

        // Make sure the first two pointers (f and g) are regular (not negated)
        let (mut f, mut g, mut h) = (f, g, h);

        // ite(~F,G,H) => ite(F,H,G)
        if f.is_negated() {
            debug!("ite(~F,G,H) => ite(F,H,G)");
            f = -f;
            std::mem::swap(&mut g, &mut h);
        }
        assert!(!f.is_negated());

        // ite(F,~G,H) => ~ite(F,G,~H)
        let mut n = false;
        if g.is_negated() {
            n = true;
            g = -g;
            h = -h;
        }
        assert!(!g.is_negated());

        let (f, g, h) = (f, g, h); // make immutable

        let key = OpKey::Ite(f, g, h);
        debug!("key = {:?}", key);
        if let Some(&res) = self.cache().get(&key) {
            debug!("cache: apply_ite(f = {}, g = {}, h = {}) -> {}", f, g, h, res);
            return if n { -res } else { res };
        }

        // Determine the top variable:
        let mut m = i;
        if j != 0 {
            m = m.min(j);
        }
        if k != 0 {
            m = m.min(k);
        }
        debug!("min variable = {}", m);
        assert_ne!(m, 0);

        let (f0, f1) = self.top_cofactors(f, m);
        debug!("cofactors of f = {} are: f0 = {}, f1 = {}", f, f0, f1);
        let (g0, g1) = self.top_cofactors(g, m);
        debug!("cofactors of g = {} are: g0 = {}, g1 = {}", g, g0, g1);
        let (h0, h1) = self.top_cofactors(h, m);
        debug!("cofactors of h = {} are: h0 = {}, h1 = {}", h, h0, h1);

        let e = self.apply_ite(f0, g0, h0);
        let t = self.apply_ite(f1, g1, h1);
        debug!("cofactors of res: e = {}, t = {}", e, t);

        let res = self.mk_node(m, e, t);
        debug!("computed: apply_ite(f = {}, g = {}, h = {}) -> {}", f, g, h, res);
        self.cache_mut().insert(key, res);
        if n {
            -res
        } else {
            res
        }
    }

    fn maybe_constant(&self, node: Ref) -> Option<bool> {
        if self.is_zero(node) {
            Some(false)
        } else if self.is_one(node) {
            Some(true)
        } else {
            None
        }
    }

    pub fn ite_constant(&self, f: Ref, g: Ref, h: Ref) -> Option<bool> {
        debug!("ite_constant(f = {}, g = {}, h = {})", f, g, h);

        // TODO: "trivial" cases

        // Base cases:
        //   ite(1,G,H) => G
        //   ite(0,G,H) => H
        if self.is_one(f) {
            debug!("ite(1,G,H) => G");
            // return g;
            return self.maybe_constant(g);
        }
        if self.is_zero(f) {
            debug!("ite(0,G,H) => H");
            // return h;
            return self.maybe_constant(h);
        }

        // From now on, F is known not to be a constant
        assert!(!self.is_terminal(f));

        // More base cases:
        //   ite(F,G,G) => G
        //   ite(F,1,0) => F
        //   ite(F,0,1) => ~F
        //   ite(F,1,~F) => 1
        //   ite(F,F,1) => 1
        //   ite(F,~F,0) => 0
        //   ite(F,0,F) => F
        if g == h {
            debug!("ite(F,G,G) => G");
            // return g;
            return self.maybe_constant(g);
        }
        if self.is_one(g) && self.is_zero(h) {
            debug!("ite(F,1,0) => F");
            // return f;
            return None;
        }
        if self.is_zero(g) && self.is_one(h) {
            debug!("ite(F,0,1) => ~F");
            // return -f;
            return None;
        }
        if self.is_one(g) && h == -f {
            debug!("ite(F,1,~F) => 1");
            // return self.one;
            return Some(true);
        }
        if g == f && self.is_one(h) {
            debug!("ite(F,F,1) => 1");
            // return self.one;
            return Some(true);
        }
        if g == -f && self.is_zero(h) {
            debug!("ite(F,~F,0) => 0");
            // return self.zero;
            return Some(false);
        }
        if self.is_zero(g) && h == f {
            debug!("ite(F,0,F) => F");
            // return f;
            return None;
        }

        // TODO: standard triples?

        let key = OpKey::Ite(f, g, h);
        if let Some(&res) = self.cache().get(&key) {
            debug!("cache: ite_constant(f = {}, g = {}, h = {}) -> {}", f, g, h, res);
            assert!(!self.is_terminal(res));
            return None;
        }

        let i = self.variable(f.index());
        let j = self.variable(g.index());
        let k = self.variable(h.index());
        assert_ne!(i, 0);

        // Determine the top variable:
        let mut m = i;
        if j != 0 {
            m = m.min(j);
        }
        if k != 0 {
            m = m.min(k);
        }
        debug!("min variable = {}", m);
        assert_ne!(m, 0);

        let (f0, f1) = self.top_cofactors(f, m);
        debug!("cofactors of f = {} are: f0 = {}, f1 = {}", f, f0, f1);
        let (g0, g1) = self.top_cofactors(g, m);
        debug!("cofactors of g = {} are: g0 = {}, g1 = {}", g, g0, g1);
        let (h0, h1) = self.top_cofactors(h, m);
        debug!("cofactors of h = {} are: h0 = {}, h1 = {}", h, h0, h1);

        let t = self.ite_constant(f1, g1, h1);
        if t.is_none() {
            return None;
        }
        let e = self.ite_constant(f0, g0, h0);
        if e != Some(true) {
            return None;
        }
        t
    }

    pub fn is_implies(&self, f: Ref, g: Ref) -> bool {
        debug!("is_implies(f = {}, g = {})", f, g);
        self.ite_constant(f, g, self.one) == Some(true)
    }

    pub fn apply_not(&self, f: Ref) -> Ref {
        debug!("apply_not(f = {})", f);
        -f
    }

    pub fn apply_and(&self, u: Ref, v: Ref) -> Ref {
        debug!("apply_and(u = {}, v = {})", u, v);
        self.apply_ite(u, v, self.zero)
    }

    pub fn apply_or(&self, u: Ref, v: Ref) -> Ref {
        debug!("apply_or(u = {}, v = {})", u, v);
        self.apply_ite(u, self.one, v)
    }

    pub fn apply_xor(&self, u: Ref, v: Ref) -> Ref {
        debug!("apply_xor(u = {}, v = {})", u, v);
        self.apply_ite(u, -v, v)
    }

    pub fn apply_eq(&self, u: Ref, v: Ref) -> Ref {
        debug!("apply_eq(u = {}, v = {})", u, v);
        self.apply_ite(u, v, -v)
    }

    pub fn apply_imply(&self, u: Ref, v: Ref) -> Ref {
        debug!("apply_imply(u = {}, v = {})", u, v);
        self.apply_ite(u, v, self.one)
    }

    pub fn apply_and_many(&self, nodes: impl IntoIterator<Item = Ref>) -> Ref {
        debug!("apply_and_many(...)");
        let mut res = self.one;
        for node in nodes.into_iter() {
            res = self.apply_and(res, node);
        }
        res
    }

    pub fn apply_or_many(&self, nodes: impl IntoIterator<Item = Ref>) -> Ref {
        debug!("apply_or_many(...)");
        let mut res = self.zero;
        for node in nodes.into_iter() {
            res = self.apply_or(res, node);
        }
        res
    }

    // f|v<-b
    pub fn substitute(&self, f: Ref, v: u32, b: bool) -> Ref {
        let mut cache = HashMap::new();
        self.substitute_(f, v, b, &mut cache)
    }

    fn substitute_(&self, f: Ref, v: u32, b: bool, cache: &mut HashMap<Ref, Ref>) -> Ref {
        assert_ne!(v, 0, "Variable index should not be zero");

        if self.is_terminal(f) {
            return f;
        }

        let i = self.variable(f.index());

        if v < i {
            // 'f' does not depend on 'v'
            return f;
        }

        if v == i {
            // Note: here, we do not need to wrap it with restrict(...).
            return if b { self.high_node(f) } else { self.low_node(f) };
        }

        if let Some(&res) = cache.get(&f) {
            return res;
        }

        assert!(v > i);
        let low = self.substitute_(self.low_node(f), v, b, cache);
        let high = self.substitute_(self.high_node(f), v, b, cache);
        let res = self.mk_node(i, low, high);
        cache.insert(f, res);
        res
    }

    pub fn substitute_multi(&self, f: Ref, values: &HashMap<u32, bool>) -> Ref {
        let mut cache = HashMap::new();
        self.substitute_multi_(f, values, &mut cache)
    }

    fn substitute_multi_(&self, f: Ref, values: &HashMap<u32, bool>, cache: &mut HashMap<Ref, Ref>) -> Ref {
        debug!("restrict_multi(f = {}, values = {:?})", f, values);

        if self.is_terminal(f) {
            return f;
        }

        if values.is_empty() {
            return f;
        }

        if let Some(&res) = cache.get(&f) {
            return res;
        }

        let i = self.variable(f.index());
        let res = if let Some(&b) = values.get(&i) {
            if b {
                // `i` needs to be assigned true
                self.substitute_multi_(self.high_node(f), values, cache)
            } else {
                // `i` needs to be assigned false
                self.substitute_multi_(self.low_node(f), values, cache)
            }
        } else {
            // `i` does not need to be assigned
            let low = self.substitute_multi_(self.low_node(f), values, cache);
            let high = self.substitute_multi_(self.high_node(f), values, cache);
            self.mk_node(i, low, high)
        };
        cache.insert(f, res);
        res
    }

    pub fn cofactor_cube(&self, f: Ref, cube: &[i32]) -> Ref {
        let mut cache = HashMap::new();
        self.cofactor_cube_(f, cube, &mut cache)
    }

    fn cofactor_cube_(&self, f: Ref, cube: &[i32], cache: &mut HashMap<(usize, Ref), Ref>) -> Ref {
        // debug!("cofactor_cube(f = {}, cube = {:?})", f, cube);

        if cube.is_empty() {
            // debug!("cube is empty");
            return f;
        }

        if self.is_terminal(f) {
            // debug!("f is terminal");
            return f;
        }

        let key = (cube.len(), f);
        if let Some(&res) = cache.get(&key) {
            return res;
        }

        let t = self.variable(f.index()); // top variable of `f`
        let xu = cube[0];
        let u = xu.unsigned_abs();

        let res = match t.cmp(&u) {
            Ordering::Greater => {
                // `t > u`: `f` does not depend on `u`
                self.cofactor_cube_(f, &cube[1..], cache)
            }
            Ordering::Equal => {
                // `t == u`: `u` is the top variable of `f`
                // let (f0, f1) = self.top_cofactors(f, u);
                // if xu > 0 {
                //     self.cofactor_cube_(f1, &cube[1..], cache)
                // } else {
                //     self.cofactor_cube_(f0, &cube[1..], cache)
                // }
                let res = if xu > 0 { self.high_node(f) } else { self.low_node(f) };
                self.cofactor_cube_(res, &cube[1..], cache)
            }
            Ordering::Less => {
                // `t < u`: `u` is not the top variable of 'f'
                // let (f0, f1) = self.top_cofactors(f, t);
                let f0 = self.low_node(f);
                let f1 = self.high_node(f);
                let low = self.cofactor_cube_(f0, cube, cache);
                let high = self.cofactor_cube_(f1, cube, cache);
                self.mk_node(t, low, high)
            }
        };
        cache.insert(key, res);
        res
    }

    // f|v<-g
    pub fn compose(&self, f: Ref, v: u32, g: Ref) -> Ref {
        let mut cache = Cache::new(16);
        self.compose_(f, v, g, &mut cache)
    }

    fn compose_(&self, f: Ref, v: u32, g: Ref, cache: &mut Cache<(Ref, Ref), Ref>) -> Ref {
        // TODO: compose(f, v, g) = ITE(g, restrict(f, v, true), restrict(f, v, false))

        debug!("compose(f = {}, v = {}, g = {})", f, v, g);

        if self.is_terminal(f) {
            return f;
        }

        let i = self.variable(f.index());
        assert_ne!(i, 0);
        if v < i {
            // 'f' does not depend on 'v'
            return f;
        }

        let key = (f, g);
        if let Some(&res) = cache.get(&key) {
            return res;
        }

        let res = if v == i {
            let index = f.index();
            let res = self.apply_ite(g, self.high(index), self.low(index));
            if f.is_negated() {
                -res
            } else {
                res
            }
        } else {
            assert!(v > i);

            let m = if self.is_terminal(g) { i } else { min(i, self.variable(g.index())) };
            assert_ne!(m, 0);

            let (f0, f1) = self.top_cofactors(f, m);
            let (g0, g1) = self.top_cofactors(g, m);
            let h0 = self.compose_(f0, v, g0, cache);
            let h1 = self.compose_(f1, v, g1, cache);

            self.mk_node(m, h0, h1)
        };
        cache.insert(key, res);
        res
    }

    pub fn constrain(&self, f: Ref, g: Ref) -> Ref {
        debug!("constrain(f = {}, g = {})", f, g);

        if self.is_zero(g) {
            debug!("g is zero => f|g = 0");
            return self.zero;
        }
        if self.is_one(g) {
            debug!("g is one => f|g = f");
            return f;
        }
        if self.is_terminal(f) {
            debug!("f is terminal => f|g = f");
            return f;
        }
        if f == g {
            debug!("f = g => f|g = 1");
            return self.one;
        }
        if f == -g {
            debug!("f = ~g => f|g = 0");
            return self.zero;
        }

        let key = OpKey::Constrain(f, g);
        if let Some(&res) = self.cache().get(&key) {
            debug!("cache: constrain(f = {}, g = {}) -> {}", f, g, res);
            return res;
        }

        // TODO: is it necessary to compute min var, or we can just use var(g)?
        let i = self.variable(f.index());
        let j = self.variable(g.index());
        let v = min(i, j);
        debug!("min variable = {}", v);

        let (f0, f1) = self.top_cofactors(f, v);
        let (g0, g1) = self.top_cofactors(g, v);

        if self.is_zero(g1) {
            debug!("g1 is zero");
            return self.constrain(f0, g0);
        }
        if self.is_zero(g0) {
            debug!("g0 is zero");
            return self.constrain(f1, g1);
        }

        if f0 == f1 {
            debug!("f0 == f1");
            let low = self.constrain(f, g0);
            let high = self.constrain(f, g1);
            return self.mk_node(v, low, high);
        }

        let low = self.constrain(f0, g0);
        let high = self.constrain(f1, g1);
        // TODO: replace 'mk_node' with 'ITE'?
        let res = self.mk_node(v, low, high);
        debug!("computed: constrain(f = {}, g = {}) -> {}", f, g, res);

        self.cache_mut().insert(key, res);
        res
    }

    pub fn restrict(&self, f: Ref, g: Ref) -> Ref {
        debug!("restrict(f = {}, g = {})", f, g);

        if self.is_zero(g) {
            log::warn!("g is zero => f|g = 0");
            return self.zero;
        }
        if self.is_one(g) || self.is_terminal(f) {
            return f;
        }
        if f == g {
            return self.one;
        }
        if f == -g {
            return self.zero;
        }

        let key = OpKey::Restrict(f, g);
        if let Some(&res) = self.cache().get(&key) {
            debug!("cache: restrict(f = {}, g = {}) -> {}", f, g, res);
            return res;
        }

        let i = self.variable(f.index());
        let j = self.variable(g.index());
        let v = min(i, j);

        let (f0, f1) = self.top_cofactors(f, v);
        let (g0, g1) = self.top_cofactors(g, v);

        if self.is_zero(g1) {
            return self.restrict(f0, g0);
        }
        if self.is_zero(g0) {
            return self.restrict(f1, g1);
        }

        let res = if v == i {
            let low = self.restrict(f0, g0);
            let high = self.restrict(f1, g1);
            self.mk_node(v, low, high)
        } else {
            self.restrict(f, self.apply_ite(g1, self.one, g0))
        };
        self.cache_mut().insert(key, res);
        res
    }

    pub fn descendants(&self, nodes: impl IntoIterator<Item = Ref>) -> HashSet<u32> {
        let mut visited = HashSet::new();
        visited.insert(self.one.index());
        let mut queue = VecDeque::from_iter(nodes.into_iter().map(|node| node.index()));

        while let Some(i) = queue.pop_front() {
            if visited.insert(i) {
                queue.push_back(self.low(i).index());
                queue.push_back(self.high(i).index());
            }
        }

        visited
    }

    pub fn size(&self, f: Ref) -> u64 {
        debug!("size(f = {})", f);
        if let Some(&size) = self.size_cache().get(&f) {
            debug!("cache: size({}) -> {}", f, size);
            return size;
        }
        let size = self.descendants([f]).len() as u64;
        debug!("computed: size({}) -> {}", f, size);
        self.size_cache_mut().insert(f, size);
        size
    }

    pub fn collect_garbage(&self, roots: &[Ref]) {
        debug!("Collecting garbage...");

        self.cache_mut().clear();
        self.size_cache_mut().clear();

        let alive = self.descendants(roots.iter().copied());
        debug!("Alive nodes: {:?}", alive);

        let n = self.storage().num_buckets();
        for i in 0..n {
            let mut index = self.storage().bucket(i);

            if index != 0 {
                debug!("Cleaning bucket #{} pointing to {}", i, index);

                while index != 0 && !alive.contains(&(index as u32)) {
                    let next = self.storage().next(index);
                    debug!("Dropping {}, next = {}", index, next);
                    self.storage_mut().drop(index);
                    index = next;
                }

                debug!(
                    "Relinking bucket #{} to {}, next = {:?}",
                    i,
                    index,
                    if index != 0 { Some(self.storage().next(index)) } else { None }
                );
                self.storage_mut().set_bucket(i, index);

                let mut prev = index;
                while prev != 0 {
                    let mut cur = self.storage().next(prev);
                    while cur != 0 {
                        if !alive.contains(&(cur as u32)) {
                            let next = self.storage().next(cur);
                            debug!("Dropping {}, prev = {}, next = {}", cur, prev, next);
                            self.storage_mut().drop(cur);
                            cur = next;
                        } else {
                            debug!("Keeping {}, prev = {}", cur, prev);
                            break;
                        }
                    }
                    let next_prev = self.storage().next(prev);
                    if next_prev != cur {
                        debug!("Relinking next({}) from {} to {}", prev, next_prev, cur);
                        self.storage_mut().set_next(prev, cur);
                    }
                    prev = cur;
                }
            }
        }
    }

    pub fn to_bracket_string(&self, node: Ref) -> String {
        let mut visited = HashSet::new();
        self.node_to_str(node, &mut visited)
    }

    fn node_to_str(&self, node: Ref, visited: &mut HashSet<u32>) -> String {
        if self.is_zero(node) {
            return "⊥".to_string();
        } else if self.is_one(node) {
            return "⊤".to_string();
        }

        if !visited.insert(node.index()) {
            return format!("{}", node);
        }

        let index = node.index();
        let v = self.variable(index);
        let low = self.low(index);
        let high = self.high(index);

        format!(
            "{}:(x{}, {}, {})",
            node,
            v,
            self.node_to_str(high, visited),
            self.node_to_str(low, visited),
        )
    }
}

#[cfg(test)]
mod tests {
    use test_log::test;

    use super::*;

    #[test]
    fn test_var() {
        let bdd = Bdd::default();

        let x = bdd.mk_var(1);

        assert_eq!(bdd.variable(x.index()), 1);
        assert_eq!(bdd.high_node(x), bdd.one);
        assert_eq!(bdd.low_node(x), bdd.zero);
    }

    #[test]
    fn test_not_var() {
        let bdd = Bdd::default();

        let x = bdd.mk_var(1);
        let not_x = -x;

        assert_eq!(bdd.variable(not_x.index()), 1);
        assert_eq!(bdd.high_node(not_x), bdd.zero);
        assert_eq!(bdd.low_node(not_x), bdd.one);
    }

    #[test]
    fn test_terminal() {
        let bdd = Bdd::default();

        assert_eq!(bdd.is_terminal(bdd.zero), true);
        assert_eq!(bdd.is_zero(bdd.zero), true);
        assert_eq!(bdd.is_one(bdd.zero), false);

        assert_eq!(bdd.is_terminal(bdd.one), true);
        assert_eq!(bdd.is_zero(bdd.one), false);
        assert_eq!(bdd.is_one(bdd.one), true);

        assert_eq!(bdd.variable(bdd.zero.index()), 0);
        assert_eq!(bdd.low(bdd.zero.index()).index(), 0);
        assert_eq!(bdd.high(bdd.zero.index()).index(), 0);

        assert_eq!(bdd.variable(bdd.one.index()), 0);
        assert_eq!(bdd.low(bdd.one.index()).index(), 0);
        assert_eq!(bdd.high(bdd.one.index()).index(), 0);
    }

    #[test]
    fn test_cube() {
        let bdd = Bdd::default();

        let x1 = bdd.mk_var(1);
        let x2 = bdd.mk_var(2);
        let x3 = bdd.mk_var(3);

        let f = bdd.apply_and(bdd.apply_and(x1, x2), x3);
        let cube = bdd.cube([1, 2, 3]);
        assert_eq!(f, cube);

        let f = bdd.apply_and(bdd.apply_and(x1, -x2), -x3);
        let cube = bdd.cube([1, -2, -3]);
        assert_eq!(f, cube);
    }

    #[test]
    fn test_clause() {
        let bdd = Bdd::default();

        let x1 = bdd.mk_var(1);
        let x2 = bdd.mk_var(2);
        let x3 = bdd.mk_var(3);

        let f = bdd.apply_or(bdd.apply_or(x1, x2), x3);
        let clause = bdd.clause([1, 2, 3]);
        assert_eq!(f, clause);

        let f = bdd.apply_or(bdd.apply_or(x1, -x2), -x3);
        let clause = bdd.clause([1, -2, -3]);
        assert_eq!(f, clause);
    }

    #[test]
    fn test_de_morgan_and() {
        let bdd = Bdd::default();

        let x = bdd.mk_var(1);
        let y = bdd.mk_var(2);

        let f = -bdd.apply_and(x, y);
        let g = bdd.apply_or(-x, -y);
        assert_eq!(f, g);
    }

    #[test]
    fn test_de_morgan_or() {
        let bdd = Bdd::default();

        let x = bdd.mk_var(1);
        let y = bdd.mk_var(2);

        let f = -bdd.apply_or(x, y);
        let g = bdd.apply_and(-x, -y);
        assert_eq!(f, g);
    }

    #[test]
    fn test_xor_itself() {
        let bdd = Bdd::default();

        let x = bdd.mk_var(1);
        let y = bdd.mk_var(2);
        let f = bdd.apply_and(x, y);

        let res = bdd.apply_xor(f, f);
        assert_eq!(res, bdd.zero);
    }

    #[test]
    fn test_xor_contrary() {
        let bdd = Bdd::default();

        let x = bdd.mk_var(1);
        let y = bdd.mk_var(2);
        let f = bdd.apply_and(x, y);

        let res = bdd.apply_xor(f, -f);
        assert_eq!(res, bdd.one);
    }

    #[test]
    fn test_apply_ite() {
        let bdd = Bdd::default();

        // Terminal cases
        let g = bdd.mk_var(2);
        let h = bdd.mk_var(3);
        assert_eq!(bdd.apply_ite(bdd.one, g, h), g);
        assert_eq!(bdd.apply_ite(bdd.zero, g, h), h);

        // Functions
        let f = bdd.mk_node(4, bdd.one, h);
        assert_eq!(bdd.apply_ite(f, f, h), bdd.apply_or(f, h));
        assert_eq!(bdd.apply_ite(f, g, f), bdd.apply_and(f, g));
        assert_eq!(bdd.apply_ite(f, -g, bdd.one), -bdd.apply_and(f, g));
        assert_eq!(bdd.apply_ite(f, bdd.zero, -h), -bdd.apply_or(f, h));

        // Constants
        let f = bdd.mk_var(5);
        assert_eq!(bdd.apply_ite(f, g, g), g);
        assert_eq!(bdd.apply_ite(f, bdd.one, bdd.zero), f);
        assert_eq!(bdd.apply_ite(f, bdd.zero, bdd.one), -f);

        // General case
        let f = bdd.mk_var(6);
        let g = bdd.mk_var(7);
        let h = bdd.mk_var(8);
        let result = bdd.mk_node(bdd.variable(f.index()), -g, -h);
        assert_eq!(bdd.apply_ite(-f, -g, -h), result);
    }

    #[test]
    fn test_cofactor_cube() {
        let bdd = Bdd::default();

        let f = bdd.cube([1, 2, 3]);
        println!("f = {}", bdd.to_bracket_string(f));

        assert_eq!(bdd.cofactor_cube(f, &[1]), bdd.cube([2, 3]));
        assert_eq!(bdd.cofactor_cube(f, &[2]), bdd.cube([1, 3]));
        assert_eq!(bdd.cofactor_cube(f, &[3]), bdd.cube([1, 2]));
        assert_eq!(bdd.cofactor_cube(f, &[-1]), bdd.zero);
        assert_eq!(bdd.cofactor_cube(f, &[-2]), bdd.zero);
        assert_eq!(bdd.cofactor_cube(f, &[-3]), bdd.zero);

        assert_eq!(bdd.cofactor_cube(f, &[1, 2]), bdd.cube([3]));
        assert_eq!(bdd.cofactor_cube(f, &[1, 3]), bdd.cube([2]));
        assert_eq!(bdd.cofactor_cube(f, &[2, 3]), bdd.cube([1]));
        assert_eq!(bdd.cofactor_cube(f, &[1, -2]), bdd.zero);
        assert_eq!(bdd.cofactor_cube(f, &[1, -3]), bdd.zero);
        assert_eq!(bdd.cofactor_cube(f, &[2, -3]), bdd.zero);
        assert_eq!(bdd.cofactor_cube(f, &[-1, 2]), bdd.zero);
        assert_eq!(bdd.cofactor_cube(f, &[-1, 3]), bdd.zero);
        assert_eq!(bdd.cofactor_cube(f, &[-2, 3]), bdd.zero);

        assert_eq!(bdd.cofactor_cube(f, &[1, 2, 3]), bdd.one);
        assert_eq!(bdd.cofactor_cube(f, &[1, 2, -3]), bdd.zero);
        assert_eq!(bdd.cofactor_cube(f, &[1, -2, 3]), bdd.zero);
        assert_eq!(bdd.cofactor_cube(f, &[1, -2, -3]), bdd.zero);
        assert_eq!(bdd.cofactor_cube(f, &[-1, 2, 3]), bdd.zero);
        assert_eq!(bdd.cofactor_cube(f, &[-1, 2, -3]), bdd.zero);
        assert_eq!(bdd.cofactor_cube(f, &[-1, -2, 3]), bdd.zero);
        assert_eq!(bdd.cofactor_cube(f, &[-1, -2, -3]), bdd.zero);

        assert_eq!(bdd.cofactor_cube(f, &[]), f);
        assert_eq!(bdd.cofactor_cube(bdd.one, &[1]), bdd.one);
        assert_eq!(bdd.cofactor_cube(bdd.zero, &[1]), bdd.zero);
        assert_eq!(bdd.cofactor_cube(bdd.one, &[-1]), bdd.one);
        assert_eq!(bdd.cofactor_cube(bdd.zero, &[-1]), bdd.zero);
    }

    impl Bdd {
        fn build_example(&self) -> Ref {
            let x1 = self.mk_var(1);
            let x2 = self.mk_var(2);
            let x3 = self.mk_var(3);

            // x1 ∨ (x2 ∧ x3)
            let f = self.apply_or(self.apply_and(x1, x2), x3);

            f
        }
    }

    #[test]
    fn test_constrain_base() {
        let bdd = Bdd::default();
        {
            let f = bdd.build_example();
            let g = bdd.one;
            let result = bdd.constrain(f, g);
            assert_eq!(result, f); // When g is 1, the result should be f.
        }
        {
            let f = bdd.build_example();
            let g = f;
            let result = bdd.constrain(f, g);
            assert_eq!(result, bdd.one); // When g is f, the result should be 1.
        }
        {
            let f = bdd.zero;
            let g = bdd.build_example();
            let result = bdd.constrain(f, g);
            assert_eq!(result, bdd.zero); // When f is 0, the result should be 0.
        }
    }

    // Somenzi, 1999
    #[test]
    fn test_constrain_example1() {
        let bdd = Bdd::default();

        let s = bdd.mk_node(3, -bdd.one, bdd.one);
        let p = bdd.mk_node(2, -s, s);
        let r = bdd.mk_node(2, s, bdd.one);
        let q = bdd.mk_node(2, -s, bdd.one);
        let t = bdd.mk_node(2, -bdd.one, s);

        println!("s = {}", bdd.to_bracket_string(s));
        println!("p = {}", bdd.to_bracket_string(p));
        println!("r = {}", bdd.to_bracket_string(r));
        println!("q = {}", bdd.to_bracket_string(q));
        println!("t = {}", bdd.to_bracket_string(t));

        let f = bdd.mk_node(1, -p, s);
        println!("f = {}", bdd.to_bracket_string(f));
        let g = bdd.mk_node(1, -r, q);
        println!("g = {}", bdd.to_bracket_string(g));
        let h = bdd.mk_node(1, -bdd.one, t);
        println!("h = {}", bdd.to_bracket_string(h));

        let fg = bdd.constrain(f, g);
        println!("f|g = {}", bdd.to_bracket_string(fg));

        assert_eq!(fg, h, "h = constrain(f, g)");
    }

    #[test]
    fn test_constrain_example2() {
        let bdd = Bdd::default();

        // f = x1*x3 + ~x1*(x2^x3)
        // g = x1*x2 + ~x2*~x3
        // h = f|g = x1*x2*x3
        // where:
        //   * is AND
        //   + is OR
        //   ^ is XOR
        //   ~ is NOT
        //   | is 'constrain'

        let x1 = bdd.mk_var(1);
        let x2 = bdd.mk_var(2);
        let x3 = bdd.mk_var(3);

        // f = x1*x3 + ~x1*(x2^x3)
        let f = bdd.apply_or(bdd.apply_and(x1, x3), bdd.apply_and(-x1, bdd.apply_xor(x2, x3)));

        // g = x1*x2 + ~x2*~x3
        let g = bdd.apply_or(bdd.apply_and(x1, x2), bdd.apply_and(-x2, -x3));

        // h = x1*x2*x3
        let h = bdd.cube([1, 2, 3]);

        // f|g == h
        let fg = bdd.constrain(f, g);
        assert_eq!(fg, h);
    }

    // Somenzi, 1999
    #[test]
    fn test_restrict() {
        let bdd = Bdd::default();

        let x = bdd.mk_var(1);
        let _y = bdd.mk_var(2);
        let z = bdd.mk_var(3);

        let s = bdd.mk_node(3, -bdd.one, bdd.one);
        let p = bdd.mk_node(2, -s, s);
        let r = bdd.mk_node(2, s, bdd.one);
        let q = bdd.mk_node(2, -s, bdd.one);
        let t = bdd.mk_node(2, -bdd.one, s);

        println!("s = {}", bdd.to_bracket_string(s));
        println!("p = {}", bdd.to_bracket_string(p));
        println!("r = {}", bdd.to_bracket_string(r));
        println!("q = {}", bdd.to_bracket_string(q));
        println!("t = {}", bdd.to_bracket_string(t));

        let f = bdd.mk_node(1, -p, s);
        println!("f = {}", bdd.to_bracket_string(f));
        let g = bdd.mk_node(1, -r, q);
        println!("g = {}", bdd.to_bracket_string(g));
        let h = bdd.apply_and(x, z);
        println!("h = {}", bdd.to_bracket_string(h));

        let fg = bdd.restrict(f, g);
        println!("f||g = {}", bdd.to_bracket_string(fg));
        assert_eq!(fg, h, "h = restrict(f, g)");
    }

    #[test]
    fn test_negation_in_ite_cache() {
        let bdd = Bdd::default();

        let x1 = bdd.mk_var(1);
        println!("x1 = {}", bdd.to_bracket_string(x1));
        let x2 = bdd.mk_var(2);
        println!("x2 = {}", bdd.to_bracket_string(x2));

        let f = bdd.apply_xor(x1, x2);
        println!("f = {}", bdd.to_bracket_string(f));
        let g = bdd.apply_xor(x1, x2);
        println!("g = {}", bdd.to_bracket_string(g));

        let f = bdd.apply_xor(x1, -x2);
        println!("f = {}", bdd.to_bracket_string(f));
        let g = bdd.apply_xor(x1, -x2);
        println!("g = {}", bdd.to_bracket_string(g));
        assert_eq!(f, g);
    }

    #[test]
    fn test_substitute() {
        let bdd = Bdd::default();

        let x1 = bdd.mk_var(1);
        let x2 = bdd.mk_var(2);
        let x3 = bdd.mk_var(3);

        let f = bdd.apply_or(bdd.apply_eq(x1, x2), x3);
        println!("f of size {} = {}", bdd.size(f), bdd.to_bracket_string(f));

        let f_x2_zero = bdd.substitute(f, 2, false); // f|x2<-0
        println!("f|x2<-0 of size {} = {}", bdd.size(f_x2_zero), bdd.to_bracket_string(f_x2_zero));

        let g = bdd.apply_or(-x1, x3);
        println!("g of size {} = {}", bdd.size(g), bdd.to_bracket_string(g));

        assert_eq!(f_x2_zero, g);
    }

    #[test]
    fn test_substitute_multi() {
        let bdd = Bdd::default();

        let x1 = bdd.mk_var(1);
        let x2 = bdd.mk_var(2);
        let x3 = bdd.mk_var(3);
        let x4 = bdd.mk_var(4);

        let values = HashMap::from([(bdd.variable(x2.index()), true), (bdd.variable(x4.index()), false)]);
        println!("values = {:?}", values);

        let f = bdd.apply_and_many([-x1, x2, x3, -x4]);
        println!("f of size {} = {}", bdd.size(f), bdd.to_bracket_string(f));

        let g = bdd.substitute_multi(f, &values); // result of f|(x2<-1,x4<-0)
        println!("g of size {} = {}", bdd.size(g), bdd.to_bracket_string(g));

        let h = bdd.apply_and(-x1, x3); // expected
        println!("h of size {} = {}", bdd.size(h), bdd.to_bracket_string(h));

        assert_eq!(g, h);
    }

    #[test]
    fn test_compose() {
        let bdd = Bdd::default();

        let x1 = bdd.mk_var(1);
        let x2 = bdd.mk_var(2);
        let x3 = bdd.mk_var(3);

        let f = bdd.apply_and(bdd.apply_eq(x1, x2), x3);
        println!("f of size {} = {}", bdd.size(f), bdd.to_bracket_string(f));

        let g = -bdd.apply_eq(x1, x2);
        println!("g of size {} = {}", bdd.size(g), bdd.to_bracket_string(g));

        let h = bdd.compose(f, bdd.variable(x3.index()), g);
        println!("h of size {} = {}", bdd.size(h), bdd.to_bracket_string(h));
        assert!(bdd.is_zero(h));
    }

    #[test]
    fn test_ite_constant() {
        let bdd = Bdd::default();

        let x1 = bdd.mk_var(1);
        let x2 = bdd.mk_var(2);

        let f = bdd.apply_and(x1, x2);
        println!("f = x1&x2 of size {} = {}", bdd.size(f), bdd.to_bracket_string(f));

        println!("is_implies(f, x1) = {}", bdd.is_implies(f, x1));
        println!("is_implies(f, x2) = {}", bdd.is_implies(f, x2));
        println!("is_implies(f, -x1) = {}", bdd.is_implies(f, -x1));
        println!("is_implies(f, -x2) = {}", bdd.is_implies(f, -x2));
        println!("is_implies(f, x1&x2 = {}", bdd.is_implies(f, bdd.apply_and(x1, x2)));
        println!("is_implies(f, x1|x2 = {}", bdd.is_implies(f, bdd.apply_or(x1, x2)));

        assert!(bdd.is_implies(f, x1));
        assert!(bdd.is_implies(f, x2));
        assert!(!bdd.is_implies(f, -x1));
        assert!(!bdd.is_implies(f, -x2));
        assert!(bdd.is_implies(f, bdd.apply_and(x1, x2)));
        assert!(bdd.is_implies(f, bdd.apply_or(x1, x2)));
        assert!(bdd.is_implies(x1, bdd.one));
        assert!(bdd.is_implies(x2, bdd.one));
        assert!(bdd.is_implies(bdd.zero, x1));
        assert!(bdd.is_implies(bdd.zero, x2));
        assert!(bdd.is_implies(x1, bdd.apply_or(x1, x2)));
        assert!(bdd.is_implies(x2, bdd.apply_or(x1, x2)));
    }

    #[test]
    fn test_one_sat() {
        let bdd = Bdd::default();

        let f = bdd.cube([1, -2, -3]);
        println!("f = {} of size {}", f, bdd.size(f));
        let model = bdd.one_sat(f);
        println!("model = {:?}", model);
        assert_eq!(model, Some(vec![1, -2, -3]));

        let g = bdd.apply_and(f, -bdd.cube(model.unwrap()));
        println!("g = {} of size {}", g, bdd.size(g));
        let model = bdd.one_sat(g);
        println!("model = {:?}", model);
        assert_eq!(model, None);
    }

    #[test]
    fn test_one_sat_many() {
        let bdd = Bdd::default();

        let mut all_cubes = Vec::new();

        for &s1 in &[1, -1] {
            for &s2 in &[1, -1] {
                for &s3 in &[1, -1] {
                    all_cubes.push([1 * s1, 2 * s2, 3 * s3]);
                }
            }
        }

        for cube in all_cubes {
            println!("Testing cube: {:?}", cube);

            let f = bdd.cube(cube);
            println!("f = {} of size {}", f, bdd.size(f));
            let model = bdd.one_sat(f);
            println!("model = {:?}", model);
            assert_eq!(model, Some(cube.to_vec()));

            let g = bdd.apply_and(f, -bdd.cube(model.unwrap()));
            println!("g = {} of size {}", g, bdd.size(g));
            let model = bdd.one_sat(g);
            println!("model = {:?}", model);
            assert_eq!(model, None);
        }
    }

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

    #[test]
    fn test_to_bracket_string_terminal() {
        let bdd = Bdd::default();

        println!("zero = {}", bdd.to_bracket_string(bdd.zero));
        assert_eq!(bdd.to_bracket_string(bdd.zero), "⊥");

        println!("one = {}", bdd.to_bracket_string(bdd.one));
        assert_eq!(bdd.to_bracket_string(bdd.one), "⊤");
    }

    #[test]
    fn test_to_bracket_string_1() {
        let bdd = Bdd::default();

        // x1 ∧ x2
        let x1 = bdd.mk_var(1);
        let x2 = bdd.mk_var(2);
        let f = bdd.apply_and(x1, x2);
        println!("f = x1 ∧ x2 = {}", bdd.to_bracket_string(f));
        assert_eq!(bdd.to_bracket_string(f), "@4:(x1, @3:(x2, ⊤, ⊥), ⊥)");
    }

    #[test]
    fn test_to_bracket_string_2() {
        let bdd = Bdd::default();

        // ~x1 ∨ (~x2 ∧ x3)
        let x1 = bdd.mk_var(1);
        let x2 = bdd.mk_var(2);
        let x3 = bdd.mk_var(3);
        let f = bdd.apply_or(-x1, bdd.apply_and(-x2, x3));
        println!("f = ~x1 ∨ (~x2 ∧ x3) = {}", bdd.to_bracket_string(f));
        assert_eq!(bdd.to_bracket_string(f), "~@6:(x1, @5:(x2, ⊤, ~@4:(x3, ⊤, ⊥)), ⊥)");
    }
}
