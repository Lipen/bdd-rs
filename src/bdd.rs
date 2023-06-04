use std::fmt::Debug;

use log::debug;

use crate::cache::OpCache;
use crate::reference::Ref;
use crate::storage::Storage;
use crate::utils::pairing3;

pub struct Bdd {
    storage_bits: usize,
    buckets_bits: usize,
    cache_bits: usize,
    bitmask: u64,
    storage: Storage,
    buckets: Vec<usize>,
    ite_cache: OpCache<(Ref, Ref, Ref), Ref>,
    constrain_cache: OpCache<(Ref, Ref), Ref>,
    pub zero: Ref,
    pub one: Ref,
}

impl Bdd {
    pub fn new(storage_bits: usize) -> Self {
        assert!(
            storage_bits <= 31,
            "Storage bits should be in the range 0..=31"
        );

        let buckets_bits = storage_bits;
        let cache_bits = storage_bits;
        let mut storage = Storage::new(1 << storage_bits);
        let mut buckets = vec![0; 1 << buckets_bits];

        // Allocate and store the terminal node in the 0th bucket:
        buckets[0] = storage.alloc();
        assert_eq!(buckets[0], 1); // Make sure the terminal node is (1).

        Self {
            storage_bits,
            buckets_bits,
            cache_bits: 20,
            bitmask: (1 << buckets_bits) - 1,
            storage,
            buckets,
            ite_cache: OpCache::new(cache_bits),
            constrain_cache: OpCache::new(cache_bits),
            zero: Ref::new(-1),
            one: Ref::new(1),
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
        f.debug_struct("Bdd")
            .field("storage_bits", &self.storage_bits)
            .field("buckets_bits", &self.buckets_bits)
            .field("cache_bits", &self.cache_bits)
            .finish()
    }
}

impl Bdd {
    // TODO: change Ref::index from usize to u32
    pub fn variable(&self, index: usize) -> u32 {
        self.storage.variable(index)
    }
    pub fn low(&self, index: usize) -> Ref {
        Ref::new(self.storage.low(index))
    }
    pub fn high(&self, index: usize) -> Ref {
        Ref::new(self.storage.high(index))
    }
    pub fn next(&self, index: usize) -> usize {
        self.storage.next(index)
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

    fn lookup(&self, v: u32, low: Ref, high: Ref) -> usize {
        (pairing3(v as u64, low.as_lit() as u64, high.as_lit() as u64) & self.bitmask) as usize
    }

    pub fn mk_node(&mut self, v: u32, low: Ref, high: Ref) -> Ref {
        debug!("mk(v = {}, low = {}, high = {})", v, low, high);

        assert_ne!(v, 0, "Variable index not be zero");

        // Handle canonicity
        if high.is_negated() {
            debug!("mk: restoring canonicity");
            return -self.mk_node(v, -low, -high);
        }

        // Handle duplicates
        if low == high {
            debug!("mk: duplicates {} == {}", low, high);
            return low;
        }

        let bucket_index = self.lookup(v, low, high);
        debug!(
            "mk: bucketIndex for ({}, {}, {}) is {}",
            v, low, high, bucket_index
        );
        let mut index = self.buckets[bucket_index];

        if index == 0 {
            // Create new node and put it into the bucket
            let i = self.storage.add(v, low.get(), high.get());
            self.buckets[bucket_index] = i;
            let node = Ref::new(i as i32);
            debug!("mk: created new node {}", node);
            return node;
        }

        loop {
            assert!(index > 0);

            if self.variable(index) == v && self.low(index) == low && self.high(index) == high {
                // The node already exists
                let node = Ref::new(index as i32);
                debug!("mk: node {} already exists", node);
                return node;
            }

            let next = self.next(index);

            if next == 0 {
                // Create new node and append it to the bucket
                let i = self.storage.add(v, low.get(), high.get());
                self.storage.set_next(index, i);
                let node = Ref::new(i as i32);
                debug!("mk: created new node {} after {}", node, index);
                return node;
            } else {
                // Go to the next node in the bucket
                debug!("mk: iterating over the bucket to {}", next);
                index = next;
            }
        }
    }

    pub fn mk_var(&mut self, v: u32) -> Ref {
        assert_ne!(v, 0, "Variable index not be zero");
        self.mk_node(v, self.zero, self.one)
    }

    pub fn top_cofactors(&self, node: Ref, v: u32) -> (Ref, Ref) {
        assert_ne!(v, 0, "Variable index not be zero");

        let i = node.index();
        if self.is_terminal(node) || v < self.variable(i) {
            return (node, node);
        }
        assert_eq!(v, self.variable(i));
        let res = if node.is_negated() {
            (-self.low(i), -self.high(i))
        } else {
            (self.low(i), self.high(i))
        };
        debug!(
            "top_cofactors(node = {}, v = {}) -> ({}, {})",
            node, v, res.0, res.1
        );
        res
    }

    /// Apply the ITE operation to the arguments.
    ///
    /// ```text
    /// ITE(x, y, z) = (x ∧ y) ∨ (¬x ∧ z)
    /// ```
    ///
    /// # Examples
    ///
    /// ```
    /// use bdd_rs::bdd::Bdd;
    ///
    /// let mut bdd = Bdd::default();
    /// let x = bdd.mk_var(1);
    /// let y = bdd.mk_var(2);
    /// let z = bdd.mk_var(3);
    /// let f = bdd.apply_ite(x, y, z);
    /// assert_eq!(f, bdd.mk_node(bdd.variable(x.index()), z, y));
    /// let  x_and_y = bdd.apply_and(x, y);
    /// let  not_x_and_z = bdd.apply_and(-x, z);
    /// assert_eq!(f, bdd.apply_or(x_and_y, not_x_and_z));
    /// ```
    pub fn apply_ite(&mut self, f: Ref, g: Ref, h: Ref) -> Ref {
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

        let (f, g, h) = (f, g, h);

        if let Some(res) = self.ite_cache.get((f, g, h)) {
            let res = if n { -res } else { res };
            debug!(
                "cache: apply_ite(f = {}, g = {}, h = {}) -> {}",
                f, g, h, res
            );
            return res;
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
        let res = if n { -res } else { res };
        debug!(
            "computed: apply_ite(f = {}, g = {}, h = {}) -> {}",
            f, g, h, res
        );

        self.ite_cache.insert((f, g, h), res);
        res
    }

    pub fn apply_and(&mut self, u: Ref, v: Ref) -> Ref {
        debug!("apply_and(u = {}, v = {})", u, v);
        self.apply_ite(u, v, self.zero)
    }

    pub fn apply_or(&mut self, u: Ref, v: Ref) -> Ref {
        debug!("apply_or(u = {}, v = {})", u, v);
        self.apply_ite(u, self.one, v)
    }

    pub fn apply_xor(&mut self, u: Ref, v: Ref) -> Ref {
        debug!("apply_xor(u = {}, v = {})", u, v);
        self.apply_ite(u, -v, v)
    }

    pub fn apply_eq(&mut self, u: Ref, v: Ref) -> Ref {
        debug!("apply_eq(u = {}, v = {})", u, v);
        self.apply_ite(u, v, -v)
    }

    pub fn cofactor_cube(&mut self, f: Ref, cube: &[i32]) -> Ref {
        debug!("cofactor_cube(f = {}, cube = {:?})", f, cube);

        if cube.len() == 1 {
            let xu = cube[0];
            let u = xu.abs() as u32;
            let (f0, f1) = self.top_cofactors(f, u);
            return if xu > 0 { f1 } else { f0 };
        }

        let t = self.variable(f.index());
        let xu = cube[0];
        let u = xu.abs() as u32;

        if t > u {
            self.cofactor_cube(f, &cube[1..])
        } else if t == u {
            let (f0, f1) = self.top_cofactors(f, u);
            if xu > 0 {
                self.cofactor_cube(f1, &cube[1..])
            } else {
                self.cofactor_cube(f0, &cube[1..])
            }
        } else if t < u {
            let (f0, f1) = self.top_cofactors(f, t);
            let low = self.cofactor_cube(f0, cube);
            let high = self.cofactor_cube(f1, cube);
            self.mk_node(t, low, high)
        } else {
            unreachable!()
        }
    }

    pub fn constrain(&mut self, f: Ref, c: Ref) -> Ref {
        debug!("constrain(f = {}, c = {})", f, c);

        if self.is_zero(c) {
            panic!("constrain(f, 0) is not allowed");
        }
        if self.is_one(c) {
            debug!("c is one");
            return f;
        }
        if self.is_terminal(f) {
            debug!("f is terminal");
            return f;
        }

        if let Some(res) = self.constrain_cache.get((f, c)) {
            debug!("cache: constrain(f = {}, c = {}) -> {}", f, c, res);
            return res;
        }

        let v = self.variable(c.index());
        let (f0, f1) = self.top_cofactors(f, v);
        let (c0, c1) = self.top_cofactors(c, v);

        if self.is_zero(c0) {
            debug!("c0 is zero");
            return self.constrain(f1, c1);
        }
        if self.is_zero(c1) {
            debug!("c1 is zero");
            return self.constrain(f0, c0);
        }
        if f0 == f1 {
            debug!("f0 == f1");
            let low = self.constrain(f, c0);
            let high = self.constrain(f, c1);
            return self.mk_node(v, low, high);
        }

        let low = self.constrain(f0, c0);
        let high = self.constrain(f1, c1);
        let res = self.mk_node(v, low, high);
        debug!("computed: constrain(f = {}, c = {}) -> {}", f, c, res);

        self.constrain_cache.insert((f, c), res);
        res
    }

    pub fn to_bracket_string(&self, node: Ref) -> String {
        if self.is_zero(node) {
            return format!("{}:(0)", node);
        } else if self.is_one(node) {
            return format!("{}:(1)", node);
        }

        let v = self.variable(node.index());
        let low = self.low_node(node);
        let high = self.high_node(node);

        format!(
            "{}:(x{}, {}, {})",
            node,
            v,
            self.to_bracket_string(high),
            self.to_bracket_string(low)
        )
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_apply_ite() {
        let mut bdd = Bdd::default();

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
        let mut bdd = Bdd::default();

        let x1 = bdd.mk_var(1);
        let x2 = bdd.mk_var(2);

        let f = bdd.apply_and(x1, x2);
        let cube = vec![1, 2];
        assert_eq!(bdd.cofactor_cube(f, &cube), bdd.one);
        let cube = vec![1, -2];
        assert_eq!(bdd.cofactor_cube(f, &cube), bdd.zero);
        let cube = vec![-1, 2];
        assert_eq!(bdd.cofactor_cube(f, &cube), bdd.zero);
        let cube = vec![-1, -2];
        assert_eq!(bdd.cofactor_cube(f, &cube), bdd.zero);
    }

    #[test]
    fn test_constrain() {
        let mut bdd = Bdd::default();

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
}
