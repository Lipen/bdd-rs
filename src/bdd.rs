use std::cmp::{min, Ordering};
use std::fmt::Debug;

use log::debug;

use crate::cache::Cache;
use crate::reference::Ref;
use crate::table::Table;
use crate::utils::{pairing3, MyHash};

#[derive(Debug, Copy, Clone, Eq, PartialEq)]
struct Triple {
    variable: u32,
    low: Ref,
    high: Ref,
}

#[allow(clippy::derivable_impls)]
impl Default for Triple {
    fn default() -> Self {
        Self {
            variable: 0,
            low: Ref::zero(),
            high: Ref::zero(),
        }
    }
}

impl MyHash for Triple {
    fn hash(&self) -> u64 {
        pairing3(
            self.variable as u64,
            self.low.unsigned() as u64,
            self.high.unsigned() as u64,
        )
    }
}

type Storage = Table<Triple>;

impl Storage {
    pub fn variable(&self, index: usize) -> u32 {
        self.value(index).variable
    }
    pub fn low(&self, index: usize) -> Ref {
        self.value(index).low
    }
    pub fn high(&self, index: usize) -> Ref {
        self.value(index).high
    }
}

pub struct Bdd {
    storage: Storage,
    ite_cache: Cache<(Ref, Ref, Ref), Ref>,
    constrain_cache: Cache<(Ref, Ref), Ref>,
    pub zero: Ref,
    pub one: Ref,
}

impl Bdd {
    pub fn new(storage_bits: usize) -> Self {
        assert!(
            storage_bits <= 31,
            "Storage bits should be in the range 0..=31"
        );

        let cache_bits = min(storage_bits, 20);

        let mut storage = Storage::new(storage_bits);

        // Allocate the terminal node:
        let one = storage.alloc();
        assert_eq!(one, 1); // Make sure the terminal node is (1).
        let one = Ref::positive(one as u32);
        let zero = -one;

        Self {
            storage,
            ite_cache: Cache::new(cache_bits),
            constrain_cache: Cache::new(cache_bits),
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
        f.debug_struct("Bdd")
            .field("capacity", &self.storage.capacity())
            .field("size", &self.storage.size())
            .field("real_size", &self.storage.real_size())
            .finish()
    }
}

impl Bdd {
    pub fn variable(&self, index: u32) -> u32 {
        self.storage.variable(index as usize)
    }
    pub fn low(&self, index: u32) -> Ref {
        self.storage.low(index as usize)
    }
    pub fn high(&self, index: u32) -> Ref {
        self.storage.high(index as usize)
    }
    pub fn next(&self, index: u32) -> usize {
        self.storage.next(index as usize)
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

    pub fn mk_node(&mut self, v: u32, low: Ref, high: Ref) -> Ref {
        debug!("mk(v = {}, low = {}, high = {})", v, low, high);

        assert_ne!(v, 0, "Variable index should not be zero");

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

        let i = self.storage.put(Triple {
            variable: v,
            low,
            high,
        });
        Ref::positive(i as u32)
    }

    pub fn mk_var(&mut self, v: u32) -> Ref {
        assert_ne!(v, 0, "Variable index should not be zero");
        self.mk_node(v, self.zero, self.one)
    }

    pub fn cube(&mut self, literals: &[i32]) -> Ref {
        debug!("cube(literals = {:?})", literals);
        let mut current = self.one;
        let mut literals = literals.to_vec();
        literals.sort_by_key(|&v| v.abs());
        literals.reverse();
        for lit in literals {
            assert_ne!(lit, 0, "Variable index should not be zero");
            current = if lit < 0 {
                self.mk_node(-lit as u32, current, self.zero)
            } else {
                self.mk_node(lit as u32, self.zero, current)
            }
        }
        current
    }

    pub fn top_cofactors(&self, node: Ref, v: u32) -> (Ref, Ref) {
        assert_ne!(v, 0, "Variable index should not be zero");

        let i = node.index();
        if self.is_terminal(node) || v < self.variable(i) {
            return (node, node);
        }
        assert_eq!(v, self.variable(i));
        if node.is_negated() {
            (-self.low(i), -self.high(i))
        } else {
            (self.low(i), self.high(i))
        }
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

        if let Some(&res) = self.ite_cache.get(&(f, g, h)) {
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
            let u = xu.unsigned_abs();
            let (f0, f1) = self.top_cofactors(f, u);
            return if xu > 0 { f1 } else { f0 };
        }

        let t = self.variable(f.index());
        let xu = cube[0];
        let u = xu.unsigned_abs();

        match t.cmp(&u) {
            Ordering::Greater => self.cofactor_cube(f, &cube[1..]),
            Ordering::Equal => {
                let (f0, f1) = self.top_cofactors(f, u);
                if xu > 0 {
                    self.cofactor_cube(f1, &cube[1..])
                } else {
                    self.cofactor_cube(f0, &cube[1..])
                }
            }
            Ordering::Less => {
                let (f0, f1) = self.top_cofactors(f, t);
                let low = self.cofactor_cube(f0, cube);
                let high = self.cofactor_cube(f1, cube);
                self.mk_node(t, low, high)
            }
        }
    }

    pub fn constrain(&mut self, f: Ref, g: Ref) -> Ref {
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

        if let Some(&res) = self.constrain_cache.get(&(f, g)) {
            debug!("cache: constrain(f = {}, c = {}) -> {}", f, g, res);
            return res;
        }

        // TODO: is it necessary to compute min var, or we can just use var(g)?
        let i = self.variable(f.index());
        let j = self.variable(g.index());
        let v = i.min(j);
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
        debug!("computed: constrain(f = {}, c = {}) -> {}", f, g, res);

        self.constrain_cache.insert((f, g), res);
        res
    }

    pub fn to_bracket_string(&self, node: Ref) -> String {
        if self.is_zero(node) {
            return "(0)".to_string();
        } else if self.is_one(node) {
            return "(1)".to_string();
        }

        assert_ne!(node.index(), 0);

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
    fn test_var() {
        let mut bdd = Bdd::default();

        let x = bdd.mk_var(1);

        assert_eq!(bdd.variable(x.index()), 1);
        assert_eq!(bdd.high_node(x), bdd.one);
        assert_eq!(bdd.low_node(x), bdd.zero);
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
        let mut bdd = Bdd::default();

        let x1 = bdd.mk_var(1);
        let x2 = bdd.mk_var(2);
        let x3 = bdd.mk_var(3);

        let x1_and_x2 = bdd.apply_and(x1, x2);
        let x1_and_x2_and_3 = bdd.apply_and(x1_and_x2, x3);
        let cube = bdd.cube(&[1, 2, 3]);
        assert_eq!(x1_and_x2_and_3, cube);

        let x1_and_not_x2 = bdd.apply_and(x1, -x2);
        let x1_and_not_x2_and_not_x3 = bdd.apply_and(x1_and_not_x2, -x3);
        let cube = bdd.cube(&[1, -2, -3]);
        assert_eq!(x1_and_not_x2_and_not_x3, cube);
    }

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

    impl Bdd {
        fn build_example(&mut self) -> Ref {
            let x1 = self.mk_var(1);
            let x2 = self.mk_var(2);
            let x3 = self.mk_var(3);

            let t = self.apply_and(x1, x2);
            let f = self.apply_or(t, x3);

            f
        }
    }

    #[test]
    fn test_constrain_base() {
        let mut bdd = Bdd::default();
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

    #[test]
    fn test_constrain_example1() {
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

    #[test]
    fn test_constrain_example2() {
        let mut bdd = Bdd::default();

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
        let x1_and_x3 = bdd.apply_and(x1, x3);
        let x2_xor_x3 = bdd.apply_xor(x2, x3);
        let not_x1_and_x2_xor_x3 = bdd.apply_and(-x1, x2_xor_x3);
        let f = bdd.apply_or(x1_and_x3, not_x1_and_x2_xor_x3);

        // g = x1*x2 + ~x2*~x3
        let x1_and_x2 = bdd.apply_and(x1, x2);
        let not_x2_and_not_x3 = bdd.apply_and(-x2, -x3);
        let g = bdd.apply_or(x1_and_x2, not_x2_and_not_x3);

        // h = x1*x2*x3
        let h = bdd.cube(&[1, 2, 3]);

        // f|g == h
        let fg = bdd.constrain(f, g);
        assert_eq!(fg, h);
    }
}
