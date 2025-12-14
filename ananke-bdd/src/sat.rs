use std::collections::HashMap;

use num_bigint::{BigUint, ToBigUint};

use crate::bdd::Bdd;
use crate::reference::Ref;
use crate::types::Lit;

impl Bdd {
    /// Returns one satisfying assignment for the BDD, if any exists.
    ///
    /// The assignment is returned as a vector of literals.
    /// Use `lit.is_positive()` to check if the variable is true,
    /// or `lit.to_dimacs()` to get a signed integer representation.
    ///
    /// Returns `None` if the BDD represents the constant false function.
    pub fn one_sat(&self, node: Ref) -> Option<Vec<Lit>> {
        if self.is_zero(node) {
            return None;
        }

        let mut path = Vec::new();
        let mut current = node;

        // Walk down the BDD, always picking a satisfying branch
        while !self.is_one(current) {
            let var = self.variable(current.id());
            let high = self.high_node(current);
            let low = self.low_node(current);

            // Prefer high branch if satisfiable, otherwise take low
            if !self.is_zero(high) {
                path.push(var.pos());
                current = high;
            } else {
                path.push(var.neg());
                current = low;
            }
        }

        Some(path)
    }

    pub fn sat_count(&self, node: Ref, num_vars: usize) -> BigUint {
        let mut cache = HashMap::new();
        let two = 2.to_biguint().unwrap();
        let max = two.pow(num_vars as u32);
        self._sat_count(node, &max, &mut cache)
    }

    fn _sat_count(&self, node: Ref, max: &BigUint, cache: &mut HashMap<Ref, BigUint>) -> BigUint {
        // log::info!("_sat_count(node={}, max={})", node, max);

        if self.is_zero(node) {
            return BigUint::ZERO;
        } else if self.is_one(node) {
            return max.clone();
        }

        if let Some(count) = cache.get(&node) {
            // log::info!("_sat_count(node={}) -> {} (cached)", node, count);
            return count.clone();
        }

        let low = self.low(node.id());
        let high = self.high(node.id());

        let count_low = self._sat_count(low, max, cache);
        let count_high = self._sat_count(high, max, cache);

        let count: BigUint = (count_low.clone() + count_high.clone()) >> 1;
        let count = if node.is_negated() { max - count } else { count };

        cache.insert(node, count.clone());
        // log::info!("_sat_count(node={} (var={}, low={}, high={})) -> ({} + {}) / 2 =  {}", node, self.variable(node.index()), self.low(node.index()), self.high(node.index()), count_low, count_high, count);
        count
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_one_sat() {
        let bdd = Bdd::default();

        let f = bdd.mk_cube([1, -2, -3]);
        println!("f = {} of size {}", f, bdd.size(f));
        let model = bdd.one_sat(f);
        println!("model = {:?}", model);
        let expected: Vec<Lit> = vec![1, -2, -3].into_iter().map(Lit::from_dimacs).collect();
        assert_eq!(model, Some(expected));

        let g = bdd.apply_and(f, -bdd.mk_cube(model.unwrap()));
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

            let f = bdd.mk_cube(cube);
            println!("f = {} of size {}", f, bdd.size(f));
            let model = bdd.one_sat(f);
            println!("model = {:?}", model);
            let expected: Vec<Lit> = cube.into_iter().map(Lit::from_dimacs).collect();
            assert_eq!(model, Some(expected));

            let g = bdd.apply_and(f, -bdd.mk_cube(model.unwrap()));
            println!("g = {} of size {}", g, bdd.size(g));
            let model = bdd.one_sat(g);
            println!("model = {:?}", model);
            assert_eq!(model, None);
        }
    }

    #[test]
    fn test_sat_count_terminal() {
        let bdd = Bdd::default();

        assert_eq!(bdd.sat_count(bdd.zero(), 1), 0.to_biguint().unwrap());
        assert_eq!(bdd.sat_count(bdd.zero(), 2), 0.to_biguint().unwrap());
        assert_eq!(bdd.sat_count(bdd.zero(), 3), 0.to_biguint().unwrap());

        assert_eq!(bdd.sat_count(bdd.one(), 1), 2.to_biguint().unwrap());
        assert_eq!(bdd.sat_count(bdd.one(), 2), 4.to_biguint().unwrap());
        assert_eq!(bdd.sat_count(bdd.one(), 3), 8.to_biguint().unwrap());
    }

    #[test]
    fn test_sat_count_var() {
        let bdd = Bdd::default();

        let x1 = bdd.mk_var(1);
        assert_eq!(bdd.sat_count(x1, 1), 1.to_biguint().unwrap());
        assert_eq!(bdd.sat_count(x1, 2), 2.to_biguint().unwrap());
        assert_eq!(bdd.sat_count(x1, 3), 4.to_biguint().unwrap());

        let x2 = bdd.mk_var(2);
        assert_eq!(bdd.sat_count(x2, 1), 1.to_biguint().unwrap());
        assert_eq!(bdd.sat_count(x2, 2), 2.to_biguint().unwrap());
        assert_eq!(bdd.sat_count(x2, 3), 4.to_biguint().unwrap());
    }

    #[test]
    fn test_sat_count_cube() {
        let bdd = Bdd::default();

        let f = bdd.mk_cube([1, 2]);
        println!("f = {} of size {}", f, bdd.size(f));
        println!("sat_count(f, 2) = {}", bdd.sat_count(f, 2));

        assert_eq!(bdd.sat_count(f, 2), 1.to_biguint().unwrap());
        assert_eq!(bdd.sat_count(f, 3), 2.to_biguint().unwrap());
        assert_eq!(bdd.sat_count(f, 4), 4.to_biguint().unwrap());
        assert_eq!(bdd.sat_count(f, 5), 8.to_biguint().unwrap());
    }

    #[test]
    fn test_sat_count_clause() {
        let bdd = Bdd::default();

        let f = bdd.mk_clause([1, 2]);
        println!("f = {} of size {}", f, bdd.size(f));
        println!("sat_count(f, 2) = {}", bdd.sat_count(f, 2));

        assert_eq!(bdd.sat_count(f, 2), 3.to_biguint().unwrap());
        assert_eq!(bdd.sat_count(f, 3), 6.to_biguint().unwrap());
        assert_eq!(bdd.sat_count(f, 4), 12.to_biguint().unwrap());

        println!("Paths:");
        for path in bdd.paths(f) {
            println!("- {:?}", path);
        }
    }

    #[test]
    fn test_sat_count_not_cube() {
        let bdd = Bdd::default();

        let f = -bdd.mk_cube([1, 2]);
        println!("f = {} of size {}", f, bdd.size(f));
        println!("sat_count(f, 2) = {}", bdd.sat_count(f, 2));

        assert_eq!(bdd.sat_count(f, 2), 3.to_biguint().unwrap());
        assert_eq!(bdd.sat_count(f, 3), 6.to_biguint().unwrap());
        assert_eq!(bdd.sat_count(f, 4), 12.to_biguint().unwrap());

        println!("Paths:");
        for path in bdd.paths(f) {
            println!("- {:?}", path);
        }
    }
}
