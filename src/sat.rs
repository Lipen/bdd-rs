use std::collections::HashMap;

use num_bigint::{BigUint, ToBigUint};

use crate::bdd::Bdd;
use crate::reference::Ref;

impl Bdd {
    pub fn one_sat(&self, node: Ref) -> Option<Vec<i32>> {
        self._one_sat(node, vec![])
    }

    fn _one_sat(&self, node: Ref, path: Vec<i32>) -> Option<Vec<i32>> {
        if self.is_zero(node) {
            return None;
        } else if self.is_one(node) {
            return Some(path);
        }

        let v = self.variable(node.index()) as i32;

        let high = self.high_node(node);
        let mut path_high = path.clone();
        path_high.push(v);
        if let Some(res) = self._one_sat(high, path_high) {
            return Some(res);
        }

        let low = self.low_node(node);
        let mut path_low = path;
        path_low.push(-v);
        self._one_sat(low, path_low)
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

        let low = self.low(node.index());
        let high = self.high(node.index());

        let count_low = self._sat_count(low, max, cache);
        let count_high = self._sat_count(high, max, cache);

        let count: BigUint = (count_low.clone() + count_high.clone()) >> 1;
        let count = if node.is_negated() {
            max - count
        } else {
            count
        };

        cache.insert(node, count.clone());
        // log::info!("_sat_count(node={} (var={}, low={}, high={})) -> ({} + {}) / 2 =  {}", node, self.variable(node.index()), self.low(node.index()), self.high(node.index()), count_low, count_high, count);
        count
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_sat_count_terminal() {
        let bdd = Bdd::default();

        assert_eq!(bdd.sat_count(bdd.zero, 1), 0.to_biguint().unwrap());
        assert_eq!(bdd.sat_count(bdd.zero, 2), 0.to_biguint().unwrap());
        assert_eq!(bdd.sat_count(bdd.zero, 3), 0.to_biguint().unwrap());

        assert_eq!(bdd.sat_count(bdd.one, 1), 2.to_biguint().unwrap());
        assert_eq!(bdd.sat_count(bdd.one, 2), 4.to_biguint().unwrap());
        assert_eq!(bdd.sat_count(bdd.one, 3), 8.to_biguint().unwrap());
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

        let f = bdd.cube([1, 2]);
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

        let f = bdd.clause([1, 2]);
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

        let f = -bdd.cube([1, 2]);
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
