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
}
