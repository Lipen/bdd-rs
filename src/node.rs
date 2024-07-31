use crate::reference::Ref;
use crate::utils::MyHash;

#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub struct Node {
    pub variable: u32,
    pub low: Ref,
    pub high: Ref,
}

impl Default for Node {
    fn default() -> Self {
        Self {
            variable: 0,
            low: Ref::ZERO,
            high: Ref::ZERO,
        }
    }
}

impl MyHash for Node {
    fn hash(&self) -> u64 {
        let x = self.variable as u64;
        let y = MyHash::hash(&self.low);
        let z = MyHash::hash(&self.high);
        MyHash::hash(&(x, y, z))
    }
}
