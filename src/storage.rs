use crate::node::Node;
use crate::reference::Ref;
use crate::table::Table;
use crate::types::Var;

pub type Storage = Table<Node>;

impl Storage {
    pub fn node(&self, index: usize) -> &Node {
        self.value(index)
    }
    pub fn variable(&self, index: usize) -> Var {
        self.value(index).variable
    }
    pub fn low(&self, index: usize) -> Ref {
        self.value(index).low
    }
    pub fn high(&self, index: usize) -> Ref {
        self.value(index).high
    }
}
