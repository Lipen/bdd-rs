use std::collections::HashMap;
use std::fmt::Debug;

use crate::gate::Gate;
use crate::signal::Signal;

#[derive(Debug)]
pub struct Network {
    num_inputs: usize,
    outputs: Vec<Signal>,
    gates: HashMap<u32, Gate>,
}

impl Default for Network {
    fn default() -> Self {
        Self::new()
    }
}

impl Network {
    pub fn new() -> Self {
        Self {
            num_inputs: 0,
            outputs: Vec::new(),
            gates: HashMap::new(),
        }
    }

    pub fn num_inputs(&self) -> usize {
        self.num_inputs
    }

    pub fn num_outputs(&self) -> usize {
        self.outputs.len()
    }

    pub fn num_gates(&self) -> usize {
        self.gates.len()
    }

    // pub fn input(&self, input: u32) -> Signal {
    //     assert!(input < self.num_inputs() as u32);
    //     Signal::from_input(input)
    // }

    pub fn gate(&self, var: u32) -> Option<&Gate> {
        self.gates.get(&var)
    }

    pub fn outputs(&self) -> &[Signal] {
        &self.outputs
    }

    pub fn add_input(&mut self) -> Signal {
        let input = Signal::from_input(self.num_inputs as u32);
        self.num_inputs += 1;
        input
    }

    pub fn add_output(&mut self, output: Signal) {
        self.outputs.push(output);
    }

    pub fn add_gate(&mut self, var: u32, gate: Gate) -> Signal {
        self.gates.insert(var, gate);
        Signal::from_var(var)
    }

    // TODO
    // pub fn and(&mut self, a: Signal, b: Signal) -> Signal {
    //     let gate = Gate::and(a, b);
    //     let output = gate.output();
    //     self.gates.push(gate);
    //     output
    // }
}
