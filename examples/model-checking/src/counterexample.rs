//! Counterexample generation for model checking.
//!
//! When a property fails, a counterexample explains *why*.
//! This module generates:
//! - Linear traces for safety violations (finite paths to bad states)
//! - Lasso-shaped traces for liveness violations (stem + loop)

use std::collections::HashMap;
use std::fmt;
use std::rc::Rc;

use bdd_rs::bdd::Bdd;
use bdd_rs::reference::Ref;
use bdd_rs::types::Var as BddVar;

use crate::transition::{TransitionSystem, Var};

/// A state in a counterexample trace.
#[derive(Debug, Clone)]
pub struct State {
    /// Variable assignments in this state
    pub assignments: HashMap<String, bool>,
}

impl State {
    pub fn new() -> Self {
        State {
            assignments: HashMap::new(),
        }
    }

    pub fn get(&self, var: &str) -> Option<bool> {
        self.assignments.get(var).copied()
    }

    pub fn set(&mut self, var: String, value: bool) {
        self.assignments.insert(var, value);
    }
}

impl Default for State {
    fn default() -> Self {
        Self::new()
    }
}

impl fmt::Display for State {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut vars: Vec<_> = self.assignments.iter().collect();
        vars.sort_by_key(|(k, _)| *k);

        let parts: Vec<String> = vars.iter().map(|(k, v)| format!("{}={}", k, if **v { "1" } else { "0" })).collect();

        write!(f, "{{{}}}", parts.join(", "))
    }
}

/// A counterexample trace.
#[derive(Debug, Clone)]
pub enum Counterexample {
    /// Linear trace (for safety properties): sequence of states ending in violation
    Linear(Vec<State>),
    /// Lasso trace (for liveness properties): stem followed by a loop
    Lasso {
        /// States before the loop
        stem: Vec<State>,
        /// States in the loop (repeats forever)
        loop_states: Vec<State>,
    },
}

impl Counterexample {
    /// Get the length of the counterexample
    pub fn len(&self) -> usize {
        match self {
            Counterexample::Linear(states) => states.len(),
            Counterexample::Lasso { stem, loop_states } => stem.len() + loop_states.len(),
        }
    }

    /// Check if empty
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }
}

impl fmt::Display for Counterexample {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Counterexample::Linear(states) => {
                writeln!(f, "Linear counterexample ({} states):", states.len())?;
                for (i, state) in states.iter().enumerate() {
                    writeln!(f, "  Step {}: {}", i, state)?;
                }
                Ok(())
            }
            Counterexample::Lasso { stem, loop_states } => {
                writeln!(
                    f,
                    "Lasso counterexample (stem: {} states, loop: {} states):",
                    stem.len(),
                    loop_states.len()
                )?;
                writeln!(f, "  Stem:")?;
                for (i, state) in stem.iter().enumerate() {
                    writeln!(f, "    Step {}: {}", i, state)?;
                }
                writeln!(f, "  Loop (repeats forever):")?;
                for (i, state) in loop_states.iter().enumerate() {
                    writeln!(f, "    Step {}: {}", i, state)?;
                }
                Ok(())
            }
        }
    }
}

/// Counterexample generator.
pub struct CounterexampleGenerator {
    ts: Rc<TransitionSystem>,
}

impl CounterexampleGenerator {
    pub fn new(ts: Rc<TransitionSystem>) -> Self {
        CounterexampleGenerator { ts }
    }

    fn bdd(&self) -> &Bdd {
        self.ts.bdd()
    }

    /// Generate a linear counterexample from initial states to bad states.
    ///
    /// Uses backward search from bad states to find a path from initial.
    pub fn generate_linear(&self, bad_states: Ref) -> Option<Counterexample> {
        let initial = self.ts.initial();

        // Check if bad states are reachable from initial
        let reachable_bad = self.bdd().apply_and(self.ts.reachable(), bad_states);
        if self.bdd().is_zero(reachable_bad) {
            return None; // No counterexample exists
        }

        // Backward BFS to find shortest path
        let mut layers: Vec<Ref> = vec![bad_states];
        let mut current = bad_states;

        loop {
            let predecessors = self.ts.preimage(current);
            let new_states = self.bdd().apply_and(predecessors, self.bdd().apply_not(current));

            // Check if we've reached initial states
            let initial_in_pre = self.bdd().apply_and(predecessors, initial);
            if !self.bdd().is_zero(initial_in_pre) {
                // Found a path - now extract concrete states
                return Some(self.extract_linear_trace(&layers, initial));
            }

            if self.bdd().is_zero(new_states) {
                // No more states to explore - shouldn't happen if reachable
                return None;
            }

            current = self.bdd().apply_or(current, new_states);
            layers.push(current);

            // Safety bound
            if layers.len() > 1000 {
                log::warn!("Counterexample search exceeded depth limit");
                return None;
            }
        }
    }

    /// Extract a concrete linear trace from backward search layers.
    fn extract_linear_trace(&self, layers: &[Ref], initial: Ref) -> Counterexample {
        let mut trace = Vec::new();

        // Start from an initial state that can reach bad
        let first_layer_with_initial = self.bdd().apply_and(layers.last().copied().unwrap_or(initial), initial);
        let mut current_state_set = self.pick_one_state(first_layer_with_initial);
        trace.push(self.extract_state(current_state_set));

        // Walk forward through layers (reversed since we did backward search)
        for layer in layers.iter().rev().skip(1) {
            // Find a successor in the next layer
            let successors = self.ts.image(current_state_set);
            let next_in_layer = self.bdd().apply_and(successors, *layer);

            if self.bdd().is_zero(next_in_layer) {
                break;
            }

            current_state_set = self.pick_one_state(next_in_layer);
            trace.push(self.extract_state(current_state_set));
        }

        Counterexample::Linear(trace)
    }

    /// Generate a lasso counterexample for liveness violations.
    ///
    /// Finds a stem from initial to a fair cycle.
    pub fn generate_lasso(&self, eg_states: Ref) -> Option<Counterexample> {
        let initial = self.ts.initial();

        // Find initial states that can reach EG states
        let initial_to_eg = self.bdd().apply_and(initial, self.reach_backward(eg_states));
        if self.bdd().is_zero(initial_to_eg) {
            return None;
        }

        // Generate stem: path from initial to EG
        let stem = self.generate_stem(initial_to_eg, eg_states);

        // Generate loop: cycle within EG states
        let loop_start = stem.last().cloned().unwrap_or_default();
        let loop_states = self.generate_loop(eg_states, &loop_start);

        Some(Counterexample::Lasso { stem, loop_states })
    }

    /// Generate stem from initial to target states.
    fn generate_stem(&self, from: Ref, to: Ref) -> Vec<State> {
        let mut trace = Vec::new();

        let mut current = self.pick_one_state(from);
        trace.push(self.extract_state(current));

        // BFS forward until we hit target
        for _ in 0..100 {
            // Depth limit
            let successors = self.ts.image(current);
            let hit_target = self.bdd().apply_and(successors, to);

            if !self.bdd().is_zero(hit_target) {
                // Reached target
                current = self.pick_one_state(hit_target);
                trace.push(self.extract_state(current));
                break;
            }

            // Continue forward
            current = self.pick_one_state(successors);
            trace.push(self.extract_state(current));
        }

        trace
    }

    /// Generate a loop within EG states.
    fn generate_loop(&self, eg_states: Ref, start: &State) -> Vec<State> {
        let mut trace = Vec::new();

        // Convert start state back to BDD
        let start_bdd = self.state_to_bdd(start);
        let mut current = start_bdd;

        // Find a cycle by following successors within EG
        for _ in 0..100 {
            let successors = self.ts.image(current);
            let next_in_eg = self.bdd().apply_and(successors, eg_states);

            if self.bdd().is_zero(next_in_eg) {
                break;
            }

            // Check if we've returned to start
            let back_to_start = self.bdd().apply_and(next_in_eg, start_bdd);
            if !self.bdd().is_zero(back_to_start) && !trace.is_empty() {
                // Completed the loop
                break;
            }

            current = self.pick_one_state(next_in_eg);
            trace.push(self.extract_state(current));
        }

        trace
    }

    /// Backward reachability from target.
    fn reach_backward(&self, target: Ref) -> Ref {
        let mut reached = target;
        loop {
            let pre = self.ts.preimage(reached);
            let new_reached = self.bdd().apply_or(reached, pre);
            if new_reached == reached {
                return reached;
            }
            reached = new_reached;
        }
    }

    /// Pick one state from a state set (non-deterministically).
    fn pick_one_state(&self, states: Ref) -> Ref {
        // Use one_sat to get a single satisfying assignment
        // Returns Vec<i32> where positive means true, negative means false
        if let Some(assignment) = self.bdd().one_sat(states) {
            // Convert assignment to a BDD representing that single state
            let mut result = self.bdd().one();
            for lit in assignment {
                let var = BddVar::new(lit.unsigned_abs());
                let var_bdd = self.bdd().mk_var(var);
                let literal = if lit > 0 { var_bdd } else { self.bdd().apply_not(var_bdd) };
                result = self.bdd().apply_and(result, literal);
            }
            result
        } else {
            self.bdd().zero()
        }
    }

    /// Extract a concrete State from a singleton state set.
    fn extract_state(&self, state_bdd: Ref) -> State {
        let mut state = State::new();

        if let Some(assignment) = self.bdd().one_sat(state_bdd) {
            // Map BDD variables back to state variable names
            let present_vars: HashMap<BddVar, &Var> = self
                .ts
                .var_manager()
                .vars()
                .iter()
                .filter_map(|v| self.ts.var_manager().get_present(v).map(|bdd_var| (bdd_var, v)))
                .collect();

            for lit in assignment {
                let bdd_var = BddVar::new(lit.unsigned_abs());
                let value = lit > 0;
                if let Some(var) = present_vars.get(&bdd_var) {
                    state.set(var.name().to_string(), value);
                }
            }
        }

        state
    }

    /// Convert a State back to a BDD.
    fn state_to_bdd(&self, state: &State) -> Ref {
        let mut result = self.bdd().one();

        for var in self.ts.var_manager().vars() {
            if let Some(bdd_var) = self.ts.var_manager().get_present(var) {
                let var_bdd = self.bdd().mk_var(bdd_var);
                let value = state.get(var.name()).unwrap_or(false);
                let literal = if value { var_bdd } else { self.bdd().apply_not(var_bdd) };
                result = self.bdd().apply_and(result, literal);
            }
        }

        result
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn create_counter_system() -> Rc<TransitionSystem> {
        // 2-bit counter: 00 -> 01 -> 10 -> 11 -> 00 -> ...
        let bdd = Rc::new(Bdd::default());
        let mut ts = TransitionSystem::new(bdd);

        let x = Var::new("x");
        let y = Var::new("y");
        ts.declare_var(x.clone());
        ts.declare_var(y.clone());

        let x_pres = ts.var_manager().get_present(&x).unwrap();
        let y_pres = ts.var_manager().get_present(&y).unwrap();
        let x_next = ts.var_manager().get_next(&x).unwrap();
        let y_next = ts.var_manager().get_next(&y).unwrap();

        // Initial: x=0, y=0
        let x_bdd = ts.bdd().mk_var(x_pres);
        let y_bdd = ts.bdd().mk_var(y_pres);
        let not_x = ts.bdd().apply_not(x_bdd);
        let not_y = ts.bdd().apply_not(y_bdd);
        let initial = ts.bdd().apply_and(not_x, not_y);
        ts.set_initial(initial);

        // Transitions: x' = x XOR y, y' = !y
        let x_next_bdd = ts.bdd().mk_var(x_next);
        let y_next_bdd = ts.bdd().mk_var(y_next);

        let x_next_expr = ts.bdd().apply_xor(x_bdd, y_bdd);
        let y_next_expr = ts.bdd().apply_not(y_bdd);

        let x_trans = ts.bdd().apply_eq(x_next_bdd, x_next_expr);
        let y_trans = ts.bdd().apply_eq(y_next_bdd, y_next_expr);
        let transition = ts.bdd().apply_and(x_trans, y_trans);
        ts.set_transition(transition);

        // Label: "overflow" when x=1 AND y=1
        let overflow = ts.bdd().apply_and(x_bdd, y_bdd);
        ts.add_label("overflow".to_string(), overflow);

        Rc::new(ts)
    }

    #[test]
    fn test_linear_counterexample() {
        let ts = create_counter_system();
        let gen = CounterexampleGenerator::new(ts.clone());

        // Find path to overflow state
        let overflow = ts.get_label("overflow").unwrap();
        let cex = gen.generate_linear(overflow);

        assert!(cex.is_some());
        let cex = cex.unwrap();
        println!("{}", cex);

        match cex {
            Counterexample::Linear(states) => {
                assert!(!states.is_empty());
                // First state should be x=0, y=0
                assert_eq!(states[0].get("x"), Some(false));
                assert_eq!(states[0].get("y"), Some(false));
            }
            _ => panic!("Expected linear counterexample"),
        }
    }
}
