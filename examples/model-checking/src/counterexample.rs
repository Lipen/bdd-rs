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
use bdd_rs::types::{Lit, Var as BddVar};

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

        // Check if initial states are already bad
        let initial_bad = self.bdd().apply_and(initial, bad_states);
        if !self.bdd().is_zero(initial_bad) {
            // Initial state is bad - single state counterexample
            let (_, literals) = self.pick_one_state(initial_bad);
            let state = self.extract_state(&literals);
            return Some(Counterexample::Linear(vec![state]));
        }

        // Backward BFS to find shortest path from initial to bad
        // layers[i] = states that can reach bad in exactly i steps
        let mut layers: Vec<Ref> = vec![bad_states];
        let mut visited = bad_states;

        loop {
            let predecessors = self.ts.preimage(*layers.last().unwrap());

            // Check if we've reached initial states
            let initial_in_pre = self.bdd().apply_and(predecessors, initial);
            if !self.bdd().is_zero(initial_in_pre) {
                // Found a path - extract concrete states forward from initial
                return Some(self.extract_linear_trace(&layers, initial_in_pre));
            }

            // New states = predecessors not yet visited
            let new_states = self.bdd().apply_and(predecessors, self.bdd().apply_not(visited));

            if self.bdd().is_zero(new_states) {
                // No more states to explore - shouldn't happen if reachable
                return None;
            }

            visited = self.bdd().apply_or(visited, new_states);
            layers.push(new_states);

            // Safety bound
            if layers.len() > 1000 {
                log::warn!("Counterexample search exceeded depth limit");
                return None;
            }
        }
    }

    /// Extract a concrete linear trace by walking forward from initial through layers.
    fn extract_linear_trace(&self, layers: &[Ref], initial: Ref) -> Counterexample {
        let mut trace = Vec::new();

        // Pick one initial state that can reach bad
        let (mut current_bdd, mut current_lits) = self.pick_one_state(initial);
        trace.push(self.extract_state(&current_lits));

        // Walk forward through layers (they are in reverse order: layers[0] = bad)
        for layer in layers.iter().rev() {
            // Find a successor in this layer
            let successors = self.ts.image(current_bdd);
            let next_in_layer = self.bdd().apply_and(successors, *layer);

            if self.bdd().is_zero(next_in_layer) {
                break;
            }

            (current_bdd, current_lits) = self.pick_one_state(next_in_layer);
            trace.push(self.extract_state(&current_lits));
        }

        Counterexample::Linear(trace)
    }

    /// Generate a lasso counterexample for liveness violations.
    ///
    /// Finds a stem from initial to a fair cycle.
    /// The lasso structure:
    /// - Stem: path from initial to the loop entry (exclusive of loop entry)
    /// - Loop: cycle starting and ending at the same state
    ///
    /// The full trace is: `stem[0] -> stem[1] -> ... -> loop[0] -> loop[1] -> ... -> loop[0] -> ...`
    pub fn generate_lasso(&self, eg_states: Ref) -> Option<Counterexample> {
        let initial = self.ts.initial();

        // Find initial states that are in EG or can reach EG states
        let can_reach_eg = self.reach_backward(eg_states);
        let initial_to_eg = self.bdd().apply_and(initial, can_reach_eg);
        if self.bdd().is_zero(initial_to_eg) {
            return None;
        }

        // Check if initial is already in EG (can start loop immediately)
        let initial_in_eg = self.bdd().apply_and(initial, eg_states);

        if !self.bdd().is_zero(initial_in_eg) {
            // Initial state is in EG - empty stem, start loop from initial
            let (start_bdd, start_lits) = self.pick_one_state(initial_in_eg);
            let start_state = self.extract_state(&start_lits);
            let loop_states = self.generate_loop(eg_states, start_bdd, &start_state);
            return Some(Counterexample::Lasso { stem: vec![], loop_states });
        }

        // Generate stem: path from initial to first EG state
        let (stem, loop_entry_bdd, loop_entry_state) = self.generate_stem(initial_to_eg, eg_states);

        // Generate loop: cycle within EG states starting from loop_entry
        let loop_states = self.generate_loop(eg_states, loop_entry_bdd, &loop_entry_state);

        Some(Counterexample::Lasso { stem, loop_states })
    }

    /// Generate stem from initial to first EG state.
    /// Returns tuple: (stem states excluding loop entry, loop entry BDD, loop entry State).
    fn generate_stem(&self, from: Ref, eg_states: Ref) -> (Vec<State>, Ref, State) {
        let mut stem = Vec::new();

        let (mut current_bdd, mut current_lits) = self.pick_one_state(from);

        // Walk forward until we hit EG states
        for _ in 0..100 {
            let current_state = self.extract_state(&current_lits);

            // Check if current state is in EG
            let in_eg = self.bdd().apply_and(current_bdd, eg_states);
            if !self.bdd().is_zero(in_eg) {
                // Current state is in EG - this is the loop entry
                return (stem, current_bdd, current_state);
            }

            // Add to stem and continue
            stem.push(current_state);

            let successors = self.ts.image(current_bdd);
            if self.bdd().is_zero(successors) {
                break;
            }

            (current_bdd, current_lits) = self.pick_one_state(successors);
        }

        // Fallback (shouldn't happen if from can reach eg_states)
        let state = self.extract_state(&current_lits);
        (stem, current_bdd, state)
    }

    /// Generate a loop within EG states starting from a specific state.
    /// Returns the cycle including the start state as `loop[0]`.
    fn generate_loop(&self, eg_states: Ref, start_bdd: Ref, start_state: &State) -> Vec<State> {
        let mut trace = vec![start_state.clone()];
        let mut current_bdd = start_bdd;

        // Follow successors within EG until we return to start
        for _ in 0..100 {
            let successors = self.ts.image(current_bdd);
            let next_in_eg = self.bdd().apply_and(successors, eg_states);

            if self.bdd().is_zero(next_in_eg) {
                // No successors in EG - shouldn't happen for valid EG states
                break;
            }

            // Check if we can return to start (completing the loop)
            let back_to_start = self.bdd().apply_and(next_in_eg, start_bdd);
            if !self.bdd().is_zero(back_to_start) {
                // Can return to start - loop is complete
                // Don't add start again, it's already at trace[0]
                break;
            }

            let current_lits;
            (current_bdd, current_lits) = self.pick_one_state(next_in_eg);
            trace.push(self.extract_state(&current_lits));
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
    /// Returns (BDD cube, literals) to avoid recomputing the assignment.
    fn pick_one_state(&self, states: Ref) -> (Ref, Vec<Lit>) {
        if self.bdd().is_zero(states) {
            return (self.bdd().zero(), vec![]);
        }

        // Get a satisfying assignment and build a cube from it.
        // Partial assignments are fine - they represent a subset of matching states.
        let literals = self.bdd().one_sat(states).unwrap_or_default();
        let cube = self.bdd().mk_cube(literals.clone());
        (cube, literals)
    }

    /// Extract a concrete State from literals.
    fn extract_state(&self, literals: &[Lit]) -> State {
        let mut state = State::new();

        // Map BDD variables back to state variable names
        let present_vars: HashMap<BddVar, &Var> = self
            .ts
            .var_manager()
            .vars()
            .iter()
            .filter_map(|v| self.ts.var_manager().get_present(v).map(|bdd_var| (bdd_var, v)))
            .collect();

        for &lit in literals {
            let bdd_var = lit.var();
            let value = lit.is_positive();
            if let Some(var) = present_vars.get(&bdd_var) {
                state.set(var.name().to_string(), value);
            }
        }

        state
    }

    /// Convert a State back to a BDD.
    #[allow(dead_code)]
    fn state_to_bdd(&self, state: &State) -> Ref {
        let literals: Vec<Lit> = self
            .ts
            .var_manager()
            .vars()
            .iter()
            .filter_map(|var| {
                if let Some(value) = self.ts.var_manager().get_present(var) {
                    return state.get(var.name()).map(|v| Lit::new(value, !v));
                }
                None
            })
            .collect();

        self.bdd().mk_cube(literals)
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
        let _x_next = ts.var_manager().get_next(&x).unwrap();
        let _y_next = ts.var_manager().get_next(&y).unwrap();

        let x_bdd = ts.bdd().mk_var(x_pres);
        let y_bdd = ts.bdd().mk_var(y_pres);

        // Initial: x=0, y=0
        let initial = ts.bdd().mk_cube([x_pres.neg(), y_pres.neg()]);
        ts.set_initial(initial);

        // Transitions: x' = x XOR y, y' = !y
        let x_trans = ts.assign_var(&x, ts.bdd().apply_xor(x_bdd, y_bdd));
        let y_trans = ts.assign_var(&y, ts.bdd().apply_not(y_bdd));
        let transition = ts.build_transition(&[x_trans, y_trans]);
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

    #[test]
    fn test_lasso_counterexample() {
        let ts = create_counter_system();
        let gen = CounterexampleGenerator::new(ts.clone());

        // The 2-bit counter cycles: 00 -> 01 -> 10 -> 11 -> 00
        // All reachable states can reach all other reachable states,
        // so EG(true) = all reachable states.
        // Since initial (00) is already in EG, the stem is empty.
        let eg_states = ts.reachable();

        let cex = gen.generate_lasso(eg_states);
        assert!(cex.is_some());
        let cex = cex.unwrap();
        println!("{}", cex);

        match &cex {
            Counterexample::Lasso { stem, loop_states } => {
                // Initial state (00) is in EG, so stem is empty
                // Loop starts from initial and cycles through all states
                assert!(stem.is_empty(), "Stem should be empty when initial is in EG");

                // Loop should contain the full cycle
                assert!(!loop_states.is_empty(), "Loop should contain at least one state");
                assert_eq!(loop_states.len(), 4, "Should have all 4 states in the cycle");

                // Loop should start from initial (x=0, y=0)
                assert_eq!(loop_states[0].get("x"), Some(false));
                assert_eq!(loop_states[0].get("y"), Some(false));

                println!("Stem length: {}", stem.len());
                println!("Loop length: {}", loop_states.len());
            }
            _ => panic!("Expected lasso counterexample"),
        }
    }

    #[test]
    fn test_lasso_from_unreachable_returns_none() {
        // Create a simple system where EG states don't include initial
        let bdd = Rc::new(Bdd::default());
        let mut ts = TransitionSystem::new(bdd);

        let x = Var::new("x");
        ts.declare_var(x.clone());

        let x_pres = ts.var_manager().get_present(&x).unwrap();
        let _x_next = ts.var_manager().get_next(&x).unwrap();

        // Initial: x=0
        let initial = ts.bdd().mk_cube([x_pres.neg()]);
        ts.set_initial(initial);

        // Transition: x' = 1 (always goes to x=1)
        let x_trans = ts.assign_var(&x, ts.bdd().one());
        let transition = ts.build_transition(&[x_trans]);
        ts.set_transition(transition);

        let ts = Rc::new(ts);
        let gen = CounterexampleGenerator::new(ts.clone());

        // EG states that don't intersect with states reachable from initial
        // Use a state x=0 but it immediately transitions to x=1, so no cycle at x=0
        // Actually, let's use the empty set
        let empty = ts.bdd().zero();
        let cex = gen.generate_lasso(empty);
        assert!(cex.is_none());
    }

    #[test]
    fn test_lasso_with_nonempty_stem() {
        // Create a system where initial is NOT in EG, requiring a stem.
        // System: x transitions 0 -> 1 -> 1 (self-loop at 1)
        // Initial: x=0, EG states: x=1 (the self-loop)
        let bdd = Rc::new(Bdd::default());
        let mut ts = TransitionSystem::new(bdd);

        let x = Var::new("x");
        ts.declare_var(x.clone());

        let x_pres = ts.var_manager().get_present(&x).unwrap();

        let x_bdd = ts.bdd().mk_var(x_pres);

        // Initial: x=0
        let initial = ts.bdd().mk_cube([x_pres.neg()]);
        ts.set_initial(initial);

        // Transition: x' = 1 (always goes to x=1, stays at x=1)
        let x_trans = ts.assign_var(&x, ts.bdd().one());
        let transition = ts.build_transition(&[x_trans]);
        ts.set_transition(transition);

        let ts = Rc::new(ts);
        let gen = CounterexampleGenerator::new(ts.clone());

        // EG states = {x=1} (the self-loop)
        // Initial x=0 is NOT in EG, so stem should be [x=0]
        let eg_states = x_bdd;

        let cex = gen.generate_lasso(eg_states);
        assert!(cex.is_some());
        let cex = cex.unwrap();
        println!("{}", cex);

        match &cex {
            Counterexample::Lasso { stem, loop_states } => {
                // Stem should contain initial state (x=0)
                assert_eq!(stem.len(), 1, "Stem should have one state (x=0)");
                assert_eq!(stem[0].get("x"), Some(false));

                // Loop should be x=1 (self-loop, just one state)
                assert_eq!(loop_states.len(), 1, "Self-loop should have one state");
                assert_eq!(loop_states[0].get("x"), Some(true));

                println!("Stem length: {}", stem.len());
                println!("Loop length: {}", loop_states.len());
            }
            _ => panic!("Expected lasso counterexample"),
        }
    }
}
