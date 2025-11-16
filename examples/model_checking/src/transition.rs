//! Transition system representation for symbolic model checking.
//!
//! This module provides the core data structures for representing finite-state
//! systems symbolically using BDDs.

use std::collections::HashMap;
use std::fmt;

use bdd_rs::bdd::Bdd;
use bdd_rs::reference::Ref;

/// A variable in the transition system.
///
/// Variables have both present-state and next-state versions for encoding transitions.
#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Var(pub String);

impl Var {
    pub fn new(s: impl Into<String>) -> Self {
        Var(s.into())
    }

    /// Get the name of this variable
    pub fn name(&self) -> &str {
        &self.0
    }

    /// Create the next-state version of this variable (e.g., "x" -> "x'")
    pub fn next(&self) -> Var {
        Var(format!("{}'", self.0))
    }

    /// Check if this is a next-state variable
    pub fn is_next_state(&self) -> bool {
        self.0.ends_with('\'')
    }

    /// Get the present-state version (removes trailing ')
    pub fn present(&self) -> Var {
        if self.is_next_state() {
            Var(self.0[..self.0.len() - 1].to_string())
        } else {
            self.clone()
        }
    }
}

impl fmt::Display for Var {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl From<&str> for Var {
    fn from(s: &str) -> Self {
        Var::new(s)
    }
}

impl From<String> for Var {
    fn from(s: String) -> Self {
        Var(s)
    }
}

/// Manages BDD variable allocation for transition systems.
///
/// Maps logical state variables to pairs of BDD variable indices
/// (one for present state, one for next state).
#[derive(Debug, Clone)]
pub struct VarManager {
    /// Maps state variables to their present-state BDD index
    present_state_map: HashMap<Var, u32>,
    /// Maps state variables to their next-state BDD index
    next_state_map: HashMap<Var, u32>,
    /// Counter for allocating new BDD variables
    next_index: u32,
    /// Ordered list of state variables (for iteration)
    var_order: Vec<Var>,
}

impl VarManager {
    pub fn new() -> Self {
        VarManager {
            present_state_map: HashMap::new(),
            next_state_map: HashMap::new(),
            next_index: 1, // Start from 1 (0 is reserved for constants)
            var_order: Vec::new(),
        }
    }

    /// Declare a new state variable and allocate BDD indices for it.
    ///
    /// Returns (present_state_index, next_state_index).
    pub fn declare_var(&mut self, var: Var) -> (u32, u32) {
        if let Some(&present_idx) = self.present_state_map.get(&var) {
            let next_idx = self.next_state_map[&var];
            return (present_idx, next_idx);
        }

        let present_idx = self.next_index;
        self.next_index += 1;
        let next_idx = self.next_index;
        self.next_index += 1;

        self.present_state_map.insert(var.clone(), present_idx);
        self.next_state_map.insert(var.clone(), next_idx);
        self.var_order.push(var);

        (present_idx, next_idx)
    }

    /// Get the present-state BDD index for a variable
    pub fn get_present(&self, var: &Var) -> Option<u32> {
        self.present_state_map.get(var).copied()
    }

    /// Get the next-state BDD index for a variable
    pub fn get_next(&self, var: &Var) -> Option<u32> {
        self.next_state_map.get(var).copied()
    }

    /// Get all declared state variables in order
    pub fn vars(&self) -> &[Var] {
        &self.var_order
    }

    /// Get the number of state variables
    pub fn num_vars(&self) -> usize {
        self.var_order.len()
    }

    /// Get all present-state BDD indices
    pub fn present_indices(&self) -> Vec<u32> {
        self.var_order.iter().map(|v| self.present_state_map[v]).collect()
    }

    /// Get all next-state BDD indices
    pub fn next_indices(&self) -> Vec<u32> {
        self.var_order.iter().map(|v| self.next_state_map[v]).collect()
    }
}

impl Default for VarManager {
    fn default() -> Self {
        Self::new()
    }
}

/// A symbolic transition system (Kripke structure).
///
/// Represents a finite-state system using BDDs:
/// - States are encoded as boolean vectors
/// - Sets of states are represented as BDD characteristic functions
/// - Transitions are represented as a relation T(s, s') over present and next states
#[derive(Debug)]
pub struct TransitionSystem {
    /// BDD manager
    bdd: Bdd,
    /// Variable manager
    var_manager: VarManager,
    /// Initial states: I(s)
    initial: Ref,
    /// Transition relation: T(s, s')
    transition: Ref,
    /// Atomic propositions: maps proposition names to state sets
    labels: HashMap<String, Ref>,
}

impl TransitionSystem {
    /// Create a new transition system
    pub fn new(bdd: Bdd) -> Self {
        TransitionSystem {
            bdd,
            var_manager: VarManager::new(),
            initial: Ref::ZERO,
            transition: Ref::ZERO,
            labels: HashMap::new(),
        }
    }

    /// Get the BDD manager
    pub fn bdd(&self) -> &Bdd {
        &self.bdd
    }

    /// Get the variable manager
    pub fn var_manager(&self) -> &VarManager {
        &self.var_manager
    }

    /// Get mutable access to variable manager
    pub fn var_manager_mut(&mut self) -> &mut VarManager {
        &mut self.var_manager
    }

    /// Declare a state variable
    pub fn declare_var(&mut self, var: Var) -> (u32, u32) {
        self.var_manager.declare_var(var)
    }

    /// Set the initial states
    pub fn set_initial(&mut self, initial: Ref) {
        self.initial = initial;
    }

    /// Get the initial states
    pub fn initial(&self) -> Ref {
        self.initial
    }

    /// Set the transition relation
    pub fn set_transition(&mut self, transition: Ref) {
        self.transition = transition;
    }

    /// Get the transition relation
    pub fn transition(&self) -> Ref {
        self.transition
    }

    /// Add a labeled state set (atomic proposition)
    pub fn add_label(&mut self, name: String, states: Ref) {
        self.labels.insert(name, states);
    }

    /// Get the states labeled with a given atomic proposition
    pub fn get_label(&self, name: &str) -> Option<Ref> {
        self.labels.get(name).copied()
    }

    /// Get all label names
    pub fn label_names(&self) -> Vec<&str> {
        self.labels.keys().map(|s| s.as_str()).collect()
    }

    /// Compute the successor states: ∃s. from(s) ∧ T(s, s')
    ///
    /// Returns the set of states reachable in one step from `from`.
    pub fn image(&self, from: Ref) -> Ref {
        // from(s) ∧ T(s, s')
        let conjunction = self.bdd.apply_and(from, self.transition);

        // ∃s. conjunction - quantify out present-state variables
        let present_vars = self.var_manager.present_indices();
        let result_in_next = self.exists(conjunction, &present_vars);

        // Rename from next-state variables to present-state variables
        self.rename_to_present(result_in_next)
    }

    /// Compute the predecessor states: ∃s'. T(s, s') ∧ to(s')
    ///
    /// Returns the set of states that can reach `to` in one step.
    pub fn preimage(&self, to: Ref) -> Ref {
        // Rename to(s') to use next-state variables
        let to_next = self.rename_to_next(to);

        // T(s, s') ∧ to(s')
        let conjunction = self.bdd.apply_and(self.transition, to_next);

        // ∃s'. conjunction - quantify out next-state variables
        let next_vars = self.var_manager.next_indices();
        self.exists(conjunction, &next_vars)
    }

    /// Compute reachable states from initial states
    pub fn reachable(&self) -> Ref {
        let mut reached = self.initial;
        loop {
            let new_states = self.image(reached);
            let new_reached = self.bdd.apply_or(reached, new_states);

            if new_reached == reached {
                return reached;
            }
            reached = new_reached;
        }
    }

    /// Rename a state set from present-state to next-state variables
    fn rename_to_next(&self, state_set: Ref) -> Ref {
        let present_vars = self.var_manager.present_indices();
        let next_vars = self.var_manager.next_indices();
        self.rename(state_set, &present_vars, &next_vars)
    }

    /// Rename a state set from next-state to present-state variables
    pub fn rename_to_present(&self, state_set: Ref) -> Ref {
        let present_vars = self.var_manager.present_indices();
        let next_vars = self.var_manager.next_indices();
        self.rename(state_set, &next_vars, &present_vars)
    }

    /// Count the number of states in a state set (up to 2^64)
    pub fn count_states(&self, states: Ref) -> Option<u64> {
        use num_traits::ToPrimitive;
        let num_vars = self.var_manager.present_indices().len();
        let count = self.bdd.sat_count(states, num_vars);
        // Try to convert BigUint to u64
        count.to_u64()
    }

    /// Check if a state set is empty
    pub fn is_empty(&self, states: Ref) -> bool {
        self.bdd.is_zero(states)
    }

    /// Get all states (universe)
    pub fn all_states(&self) -> Ref {
        self.bdd.one
    }

    /// Existentially quantify out variables
    fn exists(&self, f: Ref, vars: &[u32]) -> Ref {
        let mut result = f;
        for &v in vars {
            // ∃v. f = f[v/0] ∨ f[v/1]
            let f0 = self.bdd.substitute(result, v, false);
            let f1 = self.bdd.substitute(result, v, true);
            result = self.bdd.apply_or(f0, f1);
        }
        result
    }

    /// Rename variables according to mapping
    ///
    /// This performs a simultaneous substitution to avoid variable conflicts.
    fn rename(&self, f: Ref, from_vars: &[u32], to_vars: &[u32]) -> Ref {
        assert_eq!(from_vars.len(), to_vars.len());

        // Build a complete mapping including both directions to handle temporary conflicts
        // We need to ensure atomicity: all variables change simultaneously
        let mut result = f;

        // Perform renaming by composing substitutions
        // Since compose can have conflicts, we do it carefully
        for (&from_v, &to_v) in from_vars.iter().zip(to_vars.iter()) {
            if from_v != to_v {
                // Compose: replace variable from_v with expression for to_v
                let to_v_bdd = self.bdd.mk_var(to_v);
                result = self.bdd.compose(result, from_v, to_v_bdd);
            }
        }
        result
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_var_next() {
        let x = Var::new("x");
        let x_next = x.next();
        assert_eq!(x_next.name(), "x'");
        assert!(x_next.is_next_state());
        assert_eq!(x_next.present(), x);
    }

    #[test]
    fn test_var_manager() {
        let mut vm = VarManager::new();

        let x = Var::new("x");
        let y = Var::new("y");

        let (x_pres, x_next) = vm.declare_var(x.clone());
        let (y_pres, y_next) = vm.declare_var(y.clone());

        assert_eq!(x_pres, 1);
        assert_eq!(x_next, 2);
        assert_eq!(y_pres, 3);
        assert_eq!(y_next, 4);

        assert_eq!(vm.get_present(&x), Some(1));
        assert_eq!(vm.get_next(&x), Some(2));
        assert_eq!(vm.num_vars(), 2);
    }

    #[test]
    fn test_transition_system_basic() {
        let bdd = Bdd::default();
        let mut ts = TransitionSystem::new(bdd);

        let x = Var::new("x");
        ts.declare_var(x.clone());

        // Initial: x = false
        let x_pres = ts.var_manager().get_present(&x).unwrap();
        let initial = ts.bdd().apply_not(ts.bdd().mk_var(x_pres));
        ts.set_initial(initial);

        // Transition: x' = !x (toggle)
        let x_next = ts.var_manager().get_next(&x).unwrap();
        let x_pres_bdd = ts.bdd().mk_var(x_pres);
        let x_next_bdd = ts.bdd().mk_var(x_next);
        // T: (x ∧ ¬x') ∨ (¬x ∧ x')  [XOR]
        let transition = ts.bdd().apply_xor(x_pres_bdd, x_next_bdd);
        ts.set_transition(transition);

        // Test image
        let successors = ts.image(initial);
        // Initial is {x=false}, successors should be {x=true}
        let x_true = ts.bdd().mk_var(x_pres);

        // Debug: check if successors represents x=true
        // successors should have variable x_pres set to true
        eprintln!("initial = {}, successors = {}, x_true = {}", initial, successors, x_true);
        eprintln!("x_pres = {}, x_next = {}", x_pres, x_next);

        // Check semantically rather than syntactically
        let equiv = ts.bdd().apply_eq(successors, x_true);
        assert!(ts.bdd().is_one(equiv), "successors should be equivalent to x=true");
    }

    #[test]
    fn test_reachability() {
        let bdd = Bdd::default();
        let mut ts = TransitionSystem::new(bdd);

        let x = Var::new("x");
        let y = Var::new("y");
        ts.declare_var(x.clone());
        ts.declare_var(y.clone());

        let x_pres = ts.var_manager().get_present(&x).unwrap();
        let y_pres = ts.var_manager().get_present(&y).unwrap();
        let x_next = ts.var_manager().get_next(&x).unwrap();
        let y_next = ts.var_manager().get_next(&y).unwrap();

        // Initial: x=false, y=false
        let initial = ts.bdd().apply_and(
            ts.bdd().apply_not(ts.bdd().mk_var(x_pres)),
            ts.bdd().apply_not(ts.bdd().mk_var(y_pres)),
        );
        ts.set_initial(initial);

        // Transition: x' = !x, y' = y XOR x (creates 2-bit counter)
        // This creates states: (0,0) -> (1,0) -> (0,1) -> (1,1) -> (0,0) ...
        let x_pres_bdd = ts.bdd().mk_var(x_pres);
        let y_pres_bdd = ts.bdd().mk_var(y_pres);
        let x_next_bdd = ts.bdd().mk_var(x_next);
        let y_next_bdd = ts.bdd().mk_var(y_next);

        // x' = !x (toggle x)
        let t1 = ts.bdd().apply_xor(x_pres_bdd, x_next_bdd);

        // y' = y XOR x (toggle y when x=1)
        let y_next_formula = ts.bdd().apply_xor(y_pres_bdd, x_pres_bdd);
        let t2 = ts.bdd().apply_eq(y_next_bdd, y_next_formula);

        let transition = ts.bdd().apply_and(t1, t2);
        ts.set_transition(transition);

        // Compute reachable states
        let reachable = ts.reachable();

        // Should reach all 4 states: (0,0), (1,0), (0,1), (1,1)
        let count = ts.count_states(reachable);
        assert_eq!(count, Some(4));
    }
}
