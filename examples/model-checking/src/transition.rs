//! Transition system representation for symbolic model checking.
//!
//! This module provides the core data structures for representing finite-state
//! systems symbolically using BDDs.

use std::collections::HashMap;
use std::fmt;
use std::rc::Rc;

use bdd_rs::bdd::Bdd;
use bdd_rs::reference::Ref;
use bdd_rs::types::Var as BddVar;

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
/// Maps logical state variables to pairs of BDD variables
/// (one for present state, one for next state).
#[derive(Debug, Clone)]
pub struct VarManager {
    /// Maps state variables to their present-state BDD variable
    present_state_map: HashMap<Var, BddVar>,
    /// Maps state variables to their next-state BDD variable
    next_state_map: HashMap<Var, BddVar>,
    /// Ordered list of state variables (for iteration)
    var_order: Vec<Var>,
}

impl VarManager {
    pub fn new() -> Self {
        VarManager {
            present_state_map: HashMap::new(),
            next_state_map: HashMap::new(),
            var_order: Vec::new(),
        }
    }

    /// Register a state variable with its pre-allocated BDD variables.
    ///
    /// This is called by [TransitionSystem] after allocating variables via the BDD manager.
    pub fn register_var(&mut self, var: Var, present: BddVar, next: BddVar) {
        if self.present_state_map.contains_key(&var) {
            return; // Already registered
        }
        self.present_state_map.insert(var.clone(), present);
        self.next_state_map.insert(var.clone(), next);
        self.var_order.push(var);
    }

    /// Check if a variable is already declared
    pub fn is_declared(&self, var: &Var) -> bool {
        self.present_state_map.contains_key(var)
    }

    /// Get the present-state BDD variable for a state variable
    pub fn get_present(&self, var: &Var) -> Option<BddVar> {
        self.present_state_map.get(var).copied()
    }

    /// Get the next-state BDD variable for a state variable
    pub fn get_next(&self, var: &Var) -> Option<BddVar> {
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

    /// Get all present-state BDD variables
    pub fn present_vars(&self) -> Vec<BddVar> {
        self.var_order.iter().map(|v| self.present_state_map[v]).collect()
    }

    /// Get all next-state BDD variables
    pub fn next_vars(&self) -> Vec<BddVar> {
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
#[derive(Debug, Clone)]
pub struct TransitionSystem {
    /// Shared BDD manager (reference-counted)
    bdd: Rc<Bdd>,
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
    /// Create a new transition system with a shared BDD manager.
    pub fn new(bdd: Rc<Bdd>) -> Self {
        TransitionSystem {
            bdd,
            var_manager: VarManager::new(),
            initial: Ref::INVALID,
            transition: Ref::INVALID,
            labels: HashMap::new(),
        }
    }

    /// Get a reference to the BDD manager.
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
    ///
    /// Allocates two BDD variables (present and next state) via the BDD manager
    /// and registers them with the variable manager.
    pub fn declare_var(&mut self, var: Var) -> (BddVar, BddVar) {
        if let Some(present) = self.var_manager.get_present(&var) {
            let next = self.var_manager.get_next(&var).unwrap();
            return (present, next);
        }
        // Allocate variables through the BDD manager so they have proper levels
        let present = self.bdd.allocate_variable();
        let next = self.bdd.allocate_variable();
        self.var_manager.register_var(var, present, next);
        (present, next)
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

    /// Compute the successor states: `∃s. from(s) ∧ T(s, s')`
    ///
    /// Returns the set of states reachable in one step from `from`.
    pub fn image(&self, from: Ref) -> Ref {
        // ∃s. from(s) ∧ T(s, s')
        let present_vars = self.var_manager.present_vars();
        let result_in_next = self.bdd().rel_product(from, self.transition, present_vars);

        // Rename from next-state to present-state variables
        self.rename_next_to_present(result_in_next)
    }

    /// Compute the predecessor states: `∃s'. T(s, s') ∧ to(s')`
    ///
    /// Returns the set of states that can reach `to` in one step.
    pub fn preimage(&self, to: Ref) -> Ref {
        // Rename to(s) to to(s')
        let to_next = self.rename_present_to_next(to);

        // ∃s'. T(s, s') ∧ to(s')
        let next_vars = self.var_manager.next_vars();
        self.bdd().rel_product(self.transition, to_next, next_vars)
    }

    /// Compute reachable states from initial states
    pub fn reachable(&self) -> Ref {
        let mut reached = self.initial;
        loop {
            let new_states = self.image(reached);
            let new_reached = self.bdd().apply_or(reached, new_states);

            if new_reached == reached {
                return reached;
            }
            reached = new_reached;
        }
    }

    /// Rename present-state variables to next-state variables (v → v').
    fn rename_present_to_next(&self, f: Ref) -> Ref {
        let present_vars = self.var_manager.present_vars();
        let next_vars = self.var_manager.next_vars();

        // v -> v'
        let perm: HashMap<BddVar, BddVar> = present_vars.into_iter().zip(next_vars).collect();

        self.bdd().rename_vars(f, &perm)
    }

    /// Rename next-state variables to present-state variables (v' → v).
    fn rename_next_to_present(&self, f: Ref) -> Ref {
        let present_vars = self.var_manager.present_vars();
        let next_vars = self.var_manager.next_vars();

        // v' -> v
        let perm: HashMap<BddVar, BddVar> = next_vars.into_iter().zip(present_vars).collect();

        self.bdd().rename_vars(f, &perm)
    }

    /// Count the number of states in a state set (up to 2^64)
    pub fn count_states(&self, states: Ref) -> Option<u64> {
        use num_traits::ToPrimitive;
        let num_vars = self.var_manager.present_vars().len();
        let count = self.bdd().sat_count(states, num_vars);
        // Try to convert BigUint to u64
        count.to_u64()
    }

    /// Check if a state set is empty
    pub fn is_empty(&self, states: Ref) -> bool {
        self.bdd().is_zero(states)
    }

    /// Get all states (universe)
    pub fn all_states(&self) -> Ref {
        self.bdd().one()
    }

    /// Create a transition relation constraint for a single variable assignment.
    ///
    /// Converts an assignment `var' := expr` into a relation `var' ↔ expr`.
    ///
    /// # Arguments
    ///
    /// * `var` - The state variable being assigned (present-state version)
    /// * `next_state_expr` - BDD representing the expression for the next state
    ///
    /// # Returns
    ///
    /// A BDD representing the constraint `var' ↔ next_state_expr`
    ///
    /// # Examples
    ///
    /// ```ignore
    /// // For assignment: x' := !x
    /// let x_pres = bdd.mk_var(x_pres_idx);
    /// let next_expr = bdd.apply_not(x_pres);
    /// let constraint = ts.assign_var(&x, next_expr);
    /// // This creates: x' ↔ !x, which is x ⊕ x' (XOR)
    /// ```
    pub fn assign_var(&self, var: &Var, next_state_expr: Ref) -> Ref {
        let next_idx = self.var_manager.get_next(var).expect("Variable not declared in transition system");
        let next_var = self.bdd().mk_var(next_idx);

        // var' ↔ expr  is  (var' ∧ expr) ∨ (¬var' ∧ ¬expr)
        self.bdd().apply_eq(next_var, next_state_expr)
    }

    /// Create a transition relation constraint for an unchanged variable.
    ///
    /// Convenience method for `var' := var`, which creates `var' ↔ var`.
    ///
    /// # Arguments
    ///
    /// * `var` - The state variable that remains unchanged
    ///
    /// # Returns
    ///
    /// A BDD representing the constraint `var' ↔ var`
    pub fn unchanged_var(&self, var: &Var) -> Ref {
        let pres_idx = self
            .var_manager
            .get_present(var)
            .expect("Variable not declared in transition system");
        let pres_var = self.bdd().mk_var(pres_idx);
        self.assign_var(var, pres_var)
    }

    /// Build a complete transition relation from individual variable assignments.
    ///
    /// Combines multiple assignment constraints with AND to form the complete
    /// transition relation. Any variables not mentioned are implicitly unchanged.
    ///
    /// # Arguments
    ///
    /// * `assignments` - Vector of assignment constraints (from `assign_var` or `unchanged_var`)
    ///
    /// # Returns
    ///
    /// A BDD representing T(s, s') = assignment₁ ∧ assignment₂ ∧ ... ∧ assignmentₙ
    ///
    /// # Examples
    ///
    /// ```ignore
    /// // For a 2-bit counter: x' := !x, y' := y ⊕ x
    /// let x_pres = bdd.mk_var(x_pres_idx);
    /// let y_pres = bdd.mk_var(y_pres_idx);
    ///
    /// let x_next_expr = bdd.apply_not(x_pres);  // !x
    /// let y_next_expr = bdd.apply_xor(y_pres, x_pres);  // y ⊕ x
    ///
    /// let transition = ts.build_transition(&[
    ///     ts.assign_var(&x, x_next_expr),
    ///     ts.assign_var(&y, y_next_expr),
    /// ]);
    /// ```
    pub fn build_transition(&self, assignments: &[Ref]) -> Ref {
        self.bdd().apply_and_many(assignments.iter().copied())
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

        // Simulate what TransitionSystem does: allocate then register
        vm.register_var(x.clone(), BddVar::new(1), BddVar::new(2));
        vm.register_var(y.clone(), BddVar::new(3), BddVar::new(4));

        assert_eq!(vm.get_present(&x), Some(BddVar::new(1)));
        assert_eq!(vm.get_next(&x), Some(BddVar::new(2)));
        assert_eq!(vm.get_present(&y), Some(BddVar::new(3)));
        assert_eq!(vm.get_next(&y), Some(BddVar::new(4)));
        assert_eq!(vm.num_vars(), 2);
    }

    #[test]
    fn test_transition_system_basic() {
        let bdd = Rc::new(Bdd::default());
        let mut ts = TransitionSystem::new(bdd.clone());

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
    fn test_reachable() {
        let bdd = Rc::new(Bdd::default());
        let mut ts = TransitionSystem::new(bdd.clone());

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

    #[test]
    fn test_assign_var_helpers() {
        let bdd = Rc::new(Bdd::default());
        let mut ts = TransitionSystem::new(bdd.clone());

        let x = Var::new("x");
        let y = Var::new("y");
        let z = Var::new("z");
        ts.declare_var(x.clone());
        ts.declare_var(y.clone());
        ts.declare_var(z.clone());

        let x_pres = ts.var_manager().get_present(&x).unwrap();
        let y_pres = ts.var_manager().get_present(&y).unwrap();
        let z_pres = ts.var_manager().get_present(&z).unwrap();

        // Build transition using helper functions
        // x' := !x  (toggle x)
        let x_pres_bdd = ts.bdd().mk_var(x_pres);
        let x_next_expr = ts.bdd().apply_not(x_pres_bdd);
        let x_constraint = ts.assign_var(&x, x_next_expr);

        // y' := y ⊕ x  (toggle y when x=1)
        let y_pres_bdd = ts.bdd().mk_var(y_pres);
        let y_next_expr = ts.bdd().apply_xor(y_pres_bdd, x_pres_bdd);
        let y_constraint = ts.assign_var(&y, y_next_expr);

        // z' := z  (z remains unchanged)
        let z_constraint = ts.unchanged_var(&z);

        // Build complete transition relation
        let transition = ts.build_transition(&[x_constraint, y_constraint, z_constraint]);
        ts.set_transition(transition);

        // Initial: x=false, y=false, z=true
        let z_pres_bdd = ts.bdd().mk_var(z_pres);
        let initial = ts.bdd().apply_and(
            ts.bdd().apply_and(ts.bdd().apply_not(x_pres_bdd), ts.bdd().apply_not(y_pres_bdd)),
            z_pres_bdd,
        );
        ts.set_initial(initial);

        // Test that it works correctly
        let reachable = ts.reachable();
        let count = ts.count_states(reachable);
        assert_eq!(count, Some(4)); // Should reach 4 states (z always true)

        // Verify z remains true in all reachable states
        let reachable_implies_z = ts.bdd().apply_imply(reachable, z_pres_bdd);
        assert!(ts.bdd().is_one(reachable_implies_z), "z should remain true in all reachable states");
    }
}
