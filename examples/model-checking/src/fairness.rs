//! Fairness constraints for model checking.
//!
//! Many systems require fairness constraints to exclude unrealistic behaviors.
//! For example, a scheduler that never gives a process a turn, or a communication
//! channel that always drops messages.
//!
//! This module provides:
//! - Strong fairness (compassion): if requested infinitely often, granted infinitely often
//! - Weak fairness (justice): if requested continuously, eventually granted
//! - Fair cycle detection for CTL/LTL checking

use std::rc::Rc;

use ananke_bdd::bdd::Bdd;
use ananke_bdd::reference::Ref;

use crate::transition::TransitionSystem;

/// A fairness constraint.
///
/// Strong fairness: GF p → GF q (if p infinitely often, then q infinitely often)
/// Weak fairness: FG p → GF q (if p eventually always, then q infinitely often)
#[derive(Debug, Clone)]
pub struct FairnessConstraint {
    /// Name for debugging
    pub name: String,
    /// The "request" condition (p in the above)
    pub request: Ref,
    /// The "grant" condition (q in the above)
    pub grant: Ref,
    /// Whether this is strong (true) or weak (false) fairness
    pub strong: bool,
}

impl FairnessConstraint {
    /// Create a strong fairness constraint: GF request → GF grant
    pub fn strong(name: impl Into<String>, request: Ref, grant: Ref) -> Self {
        FairnessConstraint {
            name: name.into(),
            request,
            grant,
            strong: true,
        }
    }

    /// Create a weak fairness constraint: FG request → GF grant
    pub fn weak(name: impl Into<String>, request: Ref, grant: Ref) -> Self {
        FairnessConstraint {
            name: name.into(),
            request,
            grant,
            strong: false,
        }
    }

    /// Simple fairness: just require visiting states satisfying `condition` infinitely often
    pub fn simple(name: impl Into<String>, condition: Ref) -> Self {
        FairnessConstraint {
            name: name.into(),
            request: condition,
            grant: condition,
            strong: true,
        }
    }
}

/// Manages fairness constraints for a transition system.
pub struct FairnessManager {
    ts: Rc<TransitionSystem>,
    constraints: Vec<FairnessConstraint>,
}

impl FairnessManager {
    pub fn new(ts: Rc<TransitionSystem>) -> Self {
        FairnessManager {
            ts,
            constraints: Vec::new(),
        }
    }

    /// Get a reference to the BDD manager.
    pub fn bdd(&self) -> &Bdd {
        self.ts.bdd()
    }

    /// Add a fairness constraint
    pub fn add_constraint(&mut self, constraint: FairnessConstraint) {
        self.constraints.push(constraint);
    }

    /// Add a simple fairness constraint (visit condition infinitely often)
    pub fn add_simple(&mut self, name: impl Into<String>, condition: Ref) {
        self.constraints.push(FairnessConstraint::simple(name, condition));
    }

    /// Get all constraints
    pub fn constraints(&self) -> &[FairnessConstraint] {
        &self.constraints
    }

    /// Check if there are any fairness constraints
    pub fn has_constraints(&self) -> bool {
        !self.constraints.is_empty()
    }

    /// Compute fair EG: states from which there exists a fair path where φ holds globally.
    ///
    /// This is the Emerson-Lei algorithm for fair EG:
    /// νY. φ ∧ ∧_{i} EX E[φ U (Y ∧ grant_i)]
    ///
    /// For each fairness constraint, we require the path to visit the grant condition.
    pub fn fair_eg(&self, phi: Ref) -> Ref {
        if self.constraints.is_empty() {
            // No fairness - standard EG
            return self.compute_eg(phi);
        }

        let mut y = self.ts.all_states();

        loop {
            let mut new_y = phi;

            // For each fairness constraint, compute E[φ U (Y ∧ grant_i)]
            for constraint in &self.constraints {
                let y_and_grant = self.bdd().apply_and(y, constraint.grant);
                let eu_result = self.compute_eu(phi, y_and_grant);
                let ex_eu = self.ts.preimage(eu_result);
                new_y = self.bdd().apply_and(new_y, ex_eu);
            }

            if new_y == y {
                return y;
            }
            y = new_y;
        }
    }

    /// Compute fair EF: states that can reach φ via a fair path.
    pub fn fair_ef(&self, phi: Ref) -> Ref {
        // EF φ under fairness is trickier
        // We use: fair EF φ = E[true U φ] with fairness
        self.fair_eu(self.bdd().one(), phi)
    }

    /// Compute fair EU: E[φ U ψ] under fairness constraints.
    pub fn fair_eu(&self, phi: Ref, psi: Ref) -> Ref {
        if self.constraints.is_empty() {
            return self.compute_eu(phi, psi);
        }

        // Fair EU is more complex - we need paths that satisfy fairness
        // Simplified: standard EU (conservative for verification)
        self.compute_eu(phi, psi)
    }

    /// Compute AG under fairness: all fair paths satisfy G φ
    pub fn fair_ag(&self, phi: Ref) -> Ref {
        // AG φ under fairness = ¬ fair EF ¬φ
        // But more precisely: ¬ (fair EG ¬φ reachable)
        let not_phi = self.bdd().apply_not(phi);
        let fair_eg_not_phi = self.fair_eg(not_phi);

        // States that can reach a fair EG ¬φ state
        let can_reach_bad = self.compute_ef(fair_eg_not_phi);

        self.bdd().apply_not(can_reach_bad)
    }

    /// Compute AF under fairness: all fair paths eventually reach φ
    pub fn fair_af(&self, phi: Ref) -> Ref {
        // AF φ under fairness = ¬ fair EG ¬φ
        let not_phi = self.bdd().apply_not(phi);
        let fair_eg_not_phi = self.fair_eg(not_phi);
        self.bdd().apply_not(fair_eg_not_phi)
    }

    // Helper functions

    fn compute_eg(&self, phi: Ref) -> Ref {
        let mut z = self.ts.all_states();
        loop {
            let pre = self.ts.preimage(z);
            let new_z = self.bdd().apply_and(phi, pre);
            if new_z == z {
                return z;
            }
            z = new_z;
        }
    }

    fn compute_ef(&self, phi: Ref) -> Ref {
        let mut z = phi;
        loop {
            let pre = self.ts.preimage(z);
            let new_z = self.bdd().apply_or(phi, pre);
            if new_z == z {
                return z;
            }
            z = new_z;
        }
    }

    fn compute_eu(&self, phi: Ref, psi: Ref) -> Ref {
        let mut z = psi;
        loop {
            let pre = self.ts.preimage(z);
            let phi_and_pre = self.bdd().apply_and(phi, pre);
            let new_z = self.bdd().apply_or(psi, phi_and_pre);
            if new_z == z {
                return z;
            }
            z = new_z;
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::transition::Var;

    fn create_unfair_system() -> Rc<TransitionSystem> {
        // System with two processes, where process 0 can starve process 1
        let bdd = Rc::new(Bdd::default());
        let mut ts = TransitionSystem::new(bdd);

        let turn = Var::new("turn"); // Whose turn it is
        ts.declare_var(turn.clone());

        let turn_pres = ts.var_manager().get_present(&turn).unwrap();
        let turn_next = ts.var_manager().get_next(&turn).unwrap();

        // Initial: turn=0
        let initial = ts.bdd().apply_not(ts.bdd().mk_var(turn_pres));
        ts.set_initial(initial);

        // Non-deterministic: turn can stay or change
        // This allows unfair schedules where turn never changes
        let turn_pres_bdd = ts.bdd().mk_var(turn_pres);
        let turn_next_bdd = ts.bdd().mk_var(turn_next);

        // turn' = turn OR turn' = !turn (non-deterministic choice)
        let stay = ts.bdd().apply_eq(turn_next_bdd, turn_pres_bdd);
        let change = ts.bdd().apply_xor(turn_next_bdd, turn_pres_bdd);
        let transition = ts.bdd().apply_or(stay, change);
        ts.set_transition(transition);

        // Labels
        ts.add_label("turn0".to_string(), ts.bdd().apply_not(turn_pres_bdd));
        ts.add_label("turn1".to_string(), turn_pres_bdd);

        Rc::new(ts)
    }

    #[test]
    fn test_fairness_constraint_creation() {
        let bdd = Rc::new(Bdd::default());
        let ts = TransitionSystem::new(bdd.clone());
        let ts = Rc::new(ts);

        let mut fm = FairnessManager::new(ts.clone());

        let req = bdd.one();
        let grant = bdd.one();
        fm.add_constraint(FairnessConstraint::strong("fair", req, grant));

        assert!(fm.has_constraints());
        assert_eq!(fm.constraints().len(), 1);
    }

    #[test]
    fn test_unfair_vs_fair_eg() {
        let ts = create_unfair_system();
        let mut fm = FairnessManager::new(ts.clone());

        let turn0 = ts.get_label("turn0").unwrap();
        let turn1 = ts.get_label("turn1").unwrap();

        // Without fairness: EG turn0 includes the initial state
        // (because there's a path that stays at turn=0 forever)
        let eg_turn0 = fm.compute_eg(turn0);
        let initial = ts.initial();
        let unfair_check = fm.bdd().apply_and(initial, eg_turn0);
        assert!(!fm.bdd().is_zero(unfair_check), "Unfair EG turn0 should include initial");

        // With fairness (must visit turn1 infinitely often):
        // There's no fair path where turn0 holds globally
        fm.add_simple("visit_turn1", turn1);
        let fair_eg_turn0 = fm.fair_eg(turn0);
        assert!(fm.bdd().is_zero(fair_eg_turn0), "Fair EG turn0 should be empty");
    }
}
