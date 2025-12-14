//! CTL (Computation Tree Logic) model checking.
//!
//! This module implements symbolic model checking algorithms for CTL formulas.
//! CTL combines path quantifiers (A=all paths, E=exists path) with temporal operators
//! (X=next, F=future, G=globally, U=until).

use std::fmt;
use std::rc::Rc;

use ananke_bdd::bdd::Bdd;
use ananke_bdd::reference::Ref;

use crate::transition::TransitionSystem;

/// CTL formula abstract syntax tree
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CtlFormula {
    /// Atomic proposition
    Atom(String),
    /// True
    True,
    /// False
    False,
    /// Negation
    Not(Box<CtlFormula>),
    /// Conjunction
    And(Box<CtlFormula>, Box<CtlFormula>),
    /// Disjunction
    Or(Box<CtlFormula>, Box<CtlFormula>),
    /// Implication
    Implies(Box<CtlFormula>, Box<CtlFormula>),
    /// Equivalence
    Iff(Box<CtlFormula>, Box<CtlFormula>),

    // CTL-specific operators (path quantifier + temporal operator)
    /// Exists Next: EX φ
    EX(Box<CtlFormula>),
    /// All Next: AX φ
    AX(Box<CtlFormula>),
    /// Exists Future (Eventually): EF φ
    EF(Box<CtlFormula>),
    /// All Future (Eventually): AF φ
    AF(Box<CtlFormula>),
    /// Exists Globally (Always): EG φ
    EG(Box<CtlFormula>),
    /// All Globally (Always): AG φ
    AG(Box<CtlFormula>),
    /// Exists Until: E[φ U ψ]
    EU(Box<CtlFormula>, Box<CtlFormula>),
    /// All Until: A[φ U ψ]
    AU(Box<CtlFormula>, Box<CtlFormula>),
}

impl CtlFormula {
    /// Constructors for convenience
    pub fn atom(s: impl Into<String>) -> Self {
        CtlFormula::Atom(s.into())
    }

    pub fn not(self) -> Self {
        CtlFormula::Not(Box::new(self))
    }

    pub fn and(self, other: Self) -> Self {
        CtlFormula::And(Box::new(self), Box::new(other))
    }

    pub fn or(self, other: Self) -> Self {
        CtlFormula::Or(Box::new(self), Box::new(other))
    }

    pub fn implies(self, other: Self) -> Self {
        CtlFormula::Implies(Box::new(self), Box::new(other))
    }

    pub fn iff(self, other: Self) -> Self {
        CtlFormula::Iff(Box::new(self), Box::new(other))
    }

    pub fn ex(self) -> Self {
        CtlFormula::EX(Box::new(self))
    }

    pub fn ax(self) -> Self {
        CtlFormula::AX(Box::new(self))
    }

    pub fn ef(self) -> Self {
        CtlFormula::EF(Box::new(self))
    }

    pub fn af(self) -> Self {
        CtlFormula::AF(Box::new(self))
    }

    pub fn eg(self) -> Self {
        CtlFormula::EG(Box::new(self))
    }

    pub fn ag(self) -> Self {
        CtlFormula::AG(Box::new(self))
    }

    pub fn eu(self, other: Self) -> Self {
        CtlFormula::EU(Box::new(self), Box::new(other))
    }

    pub fn au(self, other: Self) -> Self {
        CtlFormula::AU(Box::new(self), Box::new(other))
    }
}

impl fmt::Display for CtlFormula {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            CtlFormula::Atom(s) => write!(f, "{}", s),
            CtlFormula::True => write!(f, "true"),
            CtlFormula::False => write!(f, "false"),
            CtlFormula::Not(phi) => write!(f, "¬{}", phi),
            CtlFormula::And(phi, psi) => write!(f, "({} ∧ {})", phi, psi),
            CtlFormula::Or(phi, psi) => write!(f, "({} ∨ {})", phi, psi),
            CtlFormula::Implies(phi, psi) => write!(f, "({} → {})", phi, psi),
            CtlFormula::Iff(phi, psi) => write!(f, "({} ↔ {})", phi, psi),
            CtlFormula::EX(phi) => write!(f, "EX {}", phi),
            CtlFormula::AX(phi) => write!(f, "AX {}", phi),
            CtlFormula::EF(phi) => write!(f, "EF {}", phi),
            CtlFormula::AF(phi) => write!(f, "AF {}", phi),
            CtlFormula::EG(phi) => write!(f, "EG {}", phi),
            CtlFormula::AG(phi) => write!(f, "AG {}", phi),
            CtlFormula::EU(phi, psi) => write!(f, "E[{} U {}]", phi, psi),
            CtlFormula::AU(phi, psi) => write!(f, "A[{} U {}]", phi, psi),
        }
    }
}

/// CTL model checker
pub struct CtlChecker {
    ts: Rc<TransitionSystem>,
}

impl CtlChecker {
    pub fn new(ts: Rc<TransitionSystem>) -> Self {
        CtlChecker { ts }
    }

    /// Get a reference to the BDD manager.
    pub fn bdd(&self) -> &Bdd {
        self.ts.bdd()
    }

    /// Compute the set of states satisfying a CTL formula.
    ///
    /// Returns a BDD representing the characteristic function of the satisfying states.
    pub fn check(&self, formula: &CtlFormula) -> Ref {
        match formula {
            CtlFormula::Atom(p) => {
                // Look up atomic proposition in the labeling function
                self.ts.get_label(p).unwrap_or(self.bdd().zero())
            }
            CtlFormula::True => self.bdd().one(),
            CtlFormula::False => self.bdd().zero(),
            CtlFormula::Not(phi) => {
                let sat_phi = self.check(phi);
                self.bdd().apply_not(sat_phi)
            }
            CtlFormula::And(phi, psi) => {
                let sat_phi = self.check(phi);
                let sat_psi = self.check(psi);
                self.bdd().apply_and(sat_phi, sat_psi)
            }
            CtlFormula::Or(phi, psi) => {
                let sat_phi = self.check(phi);
                let sat_psi = self.check(psi);
                self.bdd().apply_or(sat_phi, sat_psi)
            }
            CtlFormula::Implies(phi, psi) => {
                // φ → ψ ≡ ¬φ ∨ ψ
                let sat_phi = self.check(phi);
                let sat_psi = self.check(psi);
                let not_phi = self.bdd().apply_not(sat_phi);
                self.bdd().apply_or(not_phi, sat_psi)
            }
            CtlFormula::Iff(phi, psi) => {
                // φ ↔ ψ ≡ (φ → ψ) ∧ (ψ → φ) ≡ (φ ∧ ψ) ∨ (¬φ ∧ ¬ψ)
                let sat_phi = self.check(phi);
                let sat_psi = self.check(psi);
                // XNOR: (a ∧ b) ∨ (¬a ∧ ¬b) ≡ ¬(a XOR b)
                let xor = self.bdd().apply_xor(sat_phi, sat_psi);
                self.bdd().apply_not(xor)
            }
            CtlFormula::EX(phi) => self.check_ex(phi),
            CtlFormula::AX(phi) => self.check_ax(phi),
            CtlFormula::EF(phi) => self.check_ef(phi),
            CtlFormula::AF(phi) => self.check_af(phi),
            CtlFormula::EG(phi) => self.check_eg(phi),
            CtlFormula::AG(phi) => self.check_ag(phi),
            CtlFormula::EU(phi, psi) => self.check_eu(phi, psi),
            CtlFormula::AU(phi, psi) => self.check_au(phi, psi),
        }
    }

    /// EX φ: States that have at least one successor satisfying φ
    ///
    /// SAT(EX φ) = preimage(SAT(φ))
    fn check_ex(&self, phi: &CtlFormula) -> Ref {
        let sat_phi = self.check(phi);
        self.ts.preimage(sat_phi)
    }

    /// AX φ: States where all successors satisfy φ
    ///
    /// SAT(AX φ) = ¬SAT(EX ¬φ)
    fn check_ax(&self, phi: &CtlFormula) -> Ref {
        let not_phi = CtlFormula::Not(Box::new(phi.clone()));
        let sat_ex_not_phi = self.check_ex(&not_phi);
        self.bdd().apply_not(sat_ex_not_phi)
    }

    /// EF φ: States from which φ is reachable (exists a path to φ)
    ///
    /// Least fixpoint: µZ. φ ∨ EX Z
    fn check_ef(&self, phi: &CtlFormula) -> Ref {
        let sat_phi = self.check(phi);
        let mut z = sat_phi;

        loop {
            let ex_z = self.ts.preimage(z);
            let new_z = self.bdd().apply_or(sat_phi, ex_z);

            if new_z == z {
                return z;
            }
            z = new_z;
        }
    }

    /// AF φ: States from which all paths eventually reach φ
    ///
    /// Least fixpoint: µZ. φ ∨ AX Z
    fn check_af(&self, phi: &CtlFormula) -> Ref {
        let sat_phi = self.check(phi);
        let mut z = sat_phi;

        loop {
            // AX Z = ¬EX ¬Z
            let not_z = self.bdd().apply_not(z);
            let ex_not_z = self.ts.preimage(not_z);
            let ax_z = self.bdd().apply_not(ex_not_z);

            let new_z = self.bdd().apply_or(sat_phi, ax_z);

            if new_z == z {
                return z;
            }
            z = new_z;
        }
    }

    /// EG φ: States from which there exists a path where φ holds globally
    ///
    /// Greatest fixpoint: νZ. φ ∧ EX Z
    fn check_eg(&self, phi: &CtlFormula) -> Ref {
        let sat_phi = self.check(phi);
        let mut z = self.ts.all_states(); // Start from all states

        loop {
            let ex_z = self.ts.preimage(z);
            let new_z = self.bdd().apply_and(sat_phi, ex_z);

            if new_z == z {
                return z;
            }
            z = new_z;
        }
    }

    /// AG φ: States from which φ holds on all paths globally
    ///
    /// Greatest fixpoint: νZ. φ ∧ AX Z
    fn check_ag(&self, phi: &CtlFormula) -> Ref {
        let sat_phi = self.check(phi);
        let mut z = self.ts.all_states();

        loop {
            // AX Z
            let not_z = self.bdd().apply_not(z);
            let ex_not_z = self.ts.preimage(not_z);
            let ax_z = self.bdd().apply_not(ex_not_z);

            let new_z = self.bdd().apply_and(sat_phi, ax_z);

            if new_z == z {
                return z;
            }
            z = new_z;
        }
    }

    /// E[φ U ψ]: States from which there exists a path where φ holds until ψ
    ///
    /// Least fixpoint: µZ. ψ ∨ (φ ∧ EX Z)
    fn check_eu(&self, phi: &CtlFormula, psi: &CtlFormula) -> Ref {
        let sat_phi = self.check(phi);
        let sat_psi = self.check(psi);
        let mut z = sat_psi;

        loop {
            let ex_z = self.ts.preimage(z);
            let phi_and_ex_z = self.bdd().apply_and(sat_phi, ex_z);
            let new_z = self.bdd().apply_or(sat_psi, phi_and_ex_z);

            if new_z == z {
                return z;
            }
            z = new_z;
        }
    }

    /// A[φ U ψ]: States from which on all paths φ holds until ψ
    ///
    /// Least fixpoint: µZ. ψ ∨ (φ ∧ AX Z)
    fn check_au(&self, phi: &CtlFormula, psi: &CtlFormula) -> Ref {
        let sat_phi = self.check(phi);
        let sat_psi = self.check(psi);
        let mut z = sat_psi;

        loop {
            // AX Z
            let not_z = self.bdd().apply_not(z);
            let ex_not_z = self.ts.preimage(not_z);
            let ax_z = self.bdd().apply_not(ex_not_z);

            let phi_and_ax_z = self.bdd().apply_and(sat_phi, ax_z);
            let new_z = self.bdd().apply_or(sat_psi, phi_and_ax_z);

            if new_z == z {
                return z;
            }
            z = new_z;
        }
    }

    /// Check if a formula holds in all initial states
    pub fn holds_initially(&self, formula: &CtlFormula) -> bool {
        let sat = self.check(formula);
        let initial = self.ts.initial();
        // Check if initial ⊆ sat  ⟺  initial ∧ ¬sat = ∅
        let not_sat = self.bdd().apply_not(sat);
        let violation = self.bdd().apply_and(initial, not_sat);
        self.bdd().is_zero(violation)
    }

    /// Get states where formula is violated (formula is false)
    pub fn get_violations(&self, formula: &CtlFormula) -> Ref {
        let sat = self.check(formula);
        self.bdd().apply_not(sat)
    }
}

#[cfg(test)]
mod tests {
    use std::rc::Rc;

    use ananke_bdd::bdd::Bdd;

    use super::*;
    use crate::transition::{TransitionSystem, Var};

    // Helper: Create a 2-state toggle system
    // States: {0, 1}, initial: {0}, transition: 0->1, 1->0
    fn create_toggle_system() -> Rc<TransitionSystem> {
        let bdd = Rc::new(Bdd::default());
        let mut ts = TransitionSystem::new(bdd);

        let x = Var::new("x");
        ts.declare_var(x.clone());

        let x_pres = ts.var_manager().get_present(&x).unwrap();
        let x_next = ts.var_manager().get_next(&x).unwrap();

        // Initial: x=0
        let initial = ts.bdd().apply_not(ts.bdd().mk_var(x_pres));
        ts.set_initial(initial);

        // Transition: x' = !x
        let x_pres_bdd = ts.bdd().mk_var(x_pres);
        let x_next_bdd = ts.bdd().mk_var(x_next);
        let transition = ts.bdd().apply_xor(x_pres_bdd, x_next_bdd);
        ts.set_transition(transition);

        // Label "zero" = {x=0}, "one" = {x=1}
        ts.add_label("zero".to_string(), ts.bdd().apply_not(x_pres_bdd));
        ts.add_label("one".to_string(), x_pres_bdd);

        Rc::new(ts)
    }

    #[test]
    fn test_ctl_atoms() {
        let ts = create_toggle_system();
        let checker = CtlChecker::new(ts.clone());

        let zero = CtlFormula::atom("zero");
        let one = CtlFormula::atom("one");

        let sat_zero = checker.check(&zero);
        let sat_one = checker.check(&one);

        // zero and one should be disjoint
        let overlap = ts.bdd().apply_and(sat_zero, sat_one);
        assert!(ts.bdd().is_zero(overlap));

        // zero ∨ one should be all states
        let union = ts.bdd().apply_or(sat_zero, sat_one);
        assert_eq!(union, ts.all_states());
    }

    #[test]
    fn test_ctl_ex() {
        let ts = create_toggle_system();
        let checker = CtlChecker::new(ts.clone());

        // EX one: states where next state is "one"
        // From state 0, we go to state 1, so state 0 satisfies EX one
        let ex_one = CtlFormula::atom("one").ex();
        let sat = checker.check(&ex_one);

        let zero_bdd = checker.check(&CtlFormula::atom("zero"));
        assert_eq!(sat, zero_bdd);
    }

    #[test]
    fn test_ctl_ax() {
        let ts = create_toggle_system();
        let checker = CtlChecker::new(ts.clone());

        // AX one: all successors are "one"
        // State 0 -> 1 (yes), State 1 -> 0 (no)
        let ax_one = CtlFormula::atom("one").ax();
        let sat = checker.check(&ax_one);

        let zero_bdd = checker.check(&CtlFormula::atom("zero"));
        assert_eq!(sat, zero_bdd);
    }

    #[test]
    fn test_ctl_ef() {
        let ts = create_toggle_system();
        let checker = CtlChecker::new(ts.clone());

        // EF one: can eventually reach "one"
        // Both states can reach "one" (state 1 is already "one", state 0 reaches it in 1 step)
        let ef_one = CtlFormula::atom("one").ef();
        let sat = checker.check(&ef_one);

        assert_eq!(sat, ts.all_states());
    }

    #[test]
    fn test_ctl_af() {
        let ts = create_toggle_system();
        let checker = CtlChecker::new(ts.clone());

        // AF one: all paths eventually reach "one"
        // State 0: next is 1 (reaches "one")
        // State 1: is already "one"
        let af_one = CtlFormula::atom("one").af();
        let sat = checker.check(&af_one);

        assert_eq!(sat, ts.all_states());
    }

    #[test]
    fn test_ctl_eg() {
        let ts = create_toggle_system();
        let checker = CtlChecker::new(ts.clone());

        // EG zero: exists a path where "zero" holds globally
        // This is false because from state 0, we must go to state 1
        let eg_zero = CtlFormula::atom("zero").eg();
        let sat = checker.check(&eg_zero);

        assert!(ts.bdd().is_zero(sat));
    }

    #[test]
    fn test_ctl_ag() {
        let ts = create_toggle_system();
        let checker = CtlChecker::new(ts.clone());

        // AG true: true holds globally on all paths
        let ag_true = CtlFormula::True.ag();
        let sat = checker.check(&ag_true);

        assert_eq!(sat, ts.all_states());

        // AG zero: "zero" holds globally on all paths
        // This is false because we eventually reach state 1
        let ag_zero = CtlFormula::atom("zero").ag();
        let sat = checker.check(&ag_zero);

        assert!(ts.bdd().is_zero(sat));
    }

    #[test]
    fn test_ctl_eu() {
        let ts = create_toggle_system();
        let checker = CtlChecker::new(ts.clone());

        // E[true U one]: exists path where true until "one"
        // This is equivalent to EF one
        let eu = CtlFormula::True.eu(CtlFormula::atom("one"));
        let sat = checker.check(&eu);

        assert_eq!(sat, ts.all_states());
    }

    #[test]
    fn test_ctl_holds_initially() {
        let ts = create_toggle_system();
        let checker = CtlChecker::new(ts.clone());

        // Initially we are in state "zero"
        let zero = CtlFormula::atom("zero");
        assert!(checker.holds_initially(&zero));

        let one = CtlFormula::atom("one");
        assert!(!checker.holds_initially(&one));

        // AF one: will eventually reach "one"
        let af_one = CtlFormula::atom("one").af();
        assert!(checker.holds_initially(&af_one));
    }
}
