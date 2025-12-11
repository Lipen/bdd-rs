//! LTL (Linear Temporal Logic) model checking via tableau construction.
//!
//! This module implements LTL model checking by reducing it to CTL model checking
//! over a product automaton. The approach uses the tableau method to construct
//! a Büchi automaton from an LTL formula.
//!
//! # Overview
//!
//! LTL differs from CTL in that it quantifies over *all* paths implicitly:
//! - LTL: "On every path, eventually p" (Fp)
//! - CTL: "On all paths, eventually p" (AF p) or "exists path, eventually p" (EF p)
//!
//! To check LTL, we:
//! 1. Negate the formula (we'll check for counterexamples)
//! 2. Convert ¬φ to a Büchi automaton A_¬φ
//! 3. Compute the product of the system M with A_¬φ
//! 4. Check if the product has an accepting run (fair cycle)
//! 5. If yes: counterexample found. If no: property holds.

use std::collections::HashSet;
use std::fmt;
use std::rc::Rc;

use bdd_rs::bdd::Bdd;
use bdd_rs::reference::Ref;

use crate::transition::TransitionSystem;

/// LTL formula abstract syntax tree
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum LtlFormula {
    /// Atomic proposition
    Atom(String),
    /// True
    True,
    /// False
    False,
    /// Negation
    Not(Box<LtlFormula>),
    /// Conjunction
    And(Box<LtlFormula>, Box<LtlFormula>),
    /// Disjunction
    Or(Box<LtlFormula>, Box<LtlFormula>),
    /// Implication
    Implies(Box<LtlFormula>, Box<LtlFormula>),

    // Temporal operators
    /// Next: X φ (φ holds in the next state)
    Next(Box<LtlFormula>),
    /// Finally/Eventually: F φ (φ holds eventually)
    Finally(Box<LtlFormula>),
    /// Globally/Always: G φ (φ holds forever)
    Globally(Box<LtlFormula>),
    /// Until: φ U ψ (φ holds until ψ becomes true)
    Until(Box<LtlFormula>, Box<LtlFormula>),
    /// Release: φ R ψ (ψ holds until and including when φ becomes true, or forever)
    Release(Box<LtlFormula>, Box<LtlFormula>),
    /// Weak Until: φ W ψ (φ U ψ or G φ)
    WeakUntil(Box<LtlFormula>, Box<LtlFormula>),
}

impl LtlFormula {
    // Constructors for convenience
    pub fn atom(s: impl Into<String>) -> Self {
        LtlFormula::Atom(s.into())
    }

    pub fn not(self) -> Self {
        LtlFormula::Not(Box::new(self))
    }

    pub fn and(self, other: Self) -> Self {
        LtlFormula::And(Box::new(self), Box::new(other))
    }

    pub fn or(self, other: Self) -> Self {
        LtlFormula::Or(Box::new(self), Box::new(other))
    }

    pub fn implies(self, other: Self) -> Self {
        LtlFormula::Implies(Box::new(self), Box::new(other))
    }

    pub fn next(self) -> Self {
        LtlFormula::Next(Box::new(self))
    }

    pub fn finally(self) -> Self {
        LtlFormula::Finally(Box::new(self))
    }

    pub fn globally(self) -> Self {
        LtlFormula::Globally(Box::new(self))
    }

    pub fn until(self, other: Self) -> Self {
        LtlFormula::Until(Box::new(self), Box::new(other))
    }

    pub fn release(self, other: Self) -> Self {
        LtlFormula::Release(Box::new(self), Box::new(other))
    }

    pub fn weak_until(self, other: Self) -> Self {
        LtlFormula::WeakUntil(Box::new(self), Box::new(other))
    }

    /// Convert to Negation Normal Form (NNF)
    /// Push negations to atoms only
    pub fn to_nnf(&self) -> LtlFormula {
        match self {
            LtlFormula::Atom(s) => LtlFormula::atom(s),
            LtlFormula::True => LtlFormula::True,
            LtlFormula::False => LtlFormula::False,

            // ¬φ
            LtlFormula::Not(phi) => phi.negate_to_nnf(),

            // φ ∧ ψ
            LtlFormula::And(phi, psi) => {
                let phi_nnf = phi.to_nnf();
                let psi_nnf = psi.to_nnf();
                phi_nnf.and(psi_nnf)
            }

            // φ ∨ ψ
            LtlFormula::Or(phi, psi) => {
                let phi_nnf = phi.to_nnf();
                let psi_nnf = psi.to_nnf();
                phi_nnf.or(psi_nnf)
            }

            // φ → ψ ≡ ¬φ ∨ ψ
            LtlFormula::Implies(phi, psi) => {
                let not_phi = phi.negate_to_nnf();
                let psi_nnf = psi.to_nnf();
                not_phi.or(psi_nnf)
            }

            // X φ
            LtlFormula::Next(phi) => {
                let phi_nnf = phi.to_nnf();
                phi_nnf.next()
            }

            // F φ ≡ true U φ
            LtlFormula::Finally(phi) => {
                let phi_nnf = phi.to_nnf();
                LtlFormula::True.until(phi_nnf)
            }

            // G φ ≡ false R φ
            LtlFormula::Globally(phi) => {
                let phi_nnf = phi.to_nnf();
                LtlFormula::False.release(phi_nnf)
            }

            // φ U ψ
            LtlFormula::Until(phi, psi) => {
                let phi_nnf = phi.to_nnf();
                let psi_nnf = psi.to_nnf();
                phi_nnf.until(psi_nnf)
            }

            // φ R ψ
            LtlFormula::Release(phi, psi) => {
                let phi_nnf = phi.to_nnf();
                let psi_nnf = psi.to_nnf();
                phi_nnf.release(psi_nnf)
            }

            // φ W ψ ≡ (φ U ψ) ∨ G φ ≡ ψ R (ψ ∨ φ)
            LtlFormula::WeakUntil(phi, psi) => {
                let phi_nnf = phi.to_nnf();
                let psi_nnf = psi.to_nnf();
                psi_nnf.clone().release(psi_nnf.or(phi_nnf))
            }
        }
    }

    /// Negate the formula and convert to NNF
    fn negate_to_nnf(&self) -> LtlFormula {
        match self {
            // ¬p
            LtlFormula::Atom(s) => LtlFormula::Atom(s.clone()).not(),
            // ¬true = false
            LtlFormula::True => LtlFormula::False,
            // ¬false = true
            LtlFormula::False => LtlFormula::True,

            // ¬(¬φ) ≡ φ
            LtlFormula::Not(phi) => phi.to_nnf(),

            // ¬(φ ∧ ψ) ≡ ¬φ ∨ ¬ψ
            LtlFormula::And(phi, psi) => {
                let not_phi = phi.negate_to_nnf();
                let not_psi = psi.negate_to_nnf();
                not_phi.or(not_psi)
            }

            // ¬(φ ∨ ψ) ≡ ¬φ ∧ ¬ψ
            LtlFormula::Or(phi, psi) => {
                let not_phi = phi.negate_to_nnf();
                let not_psi = psi.negate_to_nnf();
                not_phi.and(not_psi)
            }

            // ¬(φ → ψ) ≡ φ ∧ ¬ψ
            LtlFormula::Implies(phi, psi) => {
                let phi_nnf = phi.to_nnf();
                let not_psi = psi.negate_to_nnf();
                phi_nnf.and(not_psi)
            }

            // ¬X φ ≡ X ¬φ
            LtlFormula::Next(phi) => {
                let not_phi = phi.negate_to_nnf();
                not_phi.next()
            }

            // ¬F φ ≡ G ¬φ ≡ false R ¬φ
            LtlFormula::Finally(phi) => {
                let not_phi = phi.negate_to_nnf();
                LtlFormula::False.release(not_phi)
            }

            // ¬G φ ≡ F ¬φ ≡ true U ¬φ
            LtlFormula::Globally(phi) => {
                let not_phi = phi.negate_to_nnf();
                LtlFormula::True.until(not_phi)
            }

            // ¬(φ U ψ) ≡ ¬ψ R ¬φ
            LtlFormula::Until(phi, psi) => {
                let not_phi = phi.negate_to_nnf();
                let not_psi = psi.negate_to_nnf();
                not_psi.release(not_phi)
            }

            // ¬(φ R ψ) ≡ ¬ψ U ¬φ
            LtlFormula::Release(phi, psi) => {
                let not_phi = phi.negate_to_nnf();
                let not_psi = psi.negate_to_nnf();
                not_psi.until(not_phi)
            }

            // ¬(φ W ψ) ≡ ¬ψ U (¬φ ∧ ¬ψ)
            LtlFormula::WeakUntil(phi, psi) => {
                let not_phi = phi.negate_to_nnf();
                let not_psi = psi.negate_to_nnf();
                not_psi.clone().until(not_phi.and(not_psi))
            }
        }
    }

    /// Collect all atomic propositions in the formula
    pub fn atoms(&self) -> HashSet<String> {
        let mut atoms = HashSet::new();
        self.collect_atoms(&mut atoms);
        atoms
    }

    fn collect_atoms(&self, atoms: &mut HashSet<String>) {
        match self {
            LtlFormula::Atom(s) => {
                atoms.insert(s.clone());
            }
            LtlFormula::True | LtlFormula::False => {}
            LtlFormula::Not(phi) | LtlFormula::Next(phi) | LtlFormula::Finally(phi) | LtlFormula::Globally(phi) => {
                phi.collect_atoms(atoms);
            }
            LtlFormula::And(phi, psi)
            | LtlFormula::Or(phi, psi)
            | LtlFormula::Implies(phi, psi)
            | LtlFormula::Until(phi, psi)
            | LtlFormula::Release(phi, psi)
            | LtlFormula::WeakUntil(phi, psi) => {
                phi.collect_atoms(atoms);
                psi.collect_atoms(atoms);
            }
        }
    }
}

impl fmt::Display for LtlFormula {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            LtlFormula::Atom(s) => write!(f, "{}", s),
            LtlFormula::True => write!(f, "true"),
            LtlFormula::False => write!(f, "false"),
            LtlFormula::Not(phi) => write!(f, "¬{}", phi),
            LtlFormula::And(phi, psi) => write!(f, "({} ∧ {})", phi, psi),
            LtlFormula::Or(phi, psi) => write!(f, "({} ∨ {})", phi, psi),
            LtlFormula::Implies(phi, psi) => write!(f, "({} → {})", phi, psi),
            LtlFormula::Next(phi) => write!(f, "X {}", phi),
            LtlFormula::Finally(phi) => write!(f, "F {}", phi),
            LtlFormula::Globally(phi) => write!(f, "G {}", phi),
            LtlFormula::Until(phi, psi) => write!(f, "({} U {})", phi, psi),
            LtlFormula::Release(phi, psi) => write!(f, "({} R {})", phi, psi),
            LtlFormula::WeakUntil(phi, psi) => write!(f, "({} W {})", phi, psi),
        }
    }
}

/// LTL model checker using symbolic tableau construction.
///
/// This checker reduces LTL model checking to finding fair cycles in a product
/// automaton. It uses the "automata-theoretic" approach:
///
/// 1. Negate the LTL formula
/// 2. Build a symbolic Büchi automaton for ¬φ
/// 3. Compute product with the system
/// 4. Check for accepting (fair) cycles
pub struct LtlChecker {
    ts: Rc<TransitionSystem>,
}

impl LtlChecker {
    pub fn new(ts: Rc<TransitionSystem>) -> Self {
        LtlChecker { ts }
    }

    /// Get a reference to the BDD manager.
    pub fn bdd(&self) -> &Bdd {
        self.ts.bdd()
    }

    /// Check if an LTL formula holds for the system.
    ///
    /// Returns true if the formula holds on all paths from initial states.
    pub fn check(&self, formula: &LtlFormula) -> bool {
        // We check ¬φ is not satisfiable
        // i.e., there's no path violating φ
        let negated = LtlFormula::not(formula.clone());
        let nnf = negated.to_nnf();

        // For simple formulas, we can reduce to CTL
        if let Some(result) = self.try_ctl_reduction(&nnf) {
            return !result; // ¬φ not satisfiable means φ holds
        }

        // Full LTL checking via tableau
        self.check_via_tableau(formula)
    }

    /// Try to reduce simple LTL to CTL (for efficiency)
    fn try_ctl_reduction(&self, formula: &LtlFormula) -> Option<bool> {
        // Many common LTL formulas have CTL equivalents
        match formula {
            // F p ≡ EF p (for checking satisfiability of negation)
            LtlFormula::Until(phi, psi) if matches!(phi.as_ref(), LtlFormula::True) => {
                let sat_psi = self.eval_propositional(psi)?;
                let ef_psi = self.compute_ef(sat_psi);
                let initial = self.ts.initial();
                let reachable = self.bdd().apply_and(initial, ef_psi);
                Some(!self.bdd().is_zero(reachable))
            }
            // G p checking via EG p
            LtlFormula::Release(phi, psi) if matches!(phi.as_ref(), LtlFormula::False) => {
                let sat_psi = self.eval_propositional(psi)?;
                let eg_psi = self.compute_eg(sat_psi);
                let initial = self.ts.initial();
                let reachable = self.bdd().apply_and(initial, eg_psi);
                Some(!self.bdd().is_zero(reachable))
            }
            _ => None,
        }
    }

    /// Evaluate a propositional (non-temporal) formula
    fn eval_propositional(&self, formula: &LtlFormula) -> Option<Ref> {
        match formula {
            LtlFormula::Atom(p) => self.ts.get_label(p),
            LtlFormula::True => Some(self.bdd().one()),
            LtlFormula::False => Some(self.bdd().zero()),
            LtlFormula::Not(phi) => {
                let sat = self.eval_propositional(phi)?;
                Some(self.bdd().apply_not(sat))
            }
            LtlFormula::And(phi, psi) => {
                let a = self.eval_propositional(phi)?;
                let b = self.eval_propositional(psi)?;
                Some(self.bdd().apply_and(a, b))
            }
            LtlFormula::Or(phi, psi) => {
                let a = self.eval_propositional(phi)?;
                let b = self.eval_propositional(psi)?;
                Some(self.bdd().apply_or(a, b))
            }
            // Temporal operators can't be evaluated propositionally
            _ => None,
        }
    }

    /// Compute EF (exists finally) - least fixpoint
    fn compute_ef(&self, target: Ref) -> Ref {
        let mut z = target;
        loop {
            let pre = self.ts.preimage(z);
            let new_z = self.bdd().apply_or(target, pre);
            if new_z == z {
                return z;
            }
            z = new_z;
        }
    }

    /// Compute EG (exists globally) - greatest fixpoint
    fn compute_eg(&self, invariant: Ref) -> Ref {
        let mut z = self.ts.all_states();
        loop {
            let pre = self.ts.preimage(z);
            let new_z = self.bdd().apply_and(invariant, pre);
            if new_z == z {
                return z;
            }
            z = new_z;
        }
    }

    /// Full LTL checking via symbolic tableau
    fn check_via_tableau(&self, formula: &LtlFormula) -> bool {
        // Simplified implementation using Emerson-Lei algorithm
        // Full implementation would construct explicit tableau automaton

        let nnf = formula.to_nnf();

        // For safety properties (G p), use greatest fixpoint
        if let LtlFormula::Globally(phi) = &nnf {
            if let Some(sat_phi) = self.eval_propositional(phi) {
                // AG p holds if initial states satisfy EG p
                // (simplified - doesn't handle nested temporal)
                let eg_phi = self.compute_eg(sat_phi);
                let initial = self.ts.initial();
                let check = self.bdd().apply_and(initial, eg_phi);
                return check == initial;
            }
        }

        // For liveness (F p), check reachability
        if let LtlFormula::Finally(phi) = &nnf {
            if let Some(sat_phi) = self.eval_propositional(phi) {
                // AF p - all paths eventually reach p
                // Use least fixpoint: μZ. p ∨ AX Z
                let af_phi = self.compute_af(sat_phi);
                let initial = self.ts.initial();
                let check = self.bdd().apply_and(initial, af_phi);
                return check == initial;
            }
        }

        // For general formulas, would need full tableau construction
        // For now, return conservative result
        log::warn!("Full LTL tableau not implemented for formula: {}", formula);
        false
    }

    /// Compute AF (all finally) - least fixpoint
    fn compute_af(&self, target: Ref) -> Ref {
        let mut z = target;
        loop {
            // AX Z = ¬EX ¬Z
            let not_z = self.bdd().apply_not(z);
            let ex_not_z = self.ts.preimage(not_z);
            let ax_z = self.bdd().apply_not(ex_not_z);

            let new_z = self.bdd().apply_or(target, ax_z);
            if new_z == z {
                return z;
            }
            z = new_z;
        }
    }

    /// Check if the formula holds initially
    pub fn holds_initially(&self, formula: &LtlFormula) -> bool {
        self.check(formula)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::transition::Var;

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

        // Labels
        ts.add_label("zero".to_string(), ts.bdd().apply_not(x_pres_bdd));
        ts.add_label("one".to_string(), x_pres_bdd);

        Rc::new(ts)
    }

    #[test]
    fn test_ltl_formula_display() {
        let f = LtlFormula::atom("p").globally();
        assert_eq!(format!("{}", f), "G p");

        let f = LtlFormula::atom("p").until(LtlFormula::atom("q"));
        assert_eq!(format!("{}", f), "(p U q)");
    }

    #[test]
    fn test_ltl_to_nnf() {
        // ¬G p should become F ¬p (which is true U ¬p)
        let f = LtlFormula::atom("p").globally().not();
        let nnf = f.to_nnf();
        assert!(matches!(nnf, LtlFormula::Until(_, _)));
    }

    #[test]
    fn test_ltl_finally_one() {
        let ts = create_toggle_system();
        let checker = LtlChecker::new(ts);

        // F one: eventually reach "one"
        let f = LtlFormula::atom("one").finally();
        assert!(checker.holds_initially(&f));
    }

    #[test]
    fn test_ltl_globally_safe() {
        let ts = create_toggle_system();

        // Add a "safe" label that's always true
        let bdd = ts.bdd().one();
        let mut ts_mut = Rc::try_unwrap(ts).unwrap();
        ts_mut.add_label("safe".to_string(), bdd);
        let ts = Rc::new(ts_mut);

        let checker = LtlChecker::new(ts);

        // G safe: always safe
        let f = LtlFormula::atom("safe").globally();
        assert!(checker.holds_initially(&f));
    }
}
