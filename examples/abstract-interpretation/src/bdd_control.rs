//! BDD Control Domain: Path-Sensitive Abstract Interpretation
//!
//! This module implements a BDD-based control domain for path-sensitive static analysis.
//! The key idea is to partition program states based on Boolean control variables (flags,
//! mode indicators, branch conditions) and maintain separate numeric invariants for each
//! control partition.
//!
//! # Theory
//!
//! The BDD Control Domain is defined as:
//!
//! ```text
//! D_BDD = (E_BDD, ⊑, ⊔, ⊓, ∇, ⊥, ⊤)
//! ```
//!
//! Where:
//! - **Elements**: BDDs over Boolean control variables
//! - **Partial Order**: φ₁ ⊑ φ₂ ⟺ φ₁ ⇒ φ₂ (logical implication)
//! - **Join**: φ₁ ⊔ φ₂ = φ₁ ∨ φ₂ (disjunction)
//! - **Meet**: φ₁ ⊓ φ₂ = φ₁ ∧ φ₂ (conjunction)
//! - **Bottom**: false (unreachable)
//! - **Top**: true (all paths reachable)
//!
//! # Example
//!
//! ```rust
//! use abstract_interpretation::*;
//! use std::rc::Rc;
//!
//! // Create BDD control domain
//! let domain = BddControlDomain::new();
//!
//! // Allocate control variable "flag"
//! let var_id = domain.allocate_var("flag");
//!
//! // Create control state: flag = true
//! let state_true = domain.mk_var_true("flag");
//! let state_false = domain.mk_var_false("flag");
//!
//! // Join: flag could be true OR false
//! let state_any = domain.join(&state_true, &state_false);
//! assert!(domain.is_top(&state_any)); // true (no constraint)
//!
//! // Meet: flag is both true AND false (contradiction)
//! let state_bot = domain.meet(&state_true, &state_false);
//! assert!(domain.is_bottom(&state_bot)); // unreachable
//! ```
//!
//! # Architecture
//!
//! The control domain works with any numeric domain through the product construction:
//!
//! ```text
//! ControlSensitiveProduct = BddControlDomain × NumericDomain
//! ```
//!
//! This allows maintaining separate numeric invariants per control path.

use super::domain::AbstractDomain;
use bdd_rs::bdd::Bdd;
use bdd_rs::reference::Ref;
use std::cell::RefCell;
use std::collections::HashMap;
use std::fmt;
use std::rc::Rc;

/// A control state represented as a BDD over Boolean control variables.
///
/// # Interpretation
///
/// A control state `φ` represents a set of control paths. The BDD evaluates to:
/// - `true` (1): This control path is reachable
/// - `false` (0): This control path is unreachable/infeasible
///
/// # Examples
///
/// - `φ = true`: All control paths (no constraints)
/// - `φ = false`: No control paths (unreachable)
/// - `φ = (flag = true)`: Only paths where flag is true
/// - `φ = (flag₁ = true) ∧ (flag₂ = false)`: Specific control configuration
///
/// # Representation
///
/// Internally uses BDD reference (`Ref`) which is a 32-bit integer index into
/// the shared BDD manager's node table.
#[derive(Clone)]
pub struct ControlState {
    /// BDD representing the control constraint
    bdd_ref: Ref,
    /// Shared BDD manager
    manager: Rc<Bdd>,
    /// Human-readable description (for debugging)
    description: Option<String>,
}

impl ControlState {
    /// Create a new control state from a BDD reference.
    pub fn new(bdd_ref: Ref, manager: Rc<Bdd>) -> Self {
        Self {
            bdd_ref,
            manager,
            description: None,
        }
    }

    /// Create a control state with a description.
    pub fn with_description(mut self, desc: String) -> Self {
        self.description = Some(desc);
        self
    }

    /// Get the BDD reference.
    pub fn bdd_ref(&self) -> Ref {
        self.bdd_ref
    }

    /// Get the shared BDD manager.
    pub fn manager(&self) -> &Rc<Bdd> {
        &self.manager
    }

    /// Check if this control state is satisfiable (not false).
    pub fn is_sat(&self) -> bool {
        self.bdd_ref != self.manager.zero
    }

    /// Check if this control state is a tautology (true).
    pub fn is_tautology(&self) -> bool {
        self.bdd_ref == self.manager.one
    }

    /// Check if this control state is satisfiable (has at least one solution).
    ///
    /// This is a simpler alternative to counting satisfying assignments.
    /// Returns true if there exists at least one control configuration satisfying this state.
    pub fn has_solution(&self) -> bool {
        self.is_sat()
    }

    /// Get description if available.
    pub fn description(&self) -> Option<&str> {
        self.description.as_deref()
    }
}

impl PartialEq for ControlState {
    fn eq(&self, other: &Self) -> bool {
        // Two control states are equal if they represent the same BDD
        // BDD nodes are canonical, so reference equality is sufficient
        self.bdd_ref == other.bdd_ref
    }
}

impl Eq for ControlState {}

impl fmt::Debug for ControlState {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if let Some(desc) = &self.description {
            write!(f, "ControlState({})", desc)
        } else if self.bdd_ref == self.manager.zero {
            write!(f, "ControlState(⊥)")
        } else if self.bdd_ref == self.manager.one {
            write!(f, "ControlState(⊤)")
        } else {
            write!(f, "ControlState(BDD:{})", self.bdd_ref)
        }
    }
}

impl fmt::Display for ControlState {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if let Some(desc) = &self.description {
            write!(f, "{}", desc)
        } else if self.bdd_ref == self.manager.zero {
            write!(f, "⊥")
        } else if self.bdd_ref == self.manager.one {
            write!(f, "⊤")
        } else {
            write!(f, "BDD({})", self.bdd_ref)
        }
    }
}

/// BDD-based control domain for path-sensitive analysis.
///
/// This domain represents sets of Boolean control states using Binary Decision Diagrams.
/// Control variables are Boolean program variables (flags, mode indicators) that determine
/// which control path the program is on.
///
/// # Key Features
///
/// - **Compact Representation**: BDDs can represent exponentially many control states
/// - **Canonical Form**: BDDs are automatically reduced and canonical
/// - **Efficient Operations**: Boolean operations (AND, OR, NOT) are polynomial
/// - **Path Sensitivity**: Different control paths maintain separate invariants
///
/// # Usage
///
/// ```rust
/// use abstract_interpretation::*;
///
/// let domain = BddControlDomain::new();
///
/// // Allocate control variables
/// domain.allocate_var("flag");
/// domain.allocate_var("initialized");
///
/// // Create states
/// let state1 = domain.mk_var_true("flag");
/// let state2 = domain.mk_var_false("flag");
///
/// // Combine with Boolean operations
/// let any_flag = domain.join(&state1, &state2);  // flag ∈ {true, false}
/// ```
#[derive(Clone)]
pub struct BddControlDomain {
    /// Shared BDD manager
    manager: Rc<Bdd>,
    /// Control variable name to BDD variable ID mapping
    var_map: Rc<RefCell<HashMap<String, u32>>>,
    /// Next available BDD variable ID
    next_var: Rc<RefCell<u32>>,
}

impl BddControlDomain {
    /// Create a new BDD control domain with a fresh BDD manager.
    pub fn new() -> Self {
        Self {
            manager: Rc::new(Bdd::default()),
            var_map: Rc::new(RefCell::new(HashMap::new())),
            next_var: Rc::new(RefCell::new(1)), // BDD vars start at 1, not 0
        }
    }

    /// Get the shared BDD manager.
    pub fn manager(&self) -> &Rc<Bdd> {
        &self.manager
    }

    /// Allocate a BDD variable for a control variable.
    ///
    /// If the variable already exists, returns its existing ID.
    /// Otherwise, allocates a new BDD variable ID.
    ///
    /// # Arguments
    ///
    /// * `name` - Name of the control variable (e.g., "flag", "is_active")
    ///
    /// # Returns
    ///
    /// BDD variable ID (u32) for this control variable.
    ///
    /// # Example
    ///
    /// ```rust
    /// # use abstract_interpretation::*;
    /// let domain = BddControlDomain::new();
    /// let var_id = domain.allocate_var("flag");
    /// assert_eq!(var_id, 1); // First variable gets ID 1
    ///
    /// let same_id = domain.allocate_var("flag");
    /// assert_eq!(same_id, 1); // Same variable returns same ID
    ///
    /// let next_id = domain.allocate_var("other");
    /// assert_eq!(next_id, 2); // Next variable gets ID 2
    /// ```
    pub fn allocate_var(&self, name: &str) -> u32 {
        let mut var_map = self.var_map.borrow_mut();

        if let Some(&id) = var_map.get(name) {
            return id;
        }

        let mut next = self.next_var.borrow_mut();
        let id = *next;
        *next += 1;

        var_map.insert(name.to_string(), id);
        id
    }

    /// Get the BDD variable ID for a control variable, if it exists.
    pub fn get_var(&self, name: &str) -> Option<u32> {
        self.var_map.borrow().get(name).copied()
    }

    /// Get the number of allocated control variables.
    pub fn num_vars(&self) -> usize {
        self.var_map.borrow().len()
    }

    /// Create a control state where the variable is true.
    ///
    /// # Example
    ///
    /// ```rust
    /// # use abstract_interpretation::*;
    /// let domain = BddControlDomain::new();
    /// domain.allocate_var("flag");
    ///
    /// let state = domain.mk_var_true("flag");
    /// // Represents: flag = true
    /// ```
    pub fn mk_var_true(&self, var: &str) -> ControlState {
        let var_id = self.allocate_var(var);
        let bdd_ref = self.manager.mk_var(var_id);
        ControlState::new(bdd_ref, Rc::clone(&self.manager))
            .with_description(format!("{} = true", var))
    }

    /// Create a control state where the variable is false.
    ///
    /// # Example
    ///
    /// ```rust
    /// # use abstract_interpretation::*;
    /// let domain = BddControlDomain::new();
    /// domain.allocate_var("flag");
    ///
    /// let state = domain.mk_var_false("flag");
    /// // Represents: flag = false
    /// ```
    pub fn mk_var_false(&self, var: &str) -> ControlState {
        let var_id = self.allocate_var(var);
        let var_bdd = self.manager.mk_var(var_id);
        let bdd_ref = self.manager.apply_not(var_bdd);
        ControlState::new(bdd_ref, Rc::clone(&self.manager))
            .with_description(format!("{} = false", var))
    }

    /// Conjunction: φ₁ ∧ φ₂
    ///
    /// Creates a control state representing the intersection of two control states.
    pub fn and(&self, s1: &ControlState, s2: &ControlState) -> ControlState {
        let bdd_ref = self.manager.apply_and(s1.bdd_ref, s2.bdd_ref);
        ControlState::new(bdd_ref, Rc::clone(&self.manager))
    }

    /// Disjunction: φ₁ ∨ φ₂
    ///
    /// Creates a control state representing the union of two control states.
    pub fn or(&self, s1: &ControlState, s2: &ControlState) -> ControlState {
        let bdd_ref = self.manager.apply_or(s1.bdd_ref, s2.bdd_ref);
        ControlState::new(bdd_ref, Rc::clone(&self.manager))
    }

    /// Negation: ¬φ
    ///
    /// Creates a control state representing the complement.
    pub fn not(&self, s: &ControlState) -> ControlState {
        let bdd_ref = self.manager.apply_not(s.bdd_ref);
        ControlState::new(bdd_ref, Rc::clone(&self.manager))
    }

    /// Implication: φ₁ ⇒ φ₂
    ///
    /// Equivalent to: ¬φ₁ ∨ φ₂
    pub fn implies(&self, s1: &ControlState, s2: &ControlState) -> bool {
        // φ₁ ⇒ φ₂ is equivalent to checking if φ₁ ∧ ¬φ₂ is unsatisfiable
        let not_s2 = self.manager.apply_not(s2.bdd_ref);
        let and_result = self.manager.apply_and(s1.bdd_ref, not_s2);
        and_result == self.manager.zero
    }

    /// Check if two control states are equivalent.
    pub fn equivalent(&self, s1: &ControlState, s2: &ControlState) -> bool {
        // φ₁ ≡ φ₂ iff (φ₁ ⇒ φ₂) ∧ (φ₂ ⇒ φ₁)
        self.implies(s1, s2) && self.implies(s2, s1)
    }
}

impl Default for BddControlDomain {
    fn default() -> Self {
        Self::new()
    }
}

impl fmt::Debug for BddControlDomain {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("BddControlDomain")
            .field("num_vars", &self.num_vars())
            .field("variables", &self.var_map.borrow().keys().collect::<Vec<_>>())
            .finish()
    }
}

// ============================================================================
// AbstractDomain Implementation
// ============================================================================

impl AbstractDomain for BddControlDomain {
    type Element = ControlState;

    /// Create the bottom element (unreachable/false).
    ///
    /// The bottom element represents an unreachable control state, equivalent
    /// to the BDD constant `false` (0).
    ///
    /// # Properties
    ///
    /// - ⊥ ⊑ φ for all φ (bottom is the least element)
    /// - ⊥ ⊓ φ = ⊥ (bottom annihilates meet)
    /// - ⊥ ⊔ φ = φ (bottom is the identity for join)
    ///
    /// # Example
    ///
    /// ```rust
    /// # use abstract_interpretation::*;
    /// let domain = BddControlDomain::new();
    /// let bottom = domain.bottom();
    ///
    /// assert!(domain.is_bottom(&bottom));
    /// assert!(!bottom.is_sat()); // No satisfying assignments
    /// ```
    fn bottom(&self) -> Self::Element {
        ControlState::new(self.manager.zero, Rc::clone(&self.manager))
            .with_description("⊥".to_string())
    }

    /// Create the top element (all paths reachable/true).
    ///
    /// The top element represents all possible control states, equivalent
    /// to the BDD constant `true` (1).
    ///
    /// # Properties
    ///
    /// - φ ⊑ ⊤ for all φ (top is the greatest element)
    /// - ⊤ ⊔ φ = ⊤ (top annihilates join)
    /// - ⊤ ⊓ φ = φ (top is the identity for meet)
    ///
    /// # Example
    ///
    /// ```rust
    /// # use abstract_interpretation::*;
    /// let domain = BddControlDomain::new();
    /// let top = domain.top();
    ///
    /// assert!(domain.is_top(&top));
    /// assert!(top.is_tautology()); // Always true
    /// ```
    fn top(&self) -> Self::Element {
        ControlState::new(self.manager.one, Rc::clone(&self.manager))
            .with_description("⊤".to_string())
    }

    /// Check if an element is bottom (unreachable).
    ///
    /// # Example
    ///
    /// ```rust
    /// # use abstract_interpretation::*;
    /// let domain = BddControlDomain::new();
    /// domain.allocate_var("flag");
    ///
    /// let flag_true = domain.mk_var_true("flag");
    /// let flag_false = domain.mk_var_false("flag");
    ///
    /// // flag=true AND flag=false is impossible
    /// let impossible = domain.meet(&flag_true, &flag_false);
    /// assert!(domain.is_bottom(&impossible));
    /// ```
    fn is_bottom(&self, elem: &Self::Element) -> bool {
        elem.bdd_ref == self.manager.zero
    }

    /// Check if an element is top (all paths reachable).
    ///
    /// # Example
    ///
    /// ```rust
    /// # use abstract_interpretation::*;
    /// let domain = BddControlDomain::new();
    /// domain.allocate_var("flag");
    ///
    /// let flag_true = domain.mk_var_true("flag");
    /// let flag_false = domain.mk_var_false("flag");
    ///
    /// // flag=true OR flag=false covers all possibilities
    /// let all_paths = domain.join(&flag_true, &flag_false);
    /// assert!(domain.is_top(&all_paths));
    /// ```
    fn is_top(&self, elem: &Self::Element) -> bool {
        elem.bdd_ref == self.manager.one
    }

    /// Partial order: φ₁ ⊑ φ₂ iff φ₁ ⇒ φ₂ (logical implication).
    ///
    /// Checks if elem1 is "more precise" or "smaller" than elem2.
    /// In the BDD control domain, this means elem1 implies elem2.
    ///
    /// # Interpretation
    ///
    /// - φ₁ ⊑ φ₂ means: every control path in φ₁ is also in φ₂
    /// - Equivalently: the set of satisfying assignments of φ₁ is a subset of φ₂
    ///
    /// # Properties
    ///
    /// - Reflexive: φ ⊑ φ
    /// - Transitive: φ₁ ⊑ φ₂ ∧ φ₂ ⊑ φ₃ ⇒ φ₁ ⊑ φ₃
    /// - Antisymmetric: φ₁ ⊑ φ₂ ∧ φ₂ ⊑ φ₁ ⇒ φ₁ = φ₂
    ///
    /// # Example
    ///
    /// ```rust
    /// # use abstract_interpretation::*;
    /// let domain = BddControlDomain::new();
    /// domain.allocate_var("flag");
    ///
    /// let flag_true = domain.mk_var_true("flag");
    /// let top = domain.top();
    ///
    /// // flag=true is more precise than ⊤ (all paths)
    /// assert!(domain.le(&flag_true, &top));
    /// assert!(!domain.le(&top, &flag_true));
    /// ```
    fn le(&self, elem1: &Self::Element, elem2: &Self::Element) -> bool {
        // φ₁ ⊑ φ₂ ⟺ φ₁ ⇒ φ₂
        self.implies(elem1, elem2)
    }

    /// Join (least upper bound): φ₁ ⊔ φ₂ = φ₁ ∨ φ₂ (disjunction).
    ///
    /// Computes the least element that is greater than or equal to both inputs.
    /// In the BDD control domain, this is logical OR.
    ///
    /// # Interpretation
    ///
    /// - Result represents control paths reachable by **either** elem1 **or** elem2
    /// - Over-approximates: includes all paths from both inputs
    ///
    /// # Properties
    ///
    /// - Commutative: φ₁ ⊔ φ₂ = φ₂ ⊔ φ₁
    /// - Associative: (φ₁ ⊔ φ₂) ⊔ φ₃ = φ₁ ⊔ (φ₂ ⊔ φ₃)
    /// - Idempotent: φ ⊔ φ = φ
    /// - φ₁ ⊑ (φ₁ ⊔ φ₂) and φ₂ ⊑ (φ₁ ⊔ φ₂)
    ///
    /// # Example
    ///
    /// ```rust
    /// # use abstract_interpretation::*;
    /// let domain = BddControlDomain::new();
    /// domain.allocate_var("flag");
    ///
    /// let flag_true = domain.mk_var_true("flag");
    /// let flag_false = domain.mk_var_false("flag");
    ///
    /// // Either flag=true or flag=false covers all possibilities
    /// let joined = domain.join(&flag_true, &flag_false);
    /// assert!(domain.is_top(&joined)); // No constraint on flag
    /// ```
    fn join(&self, elem1: &Self::Element, elem2: &Self::Element) -> Self::Element {
        self.or(elem1, elem2)
    }

    /// Meet (greatest lower bound): φ₁ ⊓ φ₂ = φ₁ ∧ φ₂ (conjunction).
    ///
    /// Computes the greatest element that is less than or equal to both inputs.
    /// In the BDD control domain, this is logical AND.
    ///
    /// # Interpretation
    ///
    /// - Result represents control paths reachable by **both** elem1 **and** elem2
    /// - Refines: only includes paths common to both inputs
    ///
    /// # Properties
    ///
    /// - Commutative: φ₁ ⊓ φ₂ = φ₂ ⊓ φ₁
    /// - Associative: (φ₁ ⊓ φ₂) ⊓ φ₃ = φ₁ ⊓ (φ₂ ⊓ φ₃)
    /// - Idempotent: φ ⊓ φ = φ
    /// - (φ₁ ⊓ φ₂) ⊑ φ₁ and (φ₁ ⊓ φ₂) ⊑ φ₂
    ///
    /// # Example
    ///
    /// ```rust
    /// # use abstract_interpretation::*;
    /// let domain = BddControlDomain::new();
    /// domain.allocate_var("flag1");
    /// domain.allocate_var("flag2");
    ///
    /// let flag1_true = domain.mk_var_true("flag1");
    /// let flag2_true = domain.mk_var_true("flag2");
    ///
    /// // Both must be true
    /// let met = domain.meet(&flag1_true, &flag2_true);
    /// assert!(!domain.is_bottom(&met)); // Satisfiable
    /// assert!(!domain.is_top(&met));    // Constrained
    /// ```
    fn meet(&self, elem1: &Self::Element, elem2: &Self::Element) -> Self::Element {
        self.and(elem1, elem2)
    }

    /// Widening operator: φ₁ ∇ φ₂ = φ₁ ∨ φ₂ (same as join).
    ///
    /// For BDD control domain, widening is the same as join because the lattice
    /// has **finite height** (2^n where n is the number of control variables).
    /// This ensures termination of fixpoint iteration.
    ///
    /// # Finite Height Property
    ///
    /// The lattice of Boolean formulas over n variables has at most 2^n distinct
    /// equivalence classes, guaranteeing that any ascending chain:
    ///
    /// ```text
    /// φ₀ ⊑ φ₁ ⊑ φ₂ ⊑ ... ⊑ φₖ
    /// ```
    ///
    /// must stabilize after at most 2^n steps.
    ///
    /// # Example
    ///
    /// ```rust
    /// # use abstract_interpretation::*;
    /// let domain = BddControlDomain::new();
    /// domain.allocate_var("flag");
    ///
    /// let flag_true = domain.mk_var_true("flag");
    /// let flag_false = domain.mk_var_false("flag");
    ///
    /// let widened = domain.widen(&flag_true, &flag_false);
    /// assert!(domain.is_top(&widened)); // Same as join for BDD domain
    /// ```
    fn widen(&self, elem1: &Self::Element, elem2: &Self::Element) -> Self::Element {
        // For finite lattices, widening = join
        self.join(elem1, elem2)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_control_state_creation() {
        let domain = BddControlDomain::new();

        let bottom = ControlState::new(domain.manager.zero, Rc::clone(&domain.manager));
        assert!(!bottom.is_sat());
        assert!(!bottom.is_tautology());

        let top = ControlState::new(domain.manager.one, Rc::clone(&domain.manager));
        assert!(top.is_sat());
        assert!(top.is_tautology());
    }

    #[test]
    fn test_var_allocation() {
        let domain = BddControlDomain::new();

        let id1 = domain.allocate_var("flag");
        assert_eq!(id1, 1);

        let id2 = domain.allocate_var("flag");
        assert_eq!(id2, 1); // Same variable

        let id3 = domain.allocate_var("other");
        assert_eq!(id3, 2); // Different variable

        assert_eq!(domain.num_vars(), 2);
    }

    #[test]
    fn test_mk_var_true_false() {
        let domain = BddControlDomain::new();
        domain.allocate_var("flag");

        let state_true = domain.mk_var_true("flag");
        let state_false = domain.mk_var_false("flag");

        assert!(state_true.is_sat());
        assert!(state_false.is_sat());
        assert!(!state_true.is_tautology());
        assert!(!state_false.is_tautology());

        assert_ne!(state_true, state_false);
    }

    #[test]
    fn test_boolean_operations() {
        let domain = BddControlDomain::new();
        domain.allocate_var("flag");

        let state_true = domain.mk_var_true("flag");
        let state_false = domain.mk_var_false("flag");

        // flag=true AND flag=false = ⊥
        let and_result = domain.and(&state_true, &state_false);
        assert!(!and_result.is_sat());

        // flag=true OR flag=false = ⊤
        let or_result = domain.or(&state_true, &state_false);
        assert!(or_result.is_tautology());

        // NOT (flag=true) = flag=false
        let not_result = domain.not(&state_true);
        assert!(domain.equivalent(&not_result, &state_false));
    }

    #[test]
    fn test_implication() {
        let domain = BddControlDomain::new();
        domain.allocate_var("flag");

        let state_true = domain.mk_var_true("flag");
        let top = ControlState::new(domain.manager.one, Rc::clone(&domain.manager));
        let bottom = ControlState::new(domain.manager.zero, Rc::clone(&domain.manager));

        // flag=true ⇒ ⊤
        assert!(domain.implies(&state_true, &top));

        // ⊥ ⇒ flag=true
        assert!(domain.implies(&bottom, &state_true));

        // flag=true ⇏ flag=false
        let state_false = domain.mk_var_false("flag");
        assert!(!domain.implies(&state_true, &state_false));
    }

    #[test]
    fn test_control_state_equality() {
        let domain = BddControlDomain::new();
        domain.allocate_var("flag");

        let s1 = domain.mk_var_true("flag");
        let s2 = domain.mk_var_true("flag");

        assert_eq!(s1, s2); // Same BDD reference

        let s3 = domain.mk_var_false("flag");
        assert_ne!(s1, s3);
    }

    #[test]
    fn test_has_solution() {
        let domain = BddControlDomain::new();
        domain.allocate_var("flag1");
        domain.allocate_var("flag2");

        let s1 = domain.mk_var_true("flag1");
        assert!(s1.has_solution());

        let s2 = domain.mk_var_true("flag2");
        let both = domain.and(&s1, &s2);
        assert!(both.has_solution());

        let top = ControlState::new(domain.manager.one, Rc::clone(&domain.manager));
        assert!(top.has_solution());

        let bottom = ControlState::new(domain.manager.zero, Rc::clone(&domain.manager));
        assert!(!bottom.has_solution());
    }

    // ========================================================================
    // AbstractDomain Trait Tests
    // ========================================================================

    #[test]
    fn test_bottom_top() {
        let domain = BddControlDomain::new();

        let bottom = domain.bottom();
        let top = domain.top();

        assert!(domain.is_bottom(&bottom));
        assert!(!domain.is_bottom(&top));

        assert!(domain.is_top(&top));
        assert!(!domain.is_top(&bottom));
    }

    #[test]
    fn test_bottom_is_least() {
        let domain = BddControlDomain::new();
        domain.allocate_var("flag");

        let bottom = domain.bottom();
        let top = domain.top();
        let flag_true = domain.mk_var_true("flag");

        // ⊥ ⊑ everything
        assert!(domain.le(&bottom, &top));
        assert!(domain.le(&bottom, &flag_true));
        assert!(domain.le(&bottom, &bottom));
    }

    #[test]
    fn test_top_is_greatest() {
        let domain = BddControlDomain::new();
        domain.allocate_var("flag");

        let bottom = domain.bottom();
        let top = domain.top();
        let flag_true = domain.mk_var_true("flag");

        // everything ⊑ ⊤
        assert!(domain.le(&bottom, &top));
        assert!(domain.le(&flag_true, &top));
        assert!(domain.le(&top, &top));
    }

    #[test]
    fn test_le_reflexive() {
        let domain = BddControlDomain::new();
        domain.allocate_var("flag");

        let flag_true = domain.mk_var_true("flag");

        // φ ⊑ φ
        assert!(domain.le(&flag_true, &flag_true));
    }

    #[test]
    fn test_le_transitive() {
        let domain = BddControlDomain::new();
        domain.allocate_var("flag1");
        domain.allocate_var("flag2");

        let flag1_true = domain.mk_var_true("flag1");
        let flag2_true = domain.mk_var_true("flag2");

        // flag1=true ∧ flag2=true ⊑ flag1=true ⊑ ⊤
        let both = domain.meet(&flag1_true, &flag2_true);
        let top = domain.top();

        assert!(domain.le(&both, &flag1_true));
        assert!(domain.le(&flag1_true, &top));
        assert!(domain.le(&both, &top)); // Transitivity
    }

    #[test]
    fn test_le_antisymmetric() {
        let domain = BddControlDomain::new();
        domain.allocate_var("flag");

        let flag_true1 = domain.mk_var_true("flag");
        let flag_true2 = domain.mk_var_true("flag");

        // φ₁ ⊑ φ₂ ∧ φ₂ ⊑ φ₁ ⇒ φ₁ = φ₂
        assert!(domain.le(&flag_true1, &flag_true2));
        assert!(domain.le(&flag_true2, &flag_true1));
        assert_eq!(flag_true1, flag_true2);
    }

    #[test]
    fn test_join_commutative() {
        let domain = BddControlDomain::new();
        domain.allocate_var("flag1");
        domain.allocate_var("flag2");

        let s1 = domain.mk_var_true("flag1");
        let s2 = domain.mk_var_true("flag2");

        let j1 = domain.join(&s1, &s2);
        let j2 = domain.join(&s2, &s1);

        assert!(domain.equivalent(&j1, &j2));
    }

    #[test]
    fn test_join_associative() {
        let domain = BddControlDomain::new();
        domain.allocate_var("flag1");
        domain.allocate_var("flag2");
        domain.allocate_var("flag3");

        let s1 = domain.mk_var_true("flag1");
        let s2 = domain.mk_var_true("flag2");
        let s3 = domain.mk_var_true("flag3");

        let left = domain.join(&domain.join(&s1, &s2), &s3);
        let right = domain.join(&s1, &domain.join(&s2, &s3));

        assert!(domain.equivalent(&left, &right));
    }

    #[test]
    fn test_join_idempotent() {
        let domain = BddControlDomain::new();
        domain.allocate_var("flag");

        let flag_true = domain.mk_var_true("flag");
        let joined = domain.join(&flag_true, &flag_true);

        assert_eq!(flag_true, joined);
    }

    #[test]
    fn test_join_upper_bound() {
        let domain = BddControlDomain::new();
        domain.allocate_var("flag1");
        domain.allocate_var("flag2");

        let s1 = domain.mk_var_true("flag1");
        let s2 = domain.mk_var_true("flag2");
        let joined = domain.join(&s1, &s2);

        // s1 ⊑ (s1 ⊔ s2) and s2 ⊑ (s1 ⊔ s2)
        assert!(domain.le(&s1, &joined));
        assert!(domain.le(&s2, &joined));
    }

    #[test]
    fn test_join_with_bottom() {
        let domain = BddControlDomain::new();
        domain.allocate_var("flag");

        let bottom = domain.bottom();
        let flag_true = domain.mk_var_true("flag");

        // ⊥ ⊔ φ = φ
        let joined = domain.join(&bottom, &flag_true);
        assert_eq!(joined, flag_true);
    }

    #[test]
    fn test_join_with_top() {
        let domain = BddControlDomain::new();
        domain.allocate_var("flag");

        let top = domain.top();
        let flag_true = domain.mk_var_true("flag");

        // ⊤ ⊔ φ = ⊤
        let joined = domain.join(&top, &flag_true);
        assert!(domain.is_top(&joined));
    }

    #[test]
    fn test_meet_commutative() {
        let domain = BddControlDomain::new();
        domain.allocate_var("flag1");
        domain.allocate_var("flag2");

        let s1 = domain.mk_var_true("flag1");
        let s2 = domain.mk_var_true("flag2");

        let m1 = domain.meet(&s1, &s2);
        let m2 = domain.meet(&s2, &s1);

        assert!(domain.equivalent(&m1, &m2));
    }

    #[test]
    fn test_meet_associative() {
        let domain = BddControlDomain::new();
        domain.allocate_var("flag1");
        domain.allocate_var("flag2");
        domain.allocate_var("flag3");

        let s1 = domain.mk_var_true("flag1");
        let s2 = domain.mk_var_true("flag2");
        let s3 = domain.mk_var_true("flag3");

        let left = domain.meet(&domain.meet(&s1, &s2), &s3);
        let right = domain.meet(&s1, &domain.meet(&s2, &s3));

        assert!(domain.equivalent(&left, &right));
    }

    #[test]
    fn test_meet_idempotent() {
        let domain = BddControlDomain::new();
        domain.allocate_var("flag");

        let flag_true = domain.mk_var_true("flag");
        let met = domain.meet(&flag_true, &flag_true);

        assert_eq!(flag_true, met);
    }

    #[test]
    fn test_meet_lower_bound() {
        let domain = BddControlDomain::new();
        domain.allocate_var("flag1");
        domain.allocate_var("flag2");

        let s1 = domain.mk_var_true("flag1");
        let s2 = domain.mk_var_true("flag2");
        let met = domain.meet(&s1, &s2);

        // (s1 ⊓ s2) ⊑ s1 and (s1 ⊓ s2) ⊑ s2
        assert!(domain.le(&met, &s1));
        assert!(domain.le(&met, &s2));
    }

    #[test]
    fn test_meet_with_bottom() {
        let domain = BddControlDomain::new();
        domain.allocate_var("flag");

        let bottom = domain.bottom();
        let flag_true = domain.mk_var_true("flag");

        // ⊥ ⊓ φ = ⊥
        let met = domain.meet(&bottom, &flag_true);
        assert!(domain.is_bottom(&met));
    }

    #[test]
    fn test_meet_with_top() {
        let domain = BddControlDomain::new();
        domain.allocate_var("flag");

        let top = domain.top();
        let flag_true = domain.mk_var_true("flag");

        // ⊤ ⊓ φ = φ
        let met = domain.meet(&top, &flag_true);
        assert_eq!(met, flag_true);
    }

    #[test]
    fn test_meet_contradiction() {
        let domain = BddControlDomain::new();
        domain.allocate_var("flag");

        let flag_true = domain.mk_var_true("flag");
        let flag_false = domain.mk_var_false("flag");

        // flag=true ⊓ flag=false = ⊥
        let met = domain.meet(&flag_true, &flag_false);
        assert!(domain.is_bottom(&met));
    }

    #[test]
    fn test_absorption_laws() {
        let domain = BddControlDomain::new();
        domain.allocate_var("flag1");
        domain.allocate_var("flag2");

        let s1 = domain.mk_var_true("flag1");
        let s2 = domain.mk_var_true("flag2");

        // φ₁ ⊔ (φ₁ ⊓ φ₂) = φ₁
        let meet_result = domain.meet(&s1, &s2);
        let absorption1 = domain.join(&s1, &meet_result);
        assert!(domain.equivalent(&absorption1, &s1));

        // φ₁ ⊓ (φ₁ ⊔ φ₂) = φ₁
        let join_result = domain.join(&s1, &s2);
        let absorption2 = domain.meet(&s1, &join_result);
        assert!(domain.equivalent(&absorption2, &s1));
    }

    #[test]
    fn test_widen_same_as_join() {
        let domain = BddControlDomain::new();
        domain.allocate_var("flag1");
        domain.allocate_var("flag2");

        let s1 = domain.mk_var_true("flag1");
        let s2 = domain.mk_var_true("flag2");

        let joined = domain.join(&s1, &s2);
        let widened = domain.widen(&s1, &s2);

        assert!(domain.equivalent(&joined, &widened));
    }

    #[test]
    fn test_finite_height_convergence() {
        let domain = BddControlDomain::new();
        domain.allocate_var("flag");

        // Simulate ascending chain: ⊥ ⊑ flag=true ⊑ ⊤
        let bottom = domain.bottom();
        let flag_true = domain.mk_var_true("flag");
        let top = domain.top();

        // Chain must stabilize at top
        let step1 = domain.widen(&bottom, &flag_true);
        let step2 = domain.widen(&step1, &top);
        let step3 = domain.widen(&step2, &top);

        assert!(domain.is_top(&step3));
        assert_eq!(step2, step3); // Stabilized
    }
}
