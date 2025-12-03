//! SDD Manager: the central structure for creating and manipulating SDDs.
//!
//! # Architecture
//!
//! ```text
//! ┌─────────────────────────────────────────────────────────────────┐
//! │                        SddManager                               │
//! │                                                                 │
//! │  nodes: Vec<Sdd>           vtree: Vtree      cache: Cache       │
//! │  ┌────────────────┐        ┌──────────┐      ┌────────────┐     │
//! │  │ [0] False      │        │ balanced │      │  apply ops │     │
//! │  │ [1] True       │        │ tree of  │      │  memoized  │     │
//! │  │ [2] +lit1      │        │ vars     │      └────────────┘     │
//! │  │ [3] -lit1      │        └──────────┘                         │
//! │  │ [4] +lit2      │                                             │
//! │  │ [5] -lit2      │        negation_cache: Vec<Option<SddId>>   │
//! │  │ ...            │        (caches negation of each node)       │
//! │  └────────────────┘                                             │
//! │                                                                 │
//! │  unique_table: HashMap      literal_nodes: Vec                  │
//! │  (vtree, elements) → SddId  var → (pos_id, neg_id)              │
//! └─────────────────────────────────────────────────────────────────┘
//! ```

use std::cell::{Cell, RefCell};
use std::collections::{HashMap, HashSet};
use std::fmt;

use num_bigint::BigUint;
use num_traits::{One, Zero};

use crate::literal::Literal;
use crate::sdd::{Element, Sdd, SddId};
use crate::vtree::{Vtree, VtreeId};

/// Cache key for binary operations.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
struct CacheKey {
    op: u8,
    a: SddId,
    b: SddId,
}

impl CacheKey {
    const AND: u8 = 0;
    const OR: u8 = 1;

    fn new(op: u8, a: SddId, b: SddId) -> Self {
        // Normalize order for commutative ops
        let (a, b) = if a <= b { (a, b) } else { (b, a) };
        Self { op, a, b }
    }
}

/// The SDD Manager.
///
/// Central structure for creating and manipulating SDDs.
/// Maintains the vtree, all SDD nodes, and operation caches.
///
/// Unlike BDD managers, SDDs do NOT use complement edges.
/// Negations are stored as separate nodes, cached in `negation_cache`.
pub struct SddManager {
    /// The vtree structure.
    vtree: Vtree,

    /// All SDD nodes. Index 0 = FALSE, Index 1 = TRUE.
    nodes: RefCell<Vec<Sdd>>,

    /// Cached negation for each node: `negation_cache[id] = Some(neg_id)`.
    negation_cache: RefCell<Vec<Option<SddId>>>,

    /// Unique table: maps `(vtree, elements)` to existing SddId.
    unique_table: RefCell<HashMap<UniqueKey, SddId>>,

    /// Literal nodes: maps variable to `(positive_id, negative_id)`.
    /// Index 0 unused, indices `1..=num_vars` used.
    literal_nodes: Vec<(SddId, SddId)>,

    /// Operation cache for apply.
    apply_cache: RefCell<HashMap<CacheKey, SddId>>,

    /// Cache for model counting.
    count_cache: RefCell<HashMap<SddId, BigUint>>,

    /// Statistics: number of apply calls.
    apply_calls: Cell<usize>,

    /// Statistics: number of cache hits.
    cache_hits: Cell<usize>,
}

/// Key for the unique table.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct UniqueKey {
    vtree: VtreeId,
    elements: Vec<(SddId, SddId)>, // (prime, sub)
}

impl UniqueKey {
    fn new(vtree: VtreeId, elements: &[Element]) -> Self {
        let mut elems: Vec<_> = elements.iter().map(|e| (e.prime, e.sub)).collect();
        elems.sort(); // Canonical ordering
        Self { vtree, elements: elems }
    }
}

impl SddManager {
    /// Creates a new SDD manager with the given number of variables.
    ///
    /// Uses a balanced vtree by default.
    ///
    /// # Arguments
    ///
    /// * `num_vars` - Number of Boolean variables (1-indexed)
    ///
    /// # Example
    ///
    /// ```
    /// use sdd::SddManager;
    ///
    /// let mgr = SddManager::new(4);
    /// assert_eq!(mgr.num_vars(), 4);
    /// ```
    pub fn new(num_vars: u32) -> Self {
        Self::with_vtree(Vtree::balanced(num_vars))
    }

    /// Creates a new SDD manager with a right-linear vtree.
    pub fn with_right_linear_vtree(num_vars: u32) -> Self {
        Self::with_vtree(Vtree::right_linear(num_vars))
    }

    /// Creates a new SDD manager with a left-linear vtree.
    pub fn with_left_linear_vtree(num_vars: u32) -> Self {
        Self::with_vtree(Vtree::left_linear(num_vars))
    }

    /// Creates a new SDD manager with the given vtree.
    pub fn with_vtree(vtree: Vtree) -> Self {
        let num_vars = vtree.num_vars();

        // Initialize with FALSE (0) and TRUE (1) terminals
        let nodes = vec![Sdd::False, Sdd::True];
        // Negation cache: FALSE <-> TRUE
        let negation_cache = vec![Some(SddId::TRUE), Some(SddId::FALSE)];

        let mut mgr = Self {
            vtree,
            nodes: RefCell::new(nodes),
            negation_cache: RefCell::new(negation_cache),
            unique_table: RefCell::new(HashMap::new()),
            literal_nodes: vec![(SddId::FALSE, SddId::FALSE); (num_vars + 1) as usize],
            apply_cache: RefCell::new(HashMap::new()),
            count_cache: RefCell::new(HashMap::new()),
            apply_calls: Cell::new(0),
            cache_hits: Cell::new(0),
        };

        // Create literal nodes for each variable (positive and negative)
        for v in 1..=num_vars {
            let pos_lit = Literal::positive(v);
            let neg_lit = Literal::negative(v);

            let pos_id = mgr.add_node(Sdd::Literal(pos_lit));
            let neg_id = mgr.add_node(Sdd::Literal(neg_lit));

            // Cache: positive and negative literals are each other's negation
            mgr.set_negation(pos_id, neg_id);
            mgr.set_negation(neg_id, pos_id);

            mgr.literal_nodes[v as usize] = (pos_id, neg_id);
        }

        mgr
    }

    /// Returns the number of variables.
    #[inline]
    pub fn num_vars(&self) -> u32 {
        self.vtree.num_vars()
    }

    /// Returns a reference to the vtree.
    #[inline]
    pub fn vtree(&self) -> &Vtree {
        &self.vtree
    }

    /// Returns the number of SDD nodes (including terminals).
    #[inline]
    pub fn num_nodes(&self) -> usize {
        self.nodes.borrow().len()
    }

    /// Returns a node by its ID.
    pub fn node(&self, id: SddId) -> Sdd {
        self.nodes.borrow()[id.index()].clone()
    }

    /// Returns the FALSE constant.
    #[inline]
    pub fn false_sdd(&self) -> SddId {
        SddId::FALSE
    }

    /// Returns the TRUE constant.
    #[inline]
    pub fn true_sdd(&self) -> SddId {
        SddId::TRUE
    }

    /// Creates an SDD for a positive variable.
    ///
    /// # Arguments
    ///
    /// * `var` - Variable number (1-indexed)
    ///
    /// # Panics
    ///
    /// Panics if `var` is 0 or greater than `num_vars`.
    #[inline]
    pub fn var(&self, var: u32) -> SddId {
        assert!(var > 0 && var <= self.num_vars(), "Invalid variable: {}", var);
        self.literal_nodes[var as usize].0
    }

    /// Creates an SDD for a negative variable (¬var).
    ///
    /// # Arguments
    ///
    /// * `var` - Variable number (1-indexed)
    #[inline]
    pub fn neg_var(&self, var: u32) -> SddId {
        assert!(var > 0 && var <= self.num_vars(), "Invalid variable: {}", var);
        self.literal_nodes[var as usize].1
    }

    /// Creates an SDD for a literal.
    ///
    /// # Arguments
    ///
    /// * `lit` - A signed integer: positive for the variable, negative for its negation
    #[inline]
    pub fn literal(&self, lit: i32) -> SddId {
        assert!(lit != 0, "Literal cannot be zero");
        if lit < 0 {
            self.neg_var((-lit) as u32)
        } else {
            self.var(lit as u32)
        }
    }

    /// Returns the negation of an SDD.
    ///
    /// Unlike BDDs, this is NOT O(1). We compute the negation recursively
    /// and cache it for future use.
    pub fn negate(&self, f: SddId) -> SddId {
        // Check cache first
        if let Some(Some(neg)) = self.negation_cache.borrow().get(f.index()) {
            return *neg;
        }

        // Compute negation
        let neg = self.compute_negation(f);

        // Cache both directions
        self.set_negation(f, neg);
        self.set_negation(neg, f);

        neg
    }

    /// Alias for [`negate`](Self::negate) - returns ¬f.
    #[inline]
    pub fn neg(&self, f: SddId) -> SddId {
        self.negate(f)
    }

    /// Computes the negation of an SDD node.
    fn compute_negation(&self, f: SddId) -> SddId {
        if f.is_false() {
            return SddId::TRUE;
        }
        if f.is_true() {
            return SddId::FALSE;
        }

        let node = self.node(f);
        match &node {
            Sdd::False => SddId::TRUE,
            Sdd::True => SddId::FALSE,
            Sdd::Literal(lit) => {
                // Return the other literal for this variable
                let var = lit.var();
                if lit.is_positive() {
                    self.literal_nodes[var as usize].1
                } else {
                    self.literal_nodes[var as usize].0
                }
            }
            Sdd::Decision { vtree, elements } => {
                // Negate all subs: ¬(p₁∧s₁ ∨ ... ∨ pₖ∧sₖ) = p₁∧¬s₁ ∨ ... ∨ pₖ∧¬sₖ
                // (since primes partition TRUE)
                let new_elements: Vec<Element> = elements.iter().map(|e| Element::new(e.prime, self.negate(e.sub))).collect();
                self.make_decision(*vtree, new_elements)
            }
        }
    }

    /// Sets the negation cache entry.
    fn set_negation(&self, f: SddId, neg: SddId) {
        let mut cache = self.negation_cache.borrow_mut();
        let idx = f.index();
        if idx >= cache.len() {
            cache.resize(idx + 1, None);
        }
        cache[idx] = Some(neg);
    }

    /// Returns the conjunction of two SDDs (f ∧ g).
    pub fn and(&self, f: SddId, g: SddId) -> SddId {
        self.apply(f, g, true)
    }

    /// Returns the disjunction of two SDDs (f ∨ g).
    pub fn or(&self, f: SddId, g: SddId) -> SddId {
        self.apply(f, g, false)
    }

    /// Returns the exclusive OR of two SDDs (f ⊕ g).
    ///
    /// Computed as: (f ∧ ¬g) ∨ (¬f ∧ g)
    pub fn xor(&self, f: SddId, g: SddId) -> SddId {
        let neg_f = self.negate(f);
        let neg_g = self.negate(g);
        let f_and_not_g = self.and(f, neg_g);
        let not_f_and_g = self.and(neg_f, g);
        self.or(f_and_not_g, not_f_and_g)
    }

    /// Returns the implication (f → g).
    ///
    /// Computed as: ¬f ∨ g
    #[inline]
    pub fn implies(&self, f: SddId, g: SddId) -> SddId {
        let neg_f = self.negate(f);
        self.or(neg_f, g)
    }

    /// Returns the equivalence (f ↔ g).
    ///
    /// Computed as: (f → g) ∧ (g → f)
    pub fn equiv(&self, f: SddId, g: SddId) -> SddId {
        let f_impl_g = self.implies(f, g);
        let g_impl_f = self.implies(g, f);
        self.and(f_impl_g, g_impl_f)
    }

    /// Returns the if-then-else: (cond ∧ then) ∨ (¬cond ∧ else).
    pub fn ite(&self, cond: SddId, then_sdd: SddId, else_sdd: SddId) -> SddId {
        // Terminal cases
        if cond.is_true() {
            return then_sdd;
        }
        if cond.is_false() {
            return else_sdd;
        }
        if then_sdd == else_sdd {
            return then_sdd;
        }

        let neg_cond = self.negate(cond);
        let then_branch = self.and(cond, then_sdd);
        let else_branch = self.and(neg_cond, else_sdd);
        self.or(then_branch, else_branch)
    }

    /// Checks if an SDD is the FALSE constant.
    #[inline]
    pub fn is_false(&self, f: SddId) -> bool {
        f.is_false()
    }

    /// Checks if an SDD is the TRUE constant.
    #[inline]
    pub fn is_true(&self, f: SddId) -> bool {
        f.is_true()
    }

    /// Checks if an SDD is a constant (TRUE or FALSE).
    #[inline]
    pub fn is_constant(&self, f: SddId) -> bool {
        f.is_constant()
    }

    /// Checks if an SDD is satisfiable (not FALSE).
    #[inline]
    pub fn is_satisfiable(&self, f: SddId) -> bool {
        !self.is_false(f)
    }

    /// Checks if an SDD is valid/tautology (TRUE).
    #[inline]
    pub fn is_valid(&self, f: SddId) -> bool {
        self.is_true(f)
    }

    /// Adds a new node to the manager.
    fn add_node(&self, node: Sdd) -> SddId {
        let mut nodes = self.nodes.borrow_mut();
        let id = SddId::new(nodes.len() as u32);
        nodes.push(node);
        // Extend negation cache
        self.negation_cache.borrow_mut().push(None);
        id
    }

    /// Core apply operation (conjunction or disjunction).
    ///
    /// Implements the SDD apply algorithm with proper vtree-based case handling.
    fn apply(&self, f: SddId, g: SddId, is_and: bool) -> SddId {
        self.apply_calls.set(self.apply_calls.get() + 1);

        // Terminal cases
        if f == g {
            return f;
        }

        // Check if f and g are negations
        if let Some(Some(neg_f)) = self.negation_cache.borrow().get(f.index()) {
            if *neg_f == g {
                return if is_and { SddId::FALSE } else { SddId::TRUE };
            }
        }

        // Zero/One rules
        let (zero, one) = if is_and {
            (SddId::FALSE, SddId::TRUE)
        } else {
            (SddId::TRUE, SddId::FALSE)
        };

        if f == zero || g == zero {
            return zero;
        }
        if f == one {
            return g;
        }
        if g == one {
            return f;
        }

        // Check cache (normalized key)
        let cache_key = CacheKey::new(if is_and { CacheKey::AND } else { CacheKey::OR }, f, g);
        if let Some(&result) = self.apply_cache.borrow().get(&cache_key) {
            self.cache_hits.set(self.cache_hits.get() + 1);
            return result;
        }

        // Get vtrees for f and g
        let f_vtree = self.node_vtree(f);
        let g_vtree = self.node_vtree(g);

        // Order by position: ensure f_pos <= g_pos
        let (node1, node2, vtree1, vtree2) = if self.vtree.position(f_vtree) <= self.vtree.position(g_vtree) {
            (f, g, f_vtree, g_vtree)
        } else {
            (g, f, g_vtree, f_vtree)
        };

        // Determine apply case and compute result
        let result = self.apply_case(node1, node2, vtree1, vtree2, is_and);

        // Cache and return
        self.apply_cache.borrow_mut().insert(cache_key, result);
        result
    }

    /// Determines the apply case and dispatches to the appropriate handler.
    fn apply_case(&self, node1: SddId, node2: SddId, vtree1: VtreeId, vtree2: VtreeId, is_and: bool) -> SddId {
        // vtree1.position <= vtree2.position by construction

        if vtree1 == vtree2 {
            // Case Equal: Both normalized for the same vtree
            self.apply_equal(node1, node2, vtree1, is_and)
        } else {
            // Find LCA of vtree1 and vtree2
            let lca = self.vtree.lca(vtree1, vtree2);

            if lca == vtree2 {
                // vtree1 is in the left subtree of vtree2 (since pos1 < pos2)
                // Case Left: node1 in left subtree of node2's vtree
                self.apply_left(node1, node2, vtree2, is_and)
            } else if lca == vtree1 {
                // vtree2 is in the right subtree of vtree1
                // Case Right: node2 in right subtree of node1's vtree
                self.apply_right(node1, node2, vtree1, is_and)
            } else {
                // Case Incomparable: Neither is a subtree of the other
                self.apply_incomparable(node1, node2, lca, is_and)
            }
        }
    }

    /// Apply when both nodes are normalized for the same vtree.
    ///
    /// Multiplies the decompositions: for each (p1,s1) and (p2,s2),
    /// compute (p1 AND p2, s1 OP s2) when p1 AND p2 is not false.
    fn apply_equal(&self, node1: SddId, node2: SddId, vtree: VtreeId, is_and: bool) -> SddId {
        let elems1 = self.get_elements(node1, vtree);
        let elems2 = self.get_elements(node2, vtree);

        let mut result_elements = Vec::new();

        for e1 in &elems1 {
            for e2 in &elems2 {
                // Compute prime conjunction
                let new_prime = self.and(e1.prime, e2.prime);
                if self.is_false(new_prime) {
                    continue;
                }

                // Compute sub operation
                let new_sub = if is_and {
                    self.and(e1.sub, e2.sub)
                } else {
                    self.or(e1.sub, e2.sub)
                };

                result_elements.push(Element::new(new_prime, new_sub));
            }
        }

        self.build_node_from_elements(vtree, result_elements)
    }

    /// Apply when node1's vtree is in the left subtree of node2's vtree.
    ///
    /// node2 is normalized for vtree, node1 is in vtree's left subtree.
    fn apply_left(&self, node1: SddId, node2: SddId, vtree: VtreeId, is_and: bool) -> SddId {
        let elems2 = self.get_elements(node2, vtree);
        let node1_neg = self.negate(node1);

        // For AND: n = node1, for OR: n = ¬node1
        let n = if is_and { node1 } else { node1_neg };
        let n_neg = if is_and { node1_neg } else { node1 };

        let mut result_elements = Vec::new();

        // Add element for the negation part: (¬n, ZERO)
        // This is needed for the partition property
        let zero_sub = if is_and { SddId::FALSE } else { SddId::TRUE };
        result_elements.push(Element::new(n_neg, zero_sub));

        // For each (prime, sub) in node2, compute (prime AND n, sub)
        for e2 in &elems2 {
            let new_prime = self.and(e2.prime, n);
            if !self.is_false(new_prime) {
                result_elements.push(Element::new(new_prime, e2.sub));
            }
        }

        self.build_node_from_elements(vtree, result_elements)
    }

    /// Apply when node2's vtree is in the right subtree of node1's vtree.
    ///
    /// node1 is normalized for vtree, node2 is in vtree's right subtree.
    fn apply_right(&self, node1: SddId, node2: SddId, vtree: VtreeId, is_and: bool) -> SddId {
        let elems1 = self.get_elements(node1, vtree);

        let mut result_elements = Vec::new();

        // For each (prime, sub) in node1, compute (prime, sub OP node2)
        for e1 in &elems1 {
            let new_sub = if is_and { self.and(e1.sub, node2) } else { self.or(e1.sub, node2) };

            result_elements.push(Element::new(e1.prime, new_sub));
        }

        self.build_node_from_elements(vtree, result_elements)
    }

    /// Apply when the two vtrees are incomparable (neither is ancestor of the other).
    ///
    /// Creates a simple 2-element decomposition at the LCA.
    fn apply_incomparable(&self, node1: SddId, node2: SddId, lca: VtreeId, is_and: bool) -> SddId {
        let node1_neg = self.negate(node1);

        // For AND: (node1, node2), (¬node1, FALSE)
        // For OR:  (node1, TRUE), (¬node1, node2)
        let (sub1, sub2) = if is_and { (node2, SddId::FALSE) } else { (SddId::TRUE, node2) };

        let elements = vec![Element::new(node1, sub1), Element::new(node1_neg, sub2)];

        self.build_node_from_elements(lca, elements)
    }

    /// Gets the elements of an SDD as a partition at the given vtree.
    fn get_elements(&self, f: SddId, vtree: VtreeId) -> Vec<Element> {
        let node = self.node(f);

        match &node {
            Sdd::Decision {
                vtree: dec_vtree,
                elements,
            } if *dec_vtree == vtree => elements.clone(),
            Sdd::Literal(lit) => {
                let lit_vtree = self.vtree.var_vtree(lit.var());
                if self.vtree.is_in_left_subtree(lit_vtree, vtree) {
                    // Literal is in left subtree: partition is (lit, T), (¬lit, F)
                    vec![Element::new(f, SddId::TRUE), Element::new(self.negate(f), SddId::FALSE)]
                } else {
                    // Literal is in right subtree: partition is (T, lit)
                    vec![Element::new(SddId::TRUE, f)]
                }
            }
            Sdd::True => {
                vec![Element::new(SddId::TRUE, SddId::TRUE)]
            }
            Sdd::False => {
                vec![] // Empty partition for FALSE
            }
            _ => {
                // Decision node at a different vtree - shouldn't happen if called correctly
                // Fall back to treating it as being in one subtree
                let dec_vtree = self.node_vtree(f);
                if self.vtree.is_in_left_subtree(dec_vtree, vtree) {
                    vec![Element::new(f, SddId::TRUE), Element::new(self.negate(f), SddId::FALSE)]
                } else {
                    vec![Element::new(SddId::TRUE, f)]
                }
            }
        }
    }

    /// Builds a node from elements, applying compression and trimming.
    ///
    /// Following libsdd's partitions.c:
    /// - Trimming Rule 1: If all subs are the same, return that sub
    /// - Trimming Rule 2: If {(p, TRUE), (¬p, FALSE)}, return p
    /// - Compression: Merge elements with the same sub by disjoining their primes
    fn build_node_from_elements(&self, vtree: VtreeId, elements: Vec<Element>) -> SddId {
        if elements.is_empty() {
            return SddId::FALSE;
        }

        // Compress: merge elements with the same sub
        let compressed = self.compress_elements(elements);

        if compressed.is_empty() {
            return SddId::FALSE;
        }

        // Trimming Rule 1: All subs are the same → return that sub
        // This is the (TRUE, sub) case when there's only one element
        if compressed.len() == 1 {
            let e = &compressed[0];
            // If prime is TRUE, the result is just sub
            if self.is_true(e.prime) {
                return e.sub;
            }
            // Note: A single element with non-TRUE prime means
            // we have something like (p, s) where p≠TRUE, which is invalid
            // as primes must partition TRUE. This shouldn't happen with
            // correct apply, but handle it defensively.
        }

        // Trimming Rule 2: Exactly two elements (p, TRUE), (¬p, FALSE) → return p
        if compressed.len() == 2 {
            let e0 = &compressed[0];
            let e1 = &compressed[1];

            // Check if subs are TRUE and FALSE
            let (true_elem, false_elem) = if self.is_true(e0.sub) && self.is_false(e1.sub) {
                (e0, e1)
            } else if self.is_true(e1.sub) && self.is_false(e0.sub) {
                (e1, e0)
            } else {
                // Not the trimming case, proceed to create decision node
                return self.make_decision(vtree, compressed);
            };

            // Check if primes are negations of each other
            if let Some(Some(neg)) = self.negation_cache.borrow().get(true_elem.prime.index()) {
                if *neg == false_elem.prime {
                    return true_elem.prime;
                }
            }
        }

        self.make_decision(vtree, compressed)
    }

    /// Returns the vtree node for any SDD node (not just decision nodes).
    pub fn node_vtree(&self, f: SddId) -> VtreeId {
        if f.is_constant() {
            // Constants are "everywhere" - use root
            return self.vtree.root();
        }

        let node = self.node(f);
        match &node {
            Sdd::Literal(lit) => self.vtree.var_vtree(lit.var()),
            Sdd::Decision { vtree, .. } => *vtree,
            Sdd::True | Sdd::False => self.vtree.root(),
        }
    }

    /// Compresses elements by merging those with the same sub.
    fn compress_elements(&self, elements: Vec<Element>) -> Vec<Element> {
        if elements.is_empty() {
            return elements;
        }

        // Group by sub
        let mut by_sub: HashMap<SddId, Vec<SddId>> = HashMap::new();
        for elem in &elements {
            by_sub.entry(elem.sub).or_default().push(elem.prime);
        }

        // Merge primes with same sub
        let mut result = Vec::new();
        for (sub, primes) in by_sub {
            // Disjoin all primes
            let mut combined_prime = primes[0];
            for &p in &primes[1..] {
                combined_prime = self.or(combined_prime, p);
            }

            if !self.is_false(combined_prime) {
                result.push(Element::new(combined_prime, sub));
            }
        }

        // Sort by prime for canonical form
        result.sort_by_key(|e| e.prime);
        result
    }

    /// Creates a decision node or looks it up in the unique table.
    fn make_decision(&self, vtree: VtreeId, elements: Vec<Element>) -> SddId {
        if elements.is_empty() {
            return SddId::FALSE;
        }
        if elements.len() == 1 {
            let e = &elements[0];
            if self.is_true(e.prime) {
                return e.sub;
            }
            if self.is_true(e.sub) {
                return e.prime;
            }
        }

        // Check unique table
        let key = UniqueKey::new(vtree, &elements);
        if let Some(&id) = self.unique_table.borrow().get(&key) {
            return id;
        }

        // Create new node
        let node = Sdd::Decision {
            vtree,
            elements: elements.clone(),
        };
        let id = self.add_node(node);

        // Add to unique table
        self.unique_table.borrow_mut().insert(key, id);

        id
    }

    /// Conditions an SDD on a literal.
    ///
    /// Returns the SDD with the variable set to the given value.
    ///
    /// # Arguments
    ///
    /// * `f` - The SDD to condition
    /// * `lit` - A signed literal (positive for true, negative for false)
    pub fn condition(&self, f: SddId, lit: i32) -> SddId {
        assert!(lit != 0, "Literal cannot be zero");

        let var = lit.unsigned_abs();
        let value = lit > 0;

        self.condition_var(f, var, value)
    }

    /// Conditions an SDD on a variable assignment.
    fn condition_var(&self, f: SddId, var: u32, value: bool) -> SddId {
        if f.is_constant() {
            return f;
        }

        let node = self.node(f);

        match &node {
            Sdd::False => SddId::FALSE,
            Sdd::True => SddId::TRUE,

            Sdd::Literal(lit) => {
                if lit.var() == var {
                    // Conditioning this literal
                    if lit.is_positive() == value {
                        SddId::TRUE
                    } else {
                        SddId::FALSE
                    }
                } else {
                    // Different variable, unchanged
                    f
                }
            }

            Sdd::Decision { elements, .. } => {
                // Condition each element
                let mut new_elements = Vec::new();
                for elem in elements {
                    let new_prime = self.condition_var(elem.prime, var, value);
                    let new_sub = self.condition_var(elem.sub, var, value);

                    if !self.is_false(new_prime) && !self.is_false(new_sub) {
                        new_elements.push(Element::new(new_prime, new_sub));
                    }
                }

                // Compress and rebuild
                let compressed = self.compress_elements(new_elements);
                if compressed.is_empty() {
                    SddId::FALSE
                } else if compressed.len() == 1 && self.is_true(compressed[0].prime) {
                    compressed[0].sub
                } else {
                    // Combine all elements
                    let mut result = SddId::FALSE;
                    for elem in &compressed {
                        let term = self.and(elem.prime, elem.sub);
                        result = self.or(result, term);
                    }
                    result
                }
            }
        }
    }

    /// Existentially quantifies a variable from an SDD.
    ///
    /// ∃var. f = f[var/⊤] ∨ f[var/⊥]
    pub fn exists(&self, f: SddId, var: u32) -> SddId {
        let f_true = self.condition_var(f, var, true);
        let f_false = self.condition_var(f, var, false);
        self.or(f_true, f_false)
    }

    /// Universally quantifies a variable from an SDD.
    ///
    /// ∀var. f = f[var/⊤] ∧ f[var/⊥]
    pub fn forall(&self, f: SddId, var: u32) -> SddId {
        let f_true = self.condition_var(f, var, true);
        let f_false = self.condition_var(f, var, false);
        self.and(f_true, f_false)
    }

    /// Counts the number of satisfying assignments.
    ///
    /// Returns the number of truth assignments that satisfy the SDD,
    /// counting over all variables in the manager.
    ///
    /// # Algorithm
    ///
    /// Following libsdd's approach:
    /// 1. Compute local model count for each node relative to its vtree
    /// 2. Multiply by 2^(gap variables) when combining
    /// 3. For TRUE subs, multiply by 2^(all right-side variables)
    pub fn model_count(&self, f: SddId) -> BigUint {
        if f.is_false() {
            return BigUint::zero();
        }
        if f.is_true() {
            // All 2^n assignments satisfy TRUE
            return BigUint::one() << self.num_vars();
        }

        // Compute local model count (relative to node's vtree)
        self.count_cache.borrow_mut().clear();
        let local_count = self.model_count_local(f);

        // Multiply by 2^(variables not covered by node's vtree)
        let node_vtree = self.node_vtree(f);
        let covered_vars = self.vtree.variables_under(node_vtree).len() as u32;
        let gap_vars = self.num_vars() - covered_vars;

        local_count << gap_vars
    }

    /// Computes local model count relative to the node's vtree.
    ///
    /// This follows libsdd's model_count_aux approach:
    /// - LITERAL: 1 (exactly one model relative to its single variable)
    /// - DECOMPOSITION: sum over elements of (prime_count * sub_count * 2^gaps)
    pub fn model_count_local(&self, f: SddId) -> BigUint {
        if f.is_false() {
            return BigUint::zero();
        }
        if f.is_true() {
            // TRUE as a sub is handled specially at call site
            return BigUint::one();
        }

        // Check cache
        if let Some(count) = self.count_cache.borrow().get(&f) {
            return count.clone();
        }

        let node = self.node(f);

        let count = match &node {
            Sdd::False => BigUint::zero(),
            Sdd::True => BigUint::one(),

            Sdd::Literal(_) => {
                // A literal has exactly 1 model relative to its vtree (leaf)
                BigUint::one()
            }

            Sdd::Decision { vtree, elements, .. } => {
                let left = self.vtree.left(*vtree);
                let right = self.vtree.right(*vtree);
                let left_var_count = self.vtree.variables_under(left).len() as u32;
                let right_var_count = self.vtree.variables_under(right).len() as u32;

                let mut total = BigUint::zero();
                for elem in elements {
                    // Skip false subs (no models)
                    if elem.sub.is_false() {
                        continue;
                    }

                    // Prime contribution: local count * 2^(gap to left vtree)
                    let prime_local = self.model_count_local(elem.prime);
                    let prime_vtree = self.node_vtree(elem.prime);
                    let prime_covered = self.vtree.variables_under(prime_vtree).len() as u32;
                    let prime_gap = left_var_count - prime_covered;
                    let prime_count = prime_local << prime_gap;

                    // Sub contribution: special handling for TRUE
                    let sub_count = if elem.sub.is_true() {
                        // TRUE sub: all 2^(right_var_count) assignments work
                        BigUint::one() << right_var_count
                    } else {
                        // Regular sub: local count * 2^(gap to right vtree)
                        let sub_local = self.model_count_local(elem.sub);
                        let sub_vtree = self.node_vtree(elem.sub);
                        let sub_covered = self.vtree.variables_under(sub_vtree).len() as u32;
                        let sub_gap = right_var_count - sub_covered;
                        sub_local << sub_gap
                    };

                    total += prime_count * sub_count;
                }
                total
            }
        };

        self.count_cache.borrow_mut().insert(f, count.clone());
        count
    }

    /// Computes the weighted model count of an SDD.
    ///
    /// Each variable can have positive and negative weights.
    /// The weighted model count sums over all satisfying assignments,
    /// where each assignment contributes the product of its literal weights.
    ///
    /// # Arguments
    ///
    /// * `f` - The SDD to compute WMC for
    /// * `pos_weights` - Weight for positive literals (indexed by variable, 1-indexed)
    /// * `neg_weights` - Weight for negative literals (indexed by variable, 1-indexed)
    ///
    /// # Example
    ///
    /// ```
    /// use sdd::SddManager;
    ///
    /// let mgr = SddManager::new(2);
    /// let x = mgr.var(1);
    ///
    /// // Uniform weights: WMC equals model count
    /// let pos = vec![0.0, 1.0, 1.0]; // index 0 unused
    /// let neg = vec![0.0, 1.0, 1.0];
    /// assert_eq!(mgr.wmc(x, &pos, &neg), 2.0); // 2 models: (T,T), (T,F)
    ///
    /// // With weights 0.3/0.7 for x1, 0.5/0.5 for x2:
    /// let pos = vec![0.0, 0.3, 0.5];
    /// let neg = vec![0.0, 0.7, 0.5];
    /// // WMC(x1) = 0.3 * (0.5 + 0.5) = 0.3
    /// assert!((mgr.wmc(x, &pos, &neg) - 0.3).abs() < 1e-10);
    /// ```
    pub fn wmc(&self, f: SddId, pos_weights: &[f64], neg_weights: &[f64]) -> f64 {
        assert!(
            pos_weights.len() > self.num_vars() as usize,
            "pos_weights must have length > num_vars"
        );
        assert!(
            neg_weights.len() > self.num_vars() as usize,
            "neg_weights must have length > num_vars"
        );

        if f.is_false() {
            return 0.0;
        }
        if f.is_true() {
            // Product of (pos_weight + neg_weight) for all variables
            let mut result = 1.0;
            for var in 1..=self.num_vars() {
                result *= pos_weights[var as usize] + neg_weights[var as usize];
            }
            return result;
        }

        // Compute local WMC and multiply by gap weights
        let mut cache: HashMap<SddId, f64> = HashMap::new();
        let local_wmc = self.wmc_local(f, pos_weights, neg_weights, &mut cache);

        // Multiply by weights for variables not covered by node's vtree
        let node_vtree = self.node_vtree(f);
        let covered_vars: HashSet<u32> = self.vtree.variables_under(node_vtree).into_iter().collect();

        let mut gap_weight = 1.0;
        for var in 1..=self.num_vars() {
            if !covered_vars.contains(&var) {
                gap_weight *= pos_weights[var as usize] + neg_weights[var as usize];
            }
        }

        local_wmc * gap_weight
    }

    /// Computes local WMC relative to the node's vtree.
    fn wmc_local(&self, f: SddId, pos_weights: &[f64], neg_weights: &[f64], cache: &mut HashMap<SddId, f64>) -> f64 {
        if f.is_false() {
            return 0.0;
        }
        if f.is_true() {
            return 1.0;
        }

        if let Some(&wmc) = cache.get(&f) {
            return wmc;
        }

        let node = self.node(f);

        let wmc = match &node {
            Sdd::False => 0.0,
            Sdd::True => 1.0,

            Sdd::Literal(lit) => {
                let var = lit.var() as usize;
                if lit.is_positive() {
                    pos_weights[var]
                } else {
                    neg_weights[var]
                }
            }

            Sdd::Decision { vtree, elements, .. } => {
                let left = self.vtree.left(*vtree);
                let right = self.vtree.right(*vtree);
                let left_vars: HashSet<u32> = self.vtree.variables_under(left).into_iter().collect();
                let right_vars: HashSet<u32> = self.vtree.variables_under(right).into_iter().collect();

                let mut total = 0.0;
                for elem in elements {
                    if elem.sub.is_false() {
                        continue;
                    }

                    // Prime contribution with gap
                    let prime_local = self.wmc_local(elem.prime, pos_weights, neg_weights, cache);
                    let prime_vtree = self.node_vtree(elem.prime);
                    let prime_covered: HashSet<u32> = self.vtree.variables_under(prime_vtree).into_iter().collect();
                    let mut prime_gap = 1.0;
                    for &var in &left_vars {
                        if !prime_covered.contains(&var) {
                            prime_gap *= pos_weights[var as usize] + neg_weights[var as usize];
                        }
                    }
                    let prime_wmc = prime_local * prime_gap;

                    // Sub contribution with gap
                    let sub_wmc = if elem.sub.is_true() {
                        // All right-side variables can be anything
                        let mut w = 1.0;
                        for &var in &right_vars {
                            w *= pos_weights[var as usize] + neg_weights[var as usize];
                        }
                        w
                    } else {
                        let sub_local = self.wmc_local(elem.sub, pos_weights, neg_weights, cache);
                        let sub_vtree = self.node_vtree(elem.sub);
                        let sub_covered: HashSet<u32> = self.vtree.variables_under(sub_vtree).into_iter().collect();
                        let mut sub_gap = 1.0;
                        for &var in &right_vars {
                            if !sub_covered.contains(&var) {
                                sub_gap *= pos_weights[var as usize] + neg_weights[var as usize];
                            }
                        }
                        sub_local * sub_gap
                    };

                    total += prime_wmc * sub_wmc;
                }
                total
            }
        };

        cache.insert(f, wmc);
        wmc
    }

    /// Returns one satisfying assignment, if any.
    ///
    /// Returns a vector of literals representing a satisfying assignment,
    /// or None if the SDD is unsatisfiable.
    pub fn any_sat(&self, f: SddId) -> Option<Vec<i32>> {
        if f.is_false() {
            return None;
        }
        if f.is_true() {
            // Return any assignment (all false)
            return Some((1..=self.num_vars()).map(|v| -(v as i32)).collect());
        }

        let mut assignment = vec![0i32; (self.num_vars() + 1) as usize];
        if self.any_sat_rec(f, &mut assignment) {
            Some(
                assignment[1..]
                    .iter()
                    .enumerate()
                    .map(|(i, &v)| {
                        let var = (i + 1) as i32;
                        if v > 0 {
                            var
                        } else {
                            -var
                        }
                    })
                    .collect(),
            )
        } else {
            None
        }
    }

    fn any_sat_rec(&self, f: SddId, assignment: &mut [i32]) -> bool {
        if f.is_false() {
            return false;
        }
        if f.is_true() {
            return true;
        }

        let node = self.node(f);

        match &node {
            Sdd::False => false,
            Sdd::True => true,

            Sdd::Literal(lit) => {
                let var = lit.var() as usize;
                assignment[var] = if lit.is_positive() { 1 } else { -1 };
                true
            }

            Sdd::Decision { elements, .. } => {
                for elem in elements {
                    if !self.is_false(elem.prime) && !self.is_false(elem.sub) {
                        if self.any_sat_rec(elem.prime, assignment) && self.any_sat_rec(elem.sub, assignment) {
                            return true;
                        }
                    }
                }
                false
            }
        }
    }

    /// Returns the size (number of nodes) in an SDD.
    pub fn size(&self, f: SddId) -> usize {
        let mut visited = HashSet::new();
        self.size_rec(f, &mut visited)
    }

    fn size_rec(&self, f: SddId, visited: &mut HashSet<SddId>) -> usize {
        if visited.contains(&f) {
            return 0;
        }
        visited.insert(f);

        if f.is_constant() {
            return 1;
        }

        let node = self.node(f);
        match &node {
            Sdd::False | Sdd::True => 1,
            Sdd::Literal(_) => 1,
            Sdd::Decision { elements, .. } => {
                let mut count = 1;
                for elem in elements {
                    count += self.size_rec(elem.prime, visited);
                    count += self.size_rec(elem.sub, visited);
                }
                count
            }
        }
    }

    /// Creates a conjunction of all given SDDs.
    pub fn and_all(&self, sdds: impl IntoIterator<Item = SddId>) -> SddId {
        let mut result = SddId::TRUE;
        for sdd in sdds {
            result = self.and(result, sdd);
            if self.is_false(result) {
                return result;
            }
        }
        result
    }

    /// Creates a disjunction of all given SDDs.
    pub fn or_all(&self, sdds: impl IntoIterator<Item = SddId>) -> SddId {
        let mut result = SddId::FALSE;
        for sdd in sdds {
            result = self.or(result, sdd);
            if self.is_true(result) {
                return result;
            }
        }
        result
    }

    /// Creates a cube (conjunction of literals).
    pub fn cube(&self, lits: impl IntoIterator<Item = i32>) -> SddId {
        self.and_all(lits.into_iter().map(|lit| self.literal(lit)))
    }

    /// Creates a clause (disjunction of literals).
    pub fn clause(&self, lits: impl IntoIterator<Item = i32>) -> SddId {
        self.or_all(lits.into_iter().map(|lit| self.literal(lit)))
    }

    /// Returns statistics about the manager.
    pub fn stats(&self) -> SddStats {
        SddStats {
            num_vars: self.num_vars(),
            num_nodes: self.num_nodes(),
            apply_calls: self.apply_calls.get(),
            cache_hits: self.cache_hits.get(),
        }
    }

    /// Clears all operation caches.
    pub fn clear_caches(&self) {
        self.apply_cache.borrow_mut().clear();
        self.count_cache.borrow_mut().clear();
    }

    /// Returns a human-readable representation of an SDD.
    pub fn display(&self, f: SddId) -> String {
        if f.is_false() {
            return "⊥".to_string();
        }
        if f.is_true() {
            return "⊤".to_string();
        }

        let node = self.node(f);

        match &node {
            Sdd::False => "⊥".to_string(),
            Sdd::True => "⊤".to_string(),
            Sdd::Literal(lit) => format!("{}", lit),
            Sdd::Decision { elements, .. } => {
                let elems: Vec<String> = elements
                    .iter()
                    .map(|e| format!("({} ∧ {})", self.display(e.prime), self.display(e.sub)))
                    .collect();
                elems.join(" ∨ ")
            }
        }
    }
}

impl fmt::Debug for SddManager {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("SddManager")
            .field("num_vars", &self.num_vars())
            .field("num_nodes", &self.num_nodes())
            .finish()
    }
}

/// Statistics about the SDD manager.
#[derive(Debug, Clone)]
pub struct SddStats {
    pub num_vars: u32,
    pub num_nodes: usize,
    pub apply_calls: usize,
    pub cache_hits: usize,
}

impl fmt::Display for SddStats {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let hit_rate = if self.apply_calls > 0 {
            100.0 * self.cache_hits as f64 / self.apply_calls as f64
        } else {
            0.0
        };
        write!(
            f,
            "SddStats {{ vars: {}, nodes: {}, applies: {}, cache_hits: {} ({:.1}%) }}",
            self.num_vars, self.num_nodes, self.apply_calls, self.cache_hits, hit_rate
        )
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_new_manager() {
        let mgr = SddManager::new(4);
        assert_eq!(mgr.num_vars(), 4);
        // 2 terminals + 8 literal nodes (4 vars * 2 polarities)
        assert!(mgr.num_nodes() >= 10);
    }

    #[test]
    fn test_constants() {
        let mgr = SddManager::new(2);
        assert!(mgr.is_false(mgr.false_sdd()));
        assert!(mgr.is_true(mgr.true_sdd()));
        assert!(!mgr.is_false(mgr.true_sdd()));
        assert!(!mgr.is_true(mgr.false_sdd()));
    }

    #[test]
    fn test_variables() {
        let mgr = SddManager::new(3);
        let x1 = mgr.var(1);
        let x2 = mgr.var(2);

        assert!(!mgr.is_constant(x1));
        assert!(!mgr.is_constant(x2));
        assert_ne!(x1, x2);
    }

    #[test]
    fn test_negation() {
        let mgr = SddManager::new(2);
        let x1 = mgr.var(1);
        let neg_x1 = mgr.negate(x1);

        assert_eq!(mgr.negate(neg_x1), x1);
        assert_ne!(x1, neg_x1);
    }

    #[test]
    fn test_and_terminals() {
        let mgr = SddManager::new(2);
        let t = mgr.true_sdd();
        let f = mgr.false_sdd();

        assert!(mgr.is_false(mgr.and(f, f)));
        assert!(mgr.is_false(mgr.and(f, t)));
        assert!(mgr.is_false(mgr.and(t, f)));
        assert!(mgr.is_true(mgr.and(t, t)));
    }

    #[test]
    fn test_or_terminals() {
        let mgr = SddManager::new(2);
        let t = mgr.true_sdd();
        let f = mgr.false_sdd();

        assert!(mgr.is_false(mgr.or(f, f)));
        assert!(mgr.is_true(mgr.or(f, t)));
        assert!(mgr.is_true(mgr.or(t, f)));
        assert!(mgr.is_true(mgr.or(t, t)));
    }

    #[test]
    fn test_and_with_var() {
        let mgr = SddManager::new(2);
        let x1 = mgr.var(1);
        let t = mgr.true_sdd();
        let f = mgr.false_sdd();

        assert_eq!(mgr.and(x1, t), x1);
        assert!(mgr.is_false(mgr.and(x1, f)));
        assert_eq!(mgr.and(x1, x1), x1);
    }

    #[test]
    fn test_or_with_var() {
        let mgr = SddManager::new(2);
        let x1 = mgr.var(1);
        let t = mgr.true_sdd();
        let f = mgr.false_sdd();

        assert!(mgr.is_true(mgr.or(x1, t)));
        assert_eq!(mgr.or(x1, f), x1);
        assert_eq!(mgr.or(x1, x1), x1);
    }

    #[test]
    fn test_contradiction() {
        let mgr = SddManager::new(2);
        let x1 = mgr.var(1);
        let neg_x1 = mgr.negate(x1);

        // x ∧ ¬x = ⊥
        assert!(mgr.is_false(mgr.and(x1, neg_x1)));
    }

    #[test]
    fn test_tautology() {
        let mgr = SddManager::new(2);
        let x1 = mgr.var(1);
        let neg_x1 = mgr.negate(x1);

        // x ∨ ¬x = ⊤
        assert!(mgr.is_true(mgr.or(x1, neg_x1)));
    }

    #[test]
    fn test_xor() {
        let mgr = SddManager::new(2);
        let x1 = mgr.var(1);

        // x ⊕ x = ⊥
        assert!(mgr.is_false(mgr.xor(x1, x1)));

        // x ⊕ ⊥ = x
        assert_eq!(mgr.xor(x1, mgr.false_sdd()), x1);

        // x ⊕ ⊤ = ¬x
        assert_eq!(mgr.xor(x1, mgr.true_sdd()), mgr.negate(x1));
    }

    #[test]
    fn test_implies() {
        let mgr = SddManager::new(2);
        let x1 = mgr.var(1);

        // x → x = ⊤
        assert!(mgr.is_true(mgr.implies(x1, x1)));

        // ⊥ → x = ⊤
        assert!(mgr.is_true(mgr.implies(mgr.false_sdd(), x1)));

        // x → ⊤ = ⊤
        assert!(mgr.is_true(mgr.implies(x1, mgr.true_sdd())));
    }

    #[test]
    fn test_equiv() {
        let mgr = SddManager::new(2);
        let x1 = mgr.var(1);

        // x ↔ x = ⊤
        assert!(mgr.is_true(mgr.equiv(x1, x1)));

        // x ↔ ¬x = ⊥
        assert!(mgr.is_false(mgr.equiv(x1, mgr.negate(x1))));
    }

    #[test]
    fn test_ite() {
        let mgr = SddManager::new(3);
        let x1 = mgr.var(1);
        let x2 = mgr.var(2);
        let x3 = mgr.var(3);

        // ite(⊤, x, y) = x
        assert_eq!(mgr.ite(mgr.true_sdd(), x2, x3), x2);

        // ite(⊥, x, y) = y
        assert_eq!(mgr.ite(mgr.false_sdd(), x2, x3), x3);

        // ite(c, x, x) = x
        assert_eq!(mgr.ite(x1, x2, x2), x2);
    }

    #[test]
    fn test_model_count_constant() {
        let mgr = SddManager::new(3);

        // ⊥ has 0 models
        assert_eq!(mgr.model_count(mgr.false_sdd()), BigUint::zero());

        // ⊤ has 2^3 = 8 models
        assert_eq!(mgr.model_count(mgr.true_sdd()), BigUint::from(8u32));
    }

    #[test]
    fn test_model_count_literal() {
        let mgr = SddManager::new(3);
        let x1 = mgr.var(1);

        // x1 has 2^2 = 4 models
        assert_eq!(mgr.model_count(x1), BigUint::from(4u32));

        // ¬x1 also has 4 models
        assert_eq!(mgr.model_count(mgr.negate(x1)), BigUint::from(4u32));
    }

    #[test]
    fn test_model_count_and() {
        let mgr = SddManager::new(3);
        let x1 = mgr.var(1);
        let x2 = mgr.var(2);

        // x1 ∧ x2 has 2^1 = 2 models
        let f = mgr.and(x1, x2);
        assert_eq!(mgr.model_count(f), BigUint::from(2u32));
    }

    #[test]
    fn test_any_sat() {
        let mgr = SddManager::new(3);
        let x1 = mgr.var(1);
        let x2 = mgr.var(2);

        // x1 ∧ x2 should have a satisfying assignment
        let f = mgr.and(x1, x2);
        let sat = mgr.any_sat(f);
        assert!(sat.is_some());

        let assignment = sat.unwrap();
        assert_eq!(assignment.len(), 3);
        // x1 and x2 should be positive
        assert!(assignment.iter().any(|&l| l == 1)); // x1 = true
        assert!(assignment.iter().any(|&l| l == 2)); // x2 = true
    }

    #[test]
    fn test_any_sat_unsat() {
        let mgr = SddManager::new(2);

        // ⊥ has no satisfying assignment
        assert!(mgr.any_sat(mgr.false_sdd()).is_none());
    }

    #[test]
    fn test_condition() {
        let mgr = SddManager::new(2);
        let x1 = mgr.var(1);
        let x2 = mgr.var(2);

        // (x1 ∧ x2)[x1 ← ⊤] = x2
        let f = mgr.and(x1, x2);
        let conditioned = mgr.condition(f, 1);
        assert_eq!(conditioned, x2);

        // (x1 ∧ x2)[x1 ← ⊥] = ⊥
        let conditioned = mgr.condition(f, -1);
        assert!(mgr.is_false(conditioned));
    }

    #[test]
    fn test_exists() {
        let mgr = SddManager::new(2);
        let x1 = mgr.var(1);
        let x2 = mgr.var(2);

        // ∃x1. (x1 ∧ x2) = x2
        let f = mgr.and(x1, x2);
        let result = mgr.exists(f, 1);
        assert_eq!(result, x2);
    }

    #[test]
    fn test_forall() {
        let mgr = SddManager::new(2);
        let x1 = mgr.var(1);
        let x2 = mgr.var(2);

        // ∀x1. (x1 ∨ x2) = x2
        let f = mgr.or(x1, x2);
        let result = mgr.forall(f, 1);
        assert_eq!(result, x2);

        // ∀x1. (x1 ∧ x2) = ⊥
        let g = mgr.and(x1, x2);
        let result = mgr.forall(g, 1);
        assert!(mgr.is_false(result));
    }

    #[test]
    fn test_cube() {
        let mgr = SddManager::new(3);

        // Cube: x1 ∧ ¬x2 ∧ x3
        let cube = mgr.cube([1, -2, 3]);
        assert!(mgr.is_satisfiable(cube));

        // Check model count: exactly 1 satisfying assignment
        assert_eq!(mgr.model_count(cube), BigUint::one());
    }

    #[test]
    fn test_clause() {
        let mgr = SddManager::new(3);

        // Clause: x1 ∨ ¬x2 ∨ x3
        let clause = mgr.clause([1, -2, 3]);
        assert!(mgr.is_satisfiable(clause));

        // Check model count: 7 satisfying assignments (all except x1=0, x2=1, x3=0)
        assert_eq!(mgr.model_count(clause), BigUint::from(7u32));
    }

    #[test]
    fn test_size() {
        let mgr = SddManager::new(2);
        let x1 = mgr.var(1);

        // Size of a literal should be 1
        assert_eq!(mgr.size(x1), 1);

        // Size of constants
        assert_eq!(mgr.size(mgr.true_sdd()), 1);
        assert_eq!(mgr.size(mgr.false_sdd()), 1);
    }

    #[test]
    fn test_vtree_types() {
        // Test balanced vtree
        let mgr_balanced = SddManager::new(4);
        assert_eq!(mgr_balanced.num_vars(), 4);

        // Test right-linear vtree
        let mgr_right = SddManager::with_right_linear_vtree(4);
        assert_eq!(mgr_right.num_vars(), 4);

        // Test left-linear vtree
        let mgr_left = SddManager::with_left_linear_vtree(4);
        assert_eq!(mgr_left.num_vars(), 4);
    }

    #[test]
    fn test_de_morgan() {
        let mgr = SddManager::new(2);
        let x1 = mgr.var(1);
        let x2 = mgr.var(2);

        // ¬(x1 ∧ x2) = ¬x1 ∨ ¬x2
        let lhs = mgr.negate(mgr.and(x1, x2));
        let rhs = mgr.or(mgr.negate(x1), mgr.negate(x2));

        // Check equivalence via XOR
        let diff = mgr.xor(lhs, rhs);
        assert!(mgr.is_false(diff), "De Morgan's law failed for AND");

        // ¬(x1 ∨ x2) = ¬x1 ∧ ¬x2
        let lhs = mgr.negate(mgr.or(x1, x2));
        let rhs = mgr.and(mgr.negate(x1), mgr.negate(x2));

        let diff = mgr.xor(lhs, rhs);
        assert!(mgr.is_false(diff), "De Morgan's law failed for OR");
    }
}
