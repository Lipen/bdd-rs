//! Zero-Suppressed Decision Diagram (ZDD) manager.
//!
//! This module provides the core ZDD implementation optimized for
//! representing families of sets (combinatorial sets).
//!
//! # Overview
//!
//! A ZDD is a variant of BDDs specifically designed for sparse set families.
//! The key difference is the **zero-suppression rule**: nodes where `hi = ⊥`
//! are eliminated (unlike BDDs which eliminate nodes where `lo = hi`).
//!
//! # Quick Start
//!
//! ```
//! use ananke_zdd::zdd::ZddManager;
//!
//! let mut mgr = ZddManager::new();
//!
//! // Create base sets (singletons)
//! let x1 = mgr.base(1);  // {{1}}
//! let x2 = mgr.base(2);  // {{2}}
//!
//! // Set operations
//! let union = mgr.union(x1, x2);      // {{1}, {2}}
//! let joined = mgr.join(x1, x2);      // {{1, 2}}
//!
//! assert_eq!(mgr.count(union), 2);
//! assert_eq!(mgr.count(joined), 1);
//! ```

use std::cell::RefCell;
use std::cmp::{Ordering, Reverse};
use std::collections::HashMap;

use crate::cache::{Cache, CacheKey, CountCache, OpType};
use crate::node::ZddNode;
use crate::reference::ZddId;
use crate::subtable::Subtable;
use crate::types::{Level, NodeId, Var};

/// The ZDD manager: owns all nodes and handles operations.
///
/// All ZDD operations go through the manager. The manager maintains:
/// - Node storage (Vec of [ZddNode])
/// - Per-variable subtables for hash-based lookup
/// - Operation caches for memoization
/// - Variable ordering
///
/// # Design
///
/// - **Uniqueness**: Identical nodes are shared (hash consing)
/// - **Zero-suppression**: Nodes with `hi = ⊥` are eliminated
/// - **Canonicity**: Each family has exactly one representation
///
/// # Terminal Semantics
///
/// - `ZddId::ZERO` (⊥): Empty family (no sets)
/// - `ZddId::ONE` (⊤): Family containing only the empty set: {∅}
pub struct ZddManager {
    /// Node storage. Index 0 = ZERO terminal, Index 1 = ONE terminal.
    nodes: RefCell<Vec<ZddNode>>,

    /// Per-variable subtables for unique table lookup.
    subtables: RefCell<Vec<Subtable>>,

    /// Variable to level mapping (indexed by var.id() for O(1) lookup).
    /// Index i stores the level of variable with id i, or None if not allocated.
    level_map: RefCell<Vec<Level>>,

    /// Level to variable mapping.
    var_order: RefCell<Vec<Var>>,

    /// Binary operation cache.
    cache: RefCell<Cache>,

    /// Counting cache.
    count_cache: RefCell<CountCache>,

    /// Cache for subset1(f, var) operations: (ZddId, Var) -> ZddId.
    subset1_cache: RefCell<HashMap<(ZddId, u32), ZddId>>,

    /// Cache for subset0(f, var) operations: (ZddId, Var) -> ZddId.
    subset0_cache: RefCell<HashMap<(ZddId, u32), ZddId>>,
}

impl Default for ZddManager {
    fn default() -> Self {
        Self::new()
    }
}

impl ZddManager {
    // ========================================================================
    // Construction
    // ========================================================================

    /// Creates a new ZDD manager.
    pub fn new() -> Self {
        Self::with_capacity(1024)
    }

    /// Creates a manager with specified initial node capacity.
    pub fn with_capacity(capacity: usize) -> Self {
        // Initialize with two terminal nodes
        let mut nodes = Vec::with_capacity(capacity.max(2));

        // Index 0: ZERO terminal (⊥)
        nodes.push(ZddNode::default());

        // Index 1: ONE terminal (⊤)
        nodes.push(ZddNode::default());

        // Level map
        let mut level_map = Vec::new();
        level_map.push(Level::new(u32::MAX)); // Var(0) sentinel

        Self {
            nodes: RefCell::new(nodes),
            subtables: RefCell::new(Vec::new()),
            level_map: RefCell::new(level_map),
            var_order: RefCell::new(Vec::new()),
            cache: RefCell::new(Cache::new()),
            count_cache: RefCell::new(CountCache::new()),
            subset1_cache: RefCell::new(HashMap::new()),
            subset0_cache: RefCell::new(HashMap::new()),
        }
    }

    // ========================================================================
    // Terminal Constants
    // ========================================================================

    /// Returns the empty family (⊥): contains no sets.
    pub fn zero(&self) -> ZddId {
        ZddId::ZERO
    }

    /// Returns the family containing only the empty set (⊤): {∅}.
    pub fn one(&self) -> ZddId {
        ZddId::ONE
    }

    /// Returns true if this is the empty family.
    #[inline(always)]
    pub fn is_zero(&self, f: ZddId) -> bool {
        f.is_zero()
    }

    /// Returns true if this is the {∅} family.
    #[inline(always)]
    pub fn is_one(&self, f: ZddId) -> bool {
        f.is_one()
    }

    /// Returns true if this is a terminal node.
    #[inline(always)]
    pub fn is_terminal(&self, f: ZddId) -> bool {
        f.is_terminal()
    }

    /// Returns true if the family is empty (contains no sets).
    pub fn is_empty(&self, f: ZddId) -> bool {
        f.is_zero()
    }

    // ========================================================================
    // Variable Management
    // ========================================================================

    /// Allocates a new variable and returns its ID.
    pub fn new_var(&self) -> Var {
        let mut level_map = self.level_map.borrow_mut();
        let new_id = level_map.len() as u32;
        let var = Var::new(new_id);

        // Add to ordering
        let level = Level::new(self.var_order.borrow().len() as u32);
        self.var_order.borrow_mut().push(var);

        // Allocate level for this variable
        level_map.push(level);
        self.subtables.borrow_mut().push(Subtable::new(var));

        var
    }

    /// Ensures a variable exists, creating it if necessary.
    pub fn ensure_var(&self, var: Var) -> Var {
        // Allocate variables up to and including this one
        while (self.level_map.borrow().len() as u32) <= var.id() {
            self.new_var();
        }
        var
    }

    /// Returns the number of variables.
    pub fn num_vars(&self) -> usize {
        self.var_order.borrow().len()
    }

    /// Gets the level of a variable in the current ordering.
    pub fn level(&self, var: Var) -> Level {
        self.level_map.borrow()[var.id() as usize]
    }

    /// Gets the variable at a given level.
    pub fn var_at_level(&self, level: Level) -> Var {
        self.var_order.borrow()[level.index()]
    }

    // ========================================================================
    // Node Construction
    // ========================================================================

    /// Creates or retrieves a ZDD node with the given variable and children.
    ///
    /// This is the core function that enforces the zero-suppression rule:
    /// if `hi = ⊥`, returns `lo` instead of creating a node.
    pub fn get_node(&self, var: Var, lo: ZddId, hi: ZddId) -> ZddId {
        // Zero-suppression rule: if hi = ⊥, return lo
        if hi.is_zero() {
            return lo;
        }

        let level = self.level(var);

        // Check unique table
        {
            let subtables = self.subtables.borrow();
            let nodes = self.nodes.borrow();
            if let Some(id) = subtables[level.index()].find(lo, hi, &nodes) {
                return ZddId::from_node(id);
            }
        }

        // Create new node
        let node = ZddNode::new(var, lo, hi);
        let id = {
            let mut nodes = self.nodes.borrow_mut();
            let id = NodeId::new(nodes.len() as u32);
            nodes.push(node);
            id
        };

        // Insert into unique table
        {
            let mut subtables = self.subtables.borrow_mut();
            let mut nodes = self.nodes.borrow_mut();
            subtables[level.index()].insert(lo, hi, id, &mut nodes);
        }

        ZddId::from_node(id)
    }

    /// Access node data.
    pub fn node(&self, id: ZddId) -> ZddNode {
        self.nodes.borrow()[id.index()]
    }

    // ========================================================================
    // Primitive Constructors
    // ========================================================================

    /// Creates a base set: `{{var}}` — family containing only the singleton `{var}`.
    ///
    /// This is the fundamental building block for ZDDs.
    pub fn base(&self, var: impl Into<Var>) -> ZddId {
        let var = var.into();
        self.ensure_var(var);
        // Node: var with lo=⊥ (sets without var), hi=⊤ (sets with var = {∅} + var = {{var}})
        self.get_node(var, ZddId::ZERO, ZddId::ONE)
    }

    /// Creates a singleton family: `{{v1, v2, ..., vn}}`.
    ///
    /// The result contains exactly one set with all the given elements.
    pub fn singleton(&self, vars: impl IntoIterator<Item = impl Into<Var>>) -> ZddId {
        let mut vars: Vec<Var> = vars.into_iter().map(|v| v.into()).collect();
        if vars.is_empty() {
            return ZddId::ONE; // {{}} = {∅}
        }

        // Ensure all variables exist
        for &var in &vars {
            self.ensure_var(var);
        }

        // Sort by level (highest level first for bottom-up construction)
        vars.sort_unstable_by_key(|&var| Reverse(self.level(var)));

        // Build from bottom up
        let mut result = ZddId::ONE;
        for var in vars {
            result = self.get_node(var, ZddId::ZERO, result);
        }
        result
    }

    /// Creates the power set of given variables: `2^{vars}`.
    ///
    /// Contains all subsets of the given variables.
    pub fn powerset(&self, vars: impl IntoIterator<Item = impl Into<Var>>) -> ZddId {
        let mut vars: Vec<Var> = vars.into_iter().map(|v| v.into()).collect();
        if vars.is_empty() {
            return ZddId::ONE; // 2^∅ = {∅}
        }

        // Ensure all variables exist
        for &var in &vars {
            self.ensure_var(var);
        }

        // Sort by level (highest level first)
        vars.sort_unstable_by_key(|&var| Reverse(self.level(var)));

        // Build from bottom up: at each variable, both branches lead to same subtree
        let mut result = ZddId::ONE;
        for var in vars {
            // lo = result (sets without var), hi = result (sets with var)
            result = self.get_node(var, result, result);
        }
        result
    }

    /// Creates all k-element subsets of given variables: `C(n, k)`.
    pub fn combinations(&self, vars: impl IntoIterator<Item = impl Into<Var>>, k: usize) -> ZddId {
        let vars: Vec<Var> = vars.into_iter().map(|v| v.into()).collect();

        if k == 0 {
            return ZddId::ONE; // C(n, 0) = {∅}
        }
        if k > vars.len() {
            return ZddId::ZERO; // C(n, k) = ∅ when k > n
        }

        // Ensure all variables exist
        for &var in &vars {
            self.ensure_var(var);
        }

        // Use recursive approach with memoization
        self.combinations_rec(&vars, 0, k)
    }

    fn combinations_rec(&self, vars: &[Var], start: usize, k: usize) -> ZddId {
        if k == 0 {
            return ZddId::ONE;
        }
        if start + k > vars.len() {
            return ZddId::ZERO;
        }
        if start + k == vars.len() {
            // Must take all remaining
            return self.singleton(vars[start..].iter().copied());
        }

        let var = vars[start];
        // Sets including var: combine with C(rest, k-1)
        let with_var = self.combinations_rec(vars, start + 1, k - 1);
        // Sets not including var: C(rest, k)
        let without_var = self.combinations_rec(vars, start + 1, k);

        self.get_node(var, without_var, with_var)
    }

    // ========================================================================
    // Set-Theoretic Operations
    // ========================================================================

    /// Union: `F ∪ G` — sets in either family.
    pub fn union(&self, f: ZddId, g: ZddId) -> ZddId {
        // Terminal cases
        if f.is_zero() {
            return g;
        }
        if g.is_zero() {
            return f;
        }
        if f == g {
            return f;
        }

        // Check cache
        let key = CacheKey::commutative(OpType::Union, f, g);
        if let Some(result) = self.cache.borrow().get(&key) {
            return result;
        }

        let result = if f.is_one() && g.is_one() {
            ZddId::ONE
        } else if f.is_one() {
            // g is non-terminal
            let g_node = self.node(g);
            let lo = self.union(ZddId::ONE, g_node.lo);
            self.get_node(g_node.var, lo, g_node.hi)
        } else if g.is_one() {
            // f is non-terminal
            let f_node = self.node(f);
            let lo = self.union(f_node.lo, ZddId::ONE);
            self.get_node(f_node.var, lo, f_node.hi)
        } else {
            // Both non-terminal
            let f_node = self.node(f);
            let g_node = self.node(g);

            let f_level = self.level(f_node.var);
            let g_level = self.level(g_node.var);
            match f_level.cmp(&g_level) {
                Ordering::Less => {
                    // f's variable is higher (closer to root)
                    let lo = self.union(f_node.lo, g);
                    self.get_node(f_node.var, lo, f_node.hi)
                }
                Ordering::Greater => {
                    // g's variable is higher
                    let lo = self.union(f, g_node.lo);
                    self.get_node(g_node.var, lo, g_node.hi)
                }
                Ordering::Equal => {
                    // Same variable
                    let lo = self.union(f_node.lo, g_node.lo);
                    let hi = self.union(f_node.hi, g_node.hi);
                    self.get_node(f_node.var, lo, hi)
                }
            }
        };

        self.cache.borrow_mut().insert(key, result);
        result
    }

    /// Intersection: F ∩ G — sets in both families.
    pub fn intersection(&self, f: ZddId, g: ZddId) -> ZddId {
        // Terminal cases
        if f.is_zero() || g.is_zero() {
            return ZddId::ZERO;
        }
        if f == g {
            return f;
        }
        if f.is_one() && g.is_one() {
            return ZddId::ONE;
        }

        // Check cache
        let key = CacheKey::commutative(OpType::Intersection, f, g);
        if let Some(result) = self.cache.borrow().get(&key) {
            return result;
        }

        let result = if f.is_one() {
            // f = {∅}, so intersection keeps only ∅ if g contains ∅
            if self.contains_empty(g) {
                ZddId::ONE
            } else {
                ZddId::ZERO
            }
        } else if g.is_one() {
            if self.contains_empty(f) {
                ZddId::ONE
            } else {
                ZddId::ZERO
            }
        } else {
            let f_node = self.node(f);
            let g_node = self.node(g);

            let f_level = self.level(f_node.var);
            let g_level = self.level(g_node.var);
            match f_level.cmp(&g_level) {
                Ordering::Less => {
                    // f's variable is higher, not in g's top variable
                    self.intersection(f_node.lo, g)
                }
                Ordering::Greater => self.intersection(f, g_node.lo),
                Ordering::Equal => {
                    let lo = self.intersection(f_node.lo, g_node.lo);
                    let hi = self.intersection(f_node.hi, g_node.hi);
                    self.get_node(f_node.var, lo, hi)
                }
            }
        };

        self.cache.borrow_mut().insert(key, result);
        result
    }

    /// Difference: `F \ G` — sets in F but not in G.
    pub fn difference(&self, f: ZddId, g: ZddId) -> ZddId {
        // Terminal cases
        if f.is_zero() {
            return ZddId::ZERO;
        }
        if g.is_zero() {
            return f;
        }
        if f == g {
            return ZddId::ZERO;
        }

        // Check cache
        let key = CacheKey::non_commutative(OpType::Difference, f, g);
        if let Some(result) = self.cache.borrow().get(&key) {
            return result;
        }

        let result = if f.is_one() {
            if self.contains_empty(g) {
                ZddId::ZERO
            } else {
                ZddId::ONE
            }
        } else if g.is_one() {
            // Remove ∅ from f
            let f_node = self.node(f);
            let lo = self.difference(f_node.lo, ZddId::ONE);
            self.get_node(f_node.var, lo, f_node.hi)
        } else {
            let f_node = self.node(f);
            let g_node = self.node(g);

            let f_level = self.level(f_node.var);
            let g_level = self.level(g_node.var);

            match f_level.cmp(&g_level) {
                Ordering::Less => {
                    let lo = self.difference(f_node.lo, g);
                    self.get_node(f_node.var, lo, f_node.hi)
                }
                Ordering::Greater => self.difference(f, g_node.lo),
                Ordering::Equal => {
                    let lo = self.difference(f_node.lo, g_node.lo);
                    let hi = self.difference(f_node.hi, g_node.hi);
                    self.get_node(f_node.var, lo, hi)
                }
            }
        };

        self.cache.borrow_mut().insert(key, result);
        result
    }

    /// Symmetric difference: F △ G — sets in exactly one of F or G.
    pub fn symmetric_difference(&self, f: ZddId, g: ZddId) -> ZddId {
        // F △ G = (F \ G) ∪ (G \ F) = (F ∪ G) \ (F ∩ G)
        let union = self.union(f, g);
        let inter = self.intersection(f, g);
        self.difference(union, inter)
    }

    // ========================================================================
    // ZDD-Specific Operations
    // ========================================================================

    /// Subset0: Sets NOT containing var.
    ///
    /// Returns the subfamily of F where var is not a member.
    pub fn subset0(&self, f: ZddId, var: Var) -> ZddId {
        if f.is_terminal() {
            return f;
        }

        // Check cache
        let cache_key = (f, var.id());
        if let Some(&result) = self.subset0_cache.borrow().get(&cache_key) {
            return result;
        }

        let f_node = self.node(f);
        let f_level = self.level(f_node.var);
        let var_level = self.level(var);

        let result = match f_level.cmp(&var_level) {
            Ordering::Less => {
                // var is below f's variable, recurse
                let lo = self.subset0(f_node.lo, var);
                let hi = self.subset0(f_node.hi, var);
                self.get_node(f_node.var, lo, hi)
            }
            Ordering::Equal => {
                // At the target variable
                f_node.lo
            }
            Ordering::Greater => {
                // var is above f's variable, all sets lack var
                f
            }
        };

        // Cache the result
        self.subset0_cache.borrow_mut().insert(cache_key, result);
        result
    }

    /// Subset1: Sets containing var (with var removed from each set).
    ///
    /// Returns the subfamily of F where var is a member, but removes var from each.
    pub fn subset1(&self, f: ZddId, var: Var) -> ZddId {
        if f.is_terminal() {
            return ZddId::ZERO; // Terminals don't contain var
        }

        // Check cache
        let cache_key = (f, var.id());
        if let Some(&result) = self.subset1_cache.borrow().get(&cache_key) {
            return result;
        }

        let f_node = self.node(f);
        let f_level = self.level(f_node.var);
        let var_level = self.level(var);

        let result = match f_level.cmp(&var_level) {
            Ordering::Less => {
                // var is below f's variable, recurse
                let lo = self.subset1(f_node.lo, var);
                let hi = self.subset1(f_node.hi, var);
                self.get_node(f_node.var, lo, hi)
            }
            Ordering::Equal => {
                // At the target variable
                f_node.hi
            }
            Ordering::Greater => {
                // var is above f's variable, no sets contain var
                ZddId::ZERO
            }
        };

        // Cache the result
        self.subset1_cache.borrow_mut().insert(cache_key, result);
        result
    }

    /// Change: Toggle var in all sets.
    ///
    /// For each set S in F:
    /// - If `var ∈ S`, result contains `S \ {var}`
    /// - If `var ∉ S`, result contains `S ∪ {var}`
    pub fn change(&self, f: ZddId, var: Var) -> ZddId {
        self.ensure_var(var);

        if f.is_zero() {
            return ZddId::ZERO;
        }
        if f.is_one() {
            // {∅} → {{var}}
            return self.base(var);
        }

        let f_node = self.node(f);
        let f_level = self.level(f_node.var);
        let var_level = self.level(var);

        match f_level.cmp(&var_level) {
            Ordering::Less => {
                // var is below f's variable
                let lo = self.change(f_node.lo, var);
                let hi = self.change(f_node.hi, var);
                self.get_node(f_node.var, lo, hi)
            }
            Ordering::Equal => {
                // Swap lo and hi branches
                self.get_node(f_node.var, f_node.hi, f_node.lo)
            }
            Ordering::Greater => {
                // var is above f's variable, add var to all sets
                self.get_node(var, ZddId::ZERO, f)
            }
        }
    }

    /// Onset: Sets containing var (keeping var).
    ///
    /// Unlike subset1, this keeps var in the result sets.
    pub fn onset(&self, f: ZddId, var: Var) -> ZddId {
        let s1 = self.subset1(f, var);
        // Add var back to all sets in s1
        if s1.is_zero() {
            return ZddId::ZERO;
        }
        self.get_node(var, ZddId::ZERO, s1)
    }

    /// Offset: Sets NOT containing var (same as subset0).
    pub fn offset(&self, f: ZddId, var: Var) -> ZddId {
        self.subset0(f, var)
    }

    /// Join: `{S ∪ T | S ∈ F, T ∈ G}`.
    ///
    /// Also known as the "cross product" or "product" operation.
    /// The result contains all unions of pairs of sets.
    pub fn join(&self, f: ZddId, g: ZddId) -> ZddId {
        // Terminal cases
        if f.is_zero() || g.is_zero() {
            return ZddId::ZERO;
        }
        if f.is_one() {
            return g; // {∅} ⊗ G = G
        }
        if g.is_one() {
            return f; // F ⊗ {∅} = F
        }

        // Check cache
        let key = CacheKey::commutative(OpType::Join, f, g);
        if let Some(result) = self.cache.borrow().get(&key) {
            return result;
        }

        let f_node = self.node(f);
        let g_node = self.node(g);

        let f_level = self.level(f_node.var);
        let g_level = self.level(g_node.var);
        let result = match f_level.cmp(&g_level) {
            Ordering::Less => {
                // f's variable is higher
                let lo = self.join(f_node.lo, g);
                let hi = self.join(f_node.hi, g);
                self.get_node(f_node.var, lo, hi)
            }
            Ordering::Greater => {
                // g's variable is higher
                let lo = self.join(f, g_node.lo);
                let hi = self.join(f, g_node.hi);
                self.get_node(g_node.var, lo, hi)
            }
            Ordering::Equal => {
                // Same variable
                // Sets without var from both
                let lo_lo = self.join(f_node.lo, g_node.lo);
                // Sets with var in f, without var in g
                let hi_lo = self.join(f_node.hi, g_node.lo);
                // Sets without var in f, with var in g
                let lo_hi = self.join(f_node.lo, g_node.hi);
                // Sets with var in both
                let hi_hi = self.join(f_node.hi, g_node.hi);

                // Combine: hi branch gets all combinations where at least one has var
                let hi = self.union(hi_lo, self.union(lo_hi, hi_hi));
                self.get_node(f_node.var, lo_lo, hi)
            }
        };

        self.cache.borrow_mut().insert(key, result);
        result
    }

    /// Meet: `{S ∩ T | S ∈ F, T ∈ G, S ∩ T ≠ ∅}`.
    ///
    /// The result contains non-empty intersections of pairs of sets.
    pub fn meet(&self, f: ZddId, g: ZddId) -> ZddId {
        // Terminal cases
        if f.is_zero() || g.is_zero() {
            return ZddId::ZERO;
        }
        if f.is_one() || g.is_one() {
            // {∅} ∩ anything = ∅ (excluded by S ∩ T ≠ ∅)
            return ZddId::ZERO;
        }

        // Check cache
        let key = CacheKey::commutative(OpType::Meet, f, g);
        if let Some(result) = self.cache.borrow().get(&key) {
            return result;
        }

        let f_node = self.node(f);
        let g_node = self.node(g);

        let f_level = self.level(f_node.var);
        let g_level = self.level(g_node.var);
        let result = match f_level.cmp(&g_level) {
            Ordering::Less => {
                // f's variable is higher, not in any g set at this level
                self.meet(f_node.lo, g)
            }
            Ordering::Greater => self.meet(f, g_node.lo),
            Ordering::Equal => {
                // Same variable
                let lo = self.meet(f_node.lo, g_node.lo);
                let hi = self.meet(f_node.hi, g_node.hi);
                // Only hi-hi contributes to hi branch (both must have var)
                self.union(lo, self.get_node(f_node.var, ZddId::ZERO, hi))
            }
        };

        self.cache.borrow_mut().insert(key, result);
        result
    }

    /// Add an element to every set in the family.
    ///
    /// Returns the family `{S ∪ {var} | S ∈ family}`.
    ///
    /// This is equivalent to joining family with the singleton {{var}}.
    pub fn add_element_to_all(&self, family: ZddId, var: Var) -> ZddId {
        if family.is_zero() {
            return ZddId::ZERO;
        }
        // Join with singleton set {var}
        self.join(family, self.base(var))
    }

    /// Remove all sets that contain BOTH var1 AND var2.
    ///
    /// Algorithm:
    /// 1. Get sets containing var1 (with var1 removed): `subset1(F, var1)`
    /// 2. Of those, get sets also containing var2 (with var2 removed): `subset1(..., var2)`
    /// 3. Reconstruct the "bad" sets by adding var1 and var2 back
    /// 4. Subtract from original family
    pub fn remove_sets_with_both(&self, family: ZddId, var1: Var, var2: Var) -> ZddId {
        // Get sets containing var1 (minus var1)
        let s1 = self.subset1(family, var1);
        if s1.is_zero() {
            return family; // No sets contain var1
        }

        // Get sets also containing var2 (minus var2)
        let s12 = self.subset1(s1, var2);
        if s12.is_zero() {
            return family; // No sets contain both
        }

        // Reconstruct: add var2 back, then var1
        let with_var2 = self.add_element_to_all(s12, var2);
        let bad_sets = self.add_element_to_all(with_var2, var1);

        self.difference(family, bad_sets)
    }

    // ========================================================================
    // Queries
    // ========================================================================

    /// Returns true if the family contains the empty set.
    pub fn contains_empty(&self, f: ZddId) -> bool {
        if f.is_zero() {
            return false;
        }
        if f.is_one() {
            return true;
        }
        // Recurse down lo branch (sets without top variable)
        self.contains_empty(self.node(f).lo)
    }

    /// Returns true if the family contains the given set.
    pub fn contains(&self, f: ZddId, set: &[Var]) -> bool {
        if set.is_empty() {
            return self.contains_empty(f);
        }

        // Check if all variables in set exist
        let level_map = self.level_map.borrow();
        for &var in set {
            let id = var.id() as usize;
            if id >= level_map.len() {
                return false; // Unknown variable can't be in any set
            }
        }

        let mut sorted_set: Vec<Var> = set.to_vec();
        sorted_set.sort_unstable_by_key(|&var| self.level(var));

        self.contains_rec(f, &sorted_set, 0)
    }

    fn contains_rec(&self, f: ZddId, set: &[Var], idx: usize) -> bool {
        if idx == set.len() {
            return self.contains_empty(f);
        }
        if f.is_terminal() {
            return false;
        }

        let f_node = self.node(f);
        let var = set[idx];
        let f_level = self.level(f_node.var);
        let var_level = self.level(var);

        match f_level.cmp(&var_level) {
            Ordering::Less => {
                // Current variable not in set, follow lo
                self.contains_rec(f_node.lo, set, idx)
            }
            Ordering::Equal => {
                // Variable matches, follow hi
                self.contains_rec(f_node.hi, set, idx + 1)
            }
            Ordering::Greater => {
                // Set requires a variable that's not in f
                false
            }
        }
    }

    // ========================================================================
    // Counting
    // ========================================================================

    /// Counts the number of sets in the family.
    pub fn count(&self, f: ZddId) -> u64 {
        if f.is_zero() {
            return 0;
        }
        if f.is_one() {
            return 1;
        }

        if let Some(cached) = self.count_cache.borrow().get(f) {
            return cached;
        }

        let f_node = self.node(f);
        let count = self.count(f_node.lo) + self.count(f_node.hi);

        self.count_cache.borrow_mut().insert(f, count);
        count
    }

    /// Returns the number of nodes in the ZDD.
    pub fn node_count(&self, f: ZddId) -> usize {
        let mut visited = std::collections::HashSet::new();
        self.node_count_rec(f, &mut visited)
    }

    fn node_count_rec(&self, f: ZddId, visited: &mut std::collections::HashSet<ZddId>) -> usize {
        if f.is_terminal() || visited.contains(&f) {
            return 0;
        }
        visited.insert(f);
        let f_node = self.node(f);
        1 + self.node_count_rec(f_node.lo, visited) + self.node_count_rec(f_node.hi, visited)
    }

    /// Total number of nodes in the manager.
    pub fn num_nodes(&self) -> usize {
        self.nodes.borrow().len()
    }

    // ========================================================================
    // Cache Management
    // ========================================================================

    /// Clears all caches.
    pub fn clear_caches(&self) {
        self.cache.borrow_mut().clear();
        self.count_cache.borrow_mut().clear();
        self.subset1_cache.borrow_mut().clear();
        self.subset0_cache.borrow_mut().clear();
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_terminals() {
        let mgr = ZddManager::new();
        assert!(mgr.is_zero(mgr.zero()));
        assert!(mgr.is_one(mgr.one()));
        assert!(mgr.is_terminal(mgr.zero()));
        assert!(mgr.is_terminal(mgr.one()));
    }

    #[test]
    fn test_base() {
        let mgr = ZddManager::new();
        let x1 = mgr.base(1);
        assert_eq!(mgr.count(x1), 1);
        assert!(!mgr.is_terminal(x1));
    }

    #[test]
    fn test_singleton() {
        let mgr = ZddManager::new();

        // Empty singleton = {∅}
        let empty: Vec<Var> = vec![];
        let s0 = mgr.singleton(empty);
        assert!(mgr.is_one(s0));

        // {{1, 2}}
        let s12 = mgr.singleton([1u32, 2]);
        assert_eq!(mgr.count(s12), 1);
        assert!(mgr.contains(s12, &[Var::new(1), Var::new(2)]));
        assert!(!mgr.contains(s12, &[Var::new(1)]));
    }

    #[test]
    fn test_union() {
        let mgr = ZddManager::new();
        let x1 = mgr.base(1);
        let x2 = mgr.base(2);

        let union = mgr.union(x1, x2);
        assert_eq!(mgr.count(union), 2);
    }

    #[test]
    fn test_join() {
        let mgr = ZddManager::new();
        let x1 = mgr.base(1);
        let x2 = mgr.base(2);

        // {{1}} ⊗ {{2}} = {{1, 2}}
        let joined = mgr.join(x1, x2);
        assert_eq!(mgr.count(joined), 1);
        assert!(mgr.contains(joined, &[Var::new(1), Var::new(2)]));
    }

    #[test]
    fn test_intersection() {
        let mgr = ZddManager::new();
        let x1 = mgr.base(1);
        let x2 = mgr.base(2);

        // {{1}} ∩ {{2}} = ∅
        let inter = mgr.intersection(x1, x2);
        assert!(mgr.is_zero(inter));

        // ({{1}} ∪ {{2}}) ∩ {{1}} = {{1}}
        let union = mgr.union(x1, x2);
        let inter2 = mgr.intersection(union, x1);
        assert_eq!(inter2, x1);
    }

    #[test]
    fn test_difference() {
        let mgr = ZddManager::new();
        let x1 = mgr.base(1);
        let x2 = mgr.base(2);
        let union = mgr.union(x1, x2);

        // ({{1}} ∪ {{2}}) \ {{1}} = {{2}}
        let diff = mgr.difference(union, x1);
        assert_eq!(diff, x2);
    }

    #[test]
    fn test_powerset() {
        let mgr = ZddManager::new();

        // 2^{1,2} = {∅, {1}, {2}, {1,2}}
        let ps = mgr.powerset([1u32, 2]);
        assert_eq!(mgr.count(ps), 4);
    }

    #[test]
    fn test_combinations() {
        let mgr = ZddManager::new();

        // C(4, 2) = 6
        let c42 = mgr.combinations([1u32, 2, 3, 4], 2);
        assert_eq!(mgr.count(c42), 6);

        // C(5, 0) = 1
        let c50 = mgr.combinations([1u32, 2, 3, 4, 5], 0);
        assert_eq!(mgr.count(c50), 1);
        assert!(mgr.is_one(c50));

        // C(3, 5) = 0
        let c35 = mgr.combinations([1u32, 2, 3], 5);
        assert!(mgr.is_zero(c35));
    }

    #[test]
    fn test_subset_operations() {
        let mgr = ZddManager::new();

        // Family: {{1}, {2}, {1,2}}
        let x1 = mgr.base(1);
        let x2 = mgr.base(2);
        let x12 = mgr.join(x1, x2);
        let family = mgr.union(mgr.union(x1, x2), x12);
        assert_eq!(mgr.count(family), 3);

        // subset0(F, 1) = {{2}}
        let s0 = mgr.subset0(family, Var::new(1));
        assert_eq!(mgr.count(s0), 1);
        assert!(mgr.contains(s0, &[Var::new(2)]));

        // subset1(F, 1) = {∅, {2}} (from {1} and {1,2})
        let s1 = mgr.subset1(family, Var::new(1));
        assert_eq!(mgr.count(s1), 2);
    }

    #[test]
    fn test_change() {
        let mgr = ZddManager::new();
        let x1 = mgr.base(1);

        // change({{1}}, 1) = {∅}
        let changed = mgr.change(x1, Var::new(1));
        assert!(mgr.is_one(changed));

        // change({∅}, 1) = {{1}}
        let changed2 = mgr.change(ZddId::ONE, Var::new(1));
        assert_eq!(changed2, x1);
    }

    #[test]
    fn test_contains() {
        let mgr = ZddManager::new();
        let x1 = mgr.base(1);
        let x2 = mgr.base(2);
        let x12 = mgr.join(x1, x2);
        let family = mgr.union(mgr.union(x1, x2), x12);

        assert!(mgr.contains(family, &[Var::new(1)]));
        assert!(mgr.contains(family, &[Var::new(2)]));
        assert!(mgr.contains(family, &[Var::new(1), Var::new(2)]));
        assert!(!mgr.contains(family, &[]));
        assert!(!mgr.contains(family, &[Var::new(3)]));
    }

    #[test]
    fn test_subset1_then_subset1() {
        // Test the logic used in remove_sets_with_both:
        // Find sets containing both var1 and var2
        let mgr = ZddManager::new();

        // Create family: {{1}, {2}, {1,2}, {1,3}, {1,2,3}}
        let v1 = mgr.base(1); // {{1}}
        let v2 = mgr.base(2); // {{2}}
        let v3 = mgr.base(3); // {{3}}

        let v12 = mgr.join(v1, v2); // {{1,2}}
        let v13 = mgr.join(v1, v3); // {{1,3}}
        let v123 = mgr.join(mgr.join(v1, v2), v3); // {{1,2,3}}

        let family = mgr.union(mgr.union(mgr.union(mgr.union(v1, v2), v12), v13), v123);

        assert_eq!(mgr.count(family), 5);

        // subset1(family, 1) = sets containing 1, minus 1
        // {1} -> {}, {1,2} -> {2}, {1,3} -> {3}, {1,2,3} -> {2,3}
        // Result: {{}, {2}, {3}, {2,3}}
        let s1 = mgr.subset1(family, Var::new(1));
        assert_eq!(mgr.count(s1), 4);

        // subset1(s1, 2) = sets containing 2, minus 2
        // From s1: {2} -> {}, {2,3} -> {3}
        // Result: {{}, {3}}
        let s12 = mgr.subset1(s1, Var::new(2));
        assert_eq!(mgr.count(s12), 2);
        assert!(mgr.contains(s12, &[]));
        assert!(mgr.contains(s12, &[Var::new(3)]));
    }

    #[test]
    fn test_add_element_to_all_basic() {
        let mgr = ZddManager::new();

        // Start with family {{}, {1}}
        let one = mgr.one(); // {{}}
        let v1 = mgr.base(1); // {{1}}
        let family = mgr.union(one, v1);

        // Add element 2 to all sets
        // Should produce {{2}, {1,2}}
        let v2 = Var::new(2);
        mgr.ensure_var(v2);

        // Create {{2}, {1,2}} properly using ZDD operations
        let expected = mgr.join(family, mgr.base(2));

        // Now manually check what adding 2 to {{}, {1}} should give
        // Empty set {} + 2 = {2}
        // {1} + 2 = {1,2}
        // So we should get {{2}, {1,2}}
        assert_eq!(mgr.count(expected), 2);
        assert!(mgr.contains(expected, &[Var::new(2)]));
        assert!(mgr.contains(expected, &[Var::new(1), Var::new(2)]));
    }

    #[test]
    fn test_remove_sets_with_both_vars() {
        // Test the logic: remove all sets containing BOTH var1 AND var2
        let mgr = ZddManager::new();

        // Start simple: Family: {{1}, {2}, {1,2}}
        let v1 = mgr.base(1); // {{1}}
        let v2 = mgr.base(2); // {{2}}
        let v12 = mgr.join(v1, v2); // {{1,2}}

        let family = mgr.union(mgr.union(v1, v2), v12);
        assert_eq!(mgr.count(family), 3);

        // subset1(family, 1) = sets with 1, minus 1
        // {1} -> {}, {1,2} -> {2}
        // Result: {{}, {2}}
        let s1 = mgr.subset1(family, Var::new(1));
        assert_eq!(mgr.count(s1), 2, "subset1(family, 1) should have 2 sets");

        // subset1(s1, 2) = sets with 2, minus 2
        // {2} -> {}
        // Result: {{}} (one set)
        let s12 = mgr.subset1(s1, Var::new(2));
        assert_eq!(mgr.count(s12), 1, "subset1(s1, 2) should have 1 set");

        // Reconstruct: add 2 back, then add 1 back
        // {{}} + 2 -> {{2}}
        // {{2}} + 1 -> {{1,2}}
        let with_v2 = mgr.add_element_to_all(s12, Var::new(2));
        assert_eq!(mgr.count(with_v2), 1);

        let with_v1 = mgr.add_element_to_all(with_v2, Var::new(1));
        assert_eq!(mgr.count(with_v1), 1);
        assert!(mgr.contains(with_v1, &[Var::new(1), Var::new(2)]));

        // Remove from original family
        let result = mgr.difference(family, with_v1);
        assert_eq!(mgr.count(result), 2);

        // Should contain: {1}, {2}
        assert!(mgr.contains(result, &[Var::new(1)]));
        assert!(mgr.contains(result, &[Var::new(2)]));

        // Should NOT contain: {1,2}
        assert!(!mgr.contains(result, &[Var::new(1), Var::new(2)]));
    }
}
