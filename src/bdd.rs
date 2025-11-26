//! Binary Decision Diagram (BDD) implementation.
//!
//! This module provides a **reduced ordered BDD** (ROBDD) with a **shared multi-rooted graph**
//! representation and **complement edges**. BDDs are a canonical data structure for representing
//! and manipulating Boolean functions efficiently.
//!
//! # Architecture
//!
//! The implementation follows a **manager-centric design** with **per-level subtables** (similar to CUDD):
//!
//! ```text
//! ┌──────────────────────────────────────────────────────────────────────────┐
//! │                           Bdd (Manager)                                  │
//! │  ┌─────────────┐  ┌─────────────┐  ┌──────────────────────────────────┐  │
//! │  │   Storage   │  │    Cache    │  │       Variable Ordering          │  │
//! │  │ (raw node   │  │  (ITE ops)  │  │    (level ↔ variable map)        │  │
//! │  │   data)     │  │             │  │                                  │  │
//! │  └─────────────┘  └─────────────┘  └──────────────────────────────────┘  │
//! │                                                                          │
//! │  ┌────────────────────────────────────────────────────────────────────┐  │
//! │  │                    Per-Level Subtables                             │  │
//! │  │  ┌────────────┐  ┌────────────┐  ┌────────────┐                    │  │
//! │  │  │ Level 0    │  │ Level 1    │  │ Level 2    │  ...               │  │
//! │  │  │ (var x1)   │  │ (var x2)   │  │ (var x3)   │                    │  │
//! │  │  │ HashMap    │  │ HashMap    │  │ HashMap    │                    │  │
//! │  │  │ (lo,hi)→idx│  │ (lo,hi)→idx│  │ (lo,hi)→idx│                    │  │
//! │  │  └────────────┘  └────────────┘  └────────────┘                    │  │
//! │  └────────────────────────────────────────────────────────────────────┘  │
//! └──────────────────────────────────────────────────────────────────────────┘
//!          │
//!          ▼
//! ┌─────────────────┐
//! │   Ref (handle)  │  32-bit: index (31 bits) + complement flag (1 bit)
//! └─────────────────┘
//! ```
//!
//! - All BDD nodes live in a **shared storage pool** managed by [`Bdd`]
//! - **Per-level subtables** enable efficient node lookup by (low, high) children
//! - Variable reordering swaps subtables, making it efficient
//! - Multiple BDD roots can share subgraphs (structural sharing)
//! - [`Ref`] is a lightweight handle to a node in the pool
//! - Negation uses **complement edges** (flipping a bit, no new nodes)
//!
//! # Terminology
//!
//! | Term | Description |
//! |------|-------------|
//! | **BDD** | A directed acyclic graph representing a Boolean function. In this crate, often refers to a [`Ref`] pointing to the root. |
//! | **Manager** ([`Bdd`]) | The central structure managing node storage, caching, and variable ordering. |
//! | **Node** ([`Node`]) | A decision node with a variable and two children (low/high edges). |
//! | **Reference** ([`Ref`]) | A 32-bit handle: 31-bit index + 1-bit complement flag. |
//! | **Terminal** | Leaf nodes `zero` (⊥) and `one` (⊤) representing constants. |
//! | **Low edge** | Followed when the decision variable is false. |
//! | **High edge** | Followed when the decision variable is true. |
//! | **Complement edge** | A negated reference (complement flag set). Only low edges can be complemented. |
//! | **Level** | Position in the variable ordering (0 = top/root). |
//! | **Forwarding pointer** | Temporary redirect during variable reordering. |
//!
//! # Key Properties
//!
//! - **Canonical**: Each Boolean function has exactly one BDD representation (up to complement)
//! - **Reduced**: No redundant nodes (if low == high, node is eliminated)
//! - **Ordered**: Variables appear in consistent order on all paths (enables efficient operations)
//! - **Shared**: Isomorphic subgraphs are shared (hash consing)
//! - **Complement edges**: Negation is O(1), no node duplication
//!
//! # Variable Ordering
//!
//! The BDD uses **explicit variable ordering** where:
//! - Variable IDs are stable identifiers (never change)
//! - Variable levels determine position in the BDD (can change via reordering)
//! - Lower level = closer to root = decided earlier
//!
//! Good variable ordering can exponentially reduce BDD size. Use [`sift_all_variables`](Bdd::sift_all_variables)
//! for automatic optimization.
//!
//! # Examples
//!
//! ## Basic Operations
//!
//! ```
//! use bdd_rs::bdd::Bdd;
//!
//! let bdd = Bdd::default();
//!
//! // Create variables
//! let x = bdd.mk_var(1);
//! let y = bdd.mk_var(2);
//!
//! // Boolean operations
//! let f = bdd.apply_and(x, y);  // x ∧ y
//! let g = bdd.apply_or(x, -y);  // x ∨ ¬y  (negation via complement edge)
//! let h = bdd.apply_xor(x, y);  // x ⊕ y
//!
//! // Check satisfiability
//! assert!(!bdd.is_zero(f));     // f is satisfiable
//! assert!(bdd.is_zero(bdd.apply_and(x, -x)));  // x ∧ ¬x is unsatisfiable
//! ```
//!
//! ## Quantification
//!
//! ```
//! use bdd_rs::bdd::Bdd;
//! use bdd_rs::types::Var;
//!
//! let bdd = Bdd::default();
//! let x = bdd.mk_var(1);
//! let y = bdd.mk_var(2);
//!
//! let f = bdd.apply_and(x, y);  // x ∧ y
//!
//! // Existential: ∃x. (x ∧ y) = y
//! let exists_x = bdd.exists(f, [Var::new(1)]);
//! assert_eq!(exists_x, y);
//!
//! // Universal: ∀x. (x ∧ y) = ⊥
//! let forall_x = bdd.forall(f, [Var::new(1)]);
//! assert!(bdd.is_zero(forall_x));
//! ```
//!
//! ## Variable Reordering
//!
//! ```
//! use bdd_rs::bdd::Bdd;
//! use bdd_rs::types::Level;
//!
//! let bdd = Bdd::default();
//! let x = bdd.mk_var(1);
//! let y = bdd.mk_var(2);
//! let mut f = bdd.apply_and(x, y);
//!
//! // Swap adjacent levels and remap references
//! let mapping = bdd.swap_adjacent_inplace(Level::new(0)).unwrap();
//! f = bdd.apply_mapping(f, &mapping);  // Update reference using the mapping
//! ```

use std::cell;
use std::cell::{Cell, RefCell};
use std::cmp::{min, Ordering};
use std::collections::{HashMap, HashSet};
use std::fmt::Debug;

use log::debug;

use crate::cache::Cache;
use crate::node::Node;
use crate::reference::Ref;
use crate::subtable::Subtable;
use crate::types::{Level, Lit, Var};
use crate::utils::OpKey;

// ============================================================================
// Bdd struct and constructors
// ============================================================================

/// The BDD manager: a shared multi-rooted graph with complement edges.
///
/// This is the central structure for creating and manipulating BDDs.
/// It maintains:
/// - A **node storage array** (`Vec<Node>`) for storing node data
/// - **Per-level subtables** for efficient hash-based node lookup
/// - An **operation cache** for memoizing ITE results
/// - An **explicit variable ordering** that can be dynamically changed
///
/// # Design
///
/// All BDD operations go through the manager.
/// The manager owns the storage and ensures:
/// - **Uniqueness**: Identical nodes are shared (hash consing via per-level subtables)
/// - **Reduction**: Redundant nodes are eliminated automatically
/// - **Canonicity**: Each function has exactly one representation
///
/// ## Architecture
///
/// ```text
/// nodes[0] = (unused, sentinel)
/// nodes[1] = Terminal ONE node
/// nodes[2] = First variable node
/// ...
///
/// subtables[0] → HashMap for level 0: (low, high) → node_index
/// subtables[1] → HashMap for level 1: (low, high) → node_index
/// ...
/// ```
///
/// # Fields
///
/// - `zero`: The constant false terminal (index 1, negated)
/// - `one`: The constant true terminal (index 1, positive)
///
/// # Thread Safety
///
/// The manager uses `RefCell` internally and is **not thread-safe**.
/// For concurrent use, wrap in appropriate synchronization primitives.
///
/// # Examples
///
/// ```
/// use bdd_rs::bdd::Bdd;
///
/// // Default: 2^20 (~1M) nodes capacity
/// let bdd = Bdd::default();
///
/// // Custom capacity for large problems
/// let big_bdd = Bdd::new(24);  // 2^24 (~16M) nodes
/// ```
pub struct Bdd {
    /// Node storage: Vec of Node, indexed by node ID.
    /// Index 0 is reserved (unused), index 1 is the terminal node (@1).
    nodes: RefCell<Vec<Node>>,
    /// Set of free (recycled) node indices available for reuse.
    free_set: RefCell<HashSet<u32>>,
    cache: RefCell<Cache<OpKey, Ref>>,
    size_cache: RefCell<Cache<Ref, u64>>,
    pub zero: Ref,
    pub one: Ref,
    var_order: RefCell<Vec<Var>>,            // level -> variable
    level_map: RefCell<HashMap<Var, Level>>, // variable -> level
    subtables: RefCell<Vec<Subtable>>,       // level -> subtable
    next_var_id: Cell<u32>,                  // next variable ID to allocate
}

impl Bdd {
    /// Creates a new BDD manager with the specified storage capacity.
    ///
    /// The capacity is specified in bits, so the actual number of nodes is `2^storage_bits`.
    /// The cache size is automatically configured to `min(storage_bits, 16)` bits.
    ///
    /// # Arguments
    ///
    /// * `storage_bits` - Storage capacity in bits (must be ≤ 31). Typical values:
    ///   - 16: 65K nodes (small problems)
    ///   - 20: 1M nodes (default, medium problems)
    ///   - 24: 16M nodes (large problems)
    ///
    /// # Panics
    ///
    /// Panics if `storage_bits > 31`.
    ///
    /// # Examples
    ///
    /// ```
    /// use bdd_rs::bdd::Bdd;
    ///
    /// // Small BDD for simple problems
    /// let small_bdd = Bdd::new(16);
    /// assert_eq!(small_bdd.num_nodes(), 1);  // Just the terminal node
    ///
    /// // Large BDD for complex problems
    /// let large_bdd = Bdd::new(24);
    /// assert_eq!(large_bdd.num_nodes(), 1);
    /// ```
    pub fn new(storage_bits: usize) -> Self {
        assert!(storage_bits <= 31, "Storage bits should be in the range 0..=31");

        let cache_bits = min(storage_bits, 16);
        let capacity = 1 << storage_bits;

        // Initialize node storage with reserved slot 0 and terminal node at index 1
        let mut nodes = Vec::with_capacity(capacity);
        nodes.push(Node::default()); // Index 0 is reserved (unused)
        nodes.push(Node::default()); // Index 1 is the terminal node (@1)

        let one = Ref::positive(1);
        let zero = -one;

        Self {
            nodes: RefCell::new(nodes),
            free_set: RefCell::new(HashSet::new()),
            cache: RefCell::new(Cache::new(cache_bits)),
            size_cache: RefCell::new(Cache::new(cache_bits)),
            zero,
            one,
            var_order: RefCell::new(Vec::new()),
            level_map: RefCell::new(HashMap::new()),
            subtables: RefCell::new(Vec::new()),
            next_var_id: Cell::new(1), // Variables start at 1
        }
    }
}

// ============================================================================
// Trait implementations
// ============================================================================

impl Default for Bdd {
    fn default() -> Self {
        Bdd::new(20)
    }
}

impl Debug for Bdd {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Bdd")
            .field("capacity", &self.nodes().capacity())
            .field("size", &self.num_nodes())
            .field(
                "order",
                &format_args!(
                    "[{}]",
                    self.var_order().iter().map(|v| v.to_string()).collect::<Vec<_>>().join(", ")
                ),
            )
            .finish()
    }
}

// ============================================================================
// Internal accessors
// ============================================================================

impl Bdd {
    pub fn nodes(&self) -> cell::Ref<'_, Vec<Node>> {
        self.nodes.borrow()
    }
    fn nodes_mut(&self) -> cell::RefMut<'_, Vec<Node>> {
        self.nodes.borrow_mut()
    }

    pub fn free_set(&self) -> cell::Ref<'_, HashSet<u32>> {
        self.free_set.borrow()
    }
    fn free_set_mut(&self) -> cell::RefMut<'_, HashSet<u32>> {
        self.free_set.borrow_mut()
    }

    pub fn var_order(&self) -> cell::Ref<'_, Vec<Var>> {
        self.var_order.borrow()
    }
    fn var_order_mut(&self) -> cell::RefMut<'_, Vec<Var>> {
        self.var_order.borrow_mut()
    }

    pub fn level_map(&self) -> cell::Ref<'_, HashMap<Var, Level>> {
        self.level_map.borrow()
    }
    fn level_map_mut(&self) -> cell::RefMut<'_, HashMap<Var, Level>> {
        self.level_map.borrow_mut()
    }

    pub fn subtables(&self) -> cell::Ref<'_, Vec<Subtable>> {
        self.subtables.borrow()
    }
    fn subtables_mut(&self) -> cell::RefMut<'_, Vec<Subtable>> {
        self.subtables.borrow_mut()
    }

    /// Returns the number of allocated nodes (excluding reserved slot 0 and free slots).
    pub fn num_nodes(&self) -> usize {
        // nodes.len() includes reserved slot 0, subtract 1 for that
        self.nodes().len() - 1 - self.free_set().len()
    }

    /// Returns a reference to the operation cache.
    pub fn cache(&self) -> cell::Ref<'_, Cache<OpKey, Ref>> {
        self.cache.borrow()
    }
    fn cache_mut(&self) -> cell::RefMut<'_, Cache<OpKey, Ref>> {
        self.cache.borrow_mut()
    }

    /// Returns a reference to the size computation cache.
    pub fn size_cache(&self) -> cell::Ref<'_, Cache<Ref, u64>> {
        self.size_cache.borrow()
    }
    fn size_cache_mut(&self) -> cell::RefMut<'_, Cache<Ref, u64>> {
        self.size_cache.borrow_mut()
    }
}

// ============================================================================
// Node inspection
// ============================================================================

impl Bdd {
    /// Gets a copy of the node at the given index.
    pub fn node(&self, index: u32) -> Node {
        self.nodes()[index as usize]
    }

    /// Gets the low child of a node.
    ///
    /// Returns the low edge of the node at the given index.
    pub fn low(&self, index: u32) -> Ref {
        self.nodes()[index as usize].low
    }

    /// Gets the high child of a node.
    ///
    /// Returns the high edge of the node at the given index.
    pub fn high(&self, index: u32) -> Ref {
        self.nodes()[index as usize].high
    }

    /// Gets the low child of a BDD node, respecting complement edges.
    ///
    /// If the node reference is negated, the returned child is also negated.
    /// This maintains the complement edge semantics throughout traversal.
    pub fn low_node(&self, node_ref: Ref) -> Ref {
        let low = self.low(node_ref.index());
        if node_ref.is_negated() {
            -low
        } else {
            low
        }
    }

    /// Gets the high child of a BDD node, respecting complement edges.
    ///
    /// If the node reference is negated, the returned child is also negated.
    /// This maintains the complement edge semantics throughout traversal.
    pub fn high_node(&self, node_ref: Ref) -> Ref {
        let high = self.high(node_ref.index());
        if node_ref.is_negated() {
            -high
        } else {
            high
        }
    }

    /// Gets the variable of a node at the given index.
    pub fn variable(&self, index: u32) -> Var {
        self.nodes()[index as usize].variable
    }
}

// ============================================================================
// Predicates
// ============================================================================

impl Bdd {
    /// Checks if a BDD node represents the constant false.
    ///
    /// # Examples
    ///
    /// ```
    /// use bdd_rs::bdd::Bdd;
    ///
    /// let bdd = Bdd::default();
    /// assert!(bdd.is_zero(bdd.zero));
    /// assert!(!bdd.is_zero(bdd.one));
    ///
    /// let x = bdd.mk_var(1);
    /// let contradiction = bdd.apply_and(x, -x);
    /// assert!(bdd.is_zero(contradiction));
    /// ```
    pub fn is_zero(&self, node_ref: Ref) -> bool {
        node_ref == self.zero
    }

    /// Checks if a BDD node represents the constant true.
    ///
    /// # Examples
    ///
    /// ```
    /// use bdd_rs::bdd::Bdd;
    ///
    /// let bdd = Bdd::default();
    /// assert!(bdd.is_one(bdd.one));
    /// assert!(!bdd.is_one(bdd.zero));
    ///
    /// let x = bdd.mk_var(1);
    /// let tautology = bdd.apply_or(x, -x);
    /// assert!(bdd.is_one(tautology));
    /// ```
    pub fn is_one(&self, node_ref: Ref) -> bool {
        node_ref == self.one
    }

    /// Checks if a BDD node is a terminal (constant) node.
    ///
    /// Returns true if the node is either zero (false) or one (true).
    ///
    /// # Examples
    ///
    /// ```
    /// use bdd_rs::bdd::Bdd;
    ///
    /// let bdd = Bdd::default();
    /// assert!(bdd.is_terminal(bdd.zero));
    /// assert!(bdd.is_terminal(bdd.one));
    ///
    /// let x = bdd.mk_var(1);
    /// assert!(!bdd.is_terminal(x));
    /// ```
    pub fn is_terminal(&self, node_ref: Ref) -> bool {
        self.is_zero(node_ref) || self.is_one(node_ref)
    }
}

// ============================================================================
// Variable management
// ============================================================================

impl Bdd {
    /// Allocates a new variable and adds it to the end of the variable ordering.
    ///
    /// # Returns
    ///
    /// The newly allocated variable.
    ///
    /// # Examples
    ///
    /// ```
    /// use bdd_rs::bdd::Bdd;
    ///
    /// let bdd = Bdd::default();
    /// let var = bdd.allocate_variable();
    /// let x = bdd.mk_var(var);  // Can pass Var directly
    /// ```
    pub fn allocate_variable(&self) -> Var {
        let var_id = self.next_var_id.get();
        self.next_var_id.set(var_id + 1);

        let var = Var::new(var_id);
        let level = Level::new(self.var_order().len());

        self.var_order_mut().push(var);
        self.level_map_mut().insert(var, level);
        self.subtables_mut().push(Subtable::new(var));

        var
    }

    /// Registers a variable in the ordering if it's not already present.
    ///
    /// This is called automatically by mk_var.
    fn register_variable(&self, var_id: u32) {
        let var = Var::new(var_id);

        if !self.level_map().contains_key(&var) {
            let level = Level::new(self.var_order().len());
            self.var_order_mut().push(var);
            self.level_map_mut().insert(var, level);
            self.subtables_mut().push(Subtable::new(var));

            // Update next_var_id if needed
            let next_val = self.next_var_id.get();
            if var_id >= next_val {
                self.next_var_id.set(var_id + 1);
            }
        }
    }

    /// Returns true if var1 comes before var2 in the variable ordering.
    ///
    /// Uses the explicit variable ordering to compare levels.
    fn var_precedes(&self, var1: Var, var2: Var) -> bool {
        if var1.is_terminal() || var2.is_terminal() {
            return false;
        }

        let level1 = self.get_level(var1);
        let level2 = self.get_level(var2);

        match (level1, level2) {
            (Some(l1), Some(l2)) => l1 < l2,
            (Some(_), None) => true,
            (None, Some(_)) => false,
            (None, None) => var1.id() < var2.id(), // fallback to ID comparison
        }
    }

    /// Compares two variables by their level in the variable ordering.
    ///
    /// Returns the variable that should appear *first* (at a lower level/higher in the tree).
    /// Uses the explicit variable ordering to determine precedence.
    ///
    /// # Arguments
    ///
    /// * `var1` - First variable (Var::ZERO means terminal/no variable)
    /// * `var2` - Second variable (Var::ZERO means terminal/no variable)
    ///
    /// # Returns
    ///
    /// The variable that comes first in the ordering, or Var::ZERO if both are terminals.
    fn top_variable(&self, var1: Var, var2: Var) -> Var {
        if var1.is_terminal() {
            return var2;
        }
        if var2.is_terminal() {
            return var1;
        }

        // Compare by level in the explicit ordering
        let level1 = self.get_level(var1);
        let level2 = self.get_level(var2);

        match (level1, level2) {
            (Some(l1), Some(l2)) => {
                if l1 <= l2 {
                    var1
                } else {
                    var2
                }
            }
            (Some(_), None) => var1,
            (None, Some(_)) => var2,
            (None, None) => {
                // Neither variable is in the ordering, fall back to ID comparison
                if var1.id() <= var2.id() {
                    var1
                } else {
                    var2
                }
            }
        }
    }
}

// ============================================================================
// Variable ordering
// ============================================================================

impl Bdd {
    /// Returns the current variable ordering as a vector.
    ///
    /// The i-th element is the variable at level i. Level 0 is the root level.
    pub fn get_variable_order(&self) -> Vec<Var> {
        self.var_order().clone()
    }

    /// Returns the variable at a given level, if it exists.
    pub fn get_variable_at_level(&self, level: Level) -> Option<Var> {
        self.var_order().get(level.index()).copied()
    }

    /// Returns the level of a variable in the current ordering.
    ///
    /// Returns `None` if the variable has not been registered.
    pub fn get_level(&self, var: Var) -> Option<Level> {
        self.level_map().get(&var).copied()
    }

    /// Returns all node indices at a specific level.
    ///
    /// This is primarily used internally for variable reordering.
    pub fn get_nodes_at_level(&self, level: Level) -> Vec<u32> {
        let nodes = self.nodes();
        self.subtables()
            .get(level.index())
            .map(|st| st.indices(&nodes).collect())
            .unwrap_or_default()
    }

    /// Returns the number of levels (registered variables) in the ordering.
    pub fn num_levels(&self) -> usize {
        self.var_order().len()
    }
}

// ============================================================================
// Node constructors (mk_*)
// ============================================================================

impl Bdd {
    /// Returns the constant false BDD.
    ///
    /// This is a convenience method equivalent to accessing `bdd.zero` directly.
    ///
    /// # Examples
    ///
    /// ```
    /// use bdd_rs::bdd::Bdd;
    ///
    /// let bdd = Bdd::default();
    /// let f = bdd.mk_false();
    /// assert!(bdd.is_zero(f));
    /// assert_eq!(f, bdd.zero);
    /// ```
    pub fn mk_false(&self) -> Ref {
        self.zero
    }

    /// Returns the constant true BDD.
    ///
    /// This is a convenience method equivalent to accessing `bdd.one` directly.
    ///
    /// # Examples
    ///
    /// ```
    /// use bdd_rs::bdd::Bdd;
    ///
    /// let bdd = Bdd::default();
    /// let t = bdd.mk_true();
    /// assert!(bdd.is_one(t));
    /// assert_eq!(t, bdd.one);
    /// ```
    pub fn mk_true(&self) -> Ref {
        self.one
    }

    /// Creates or retrieves a BDD node with the given variable and children.
    ///
    /// This is the fundamental node constructor that enforces all BDD invariants:
    /// - **Canonicity**: High edge is never complemented (negates entire node if needed)
    /// - **Reduction**: If low == high, returns the child directly (no redundant node)
    /// - **Uniqueness**: Uses hash consing to return existing identical nodes
    ///
    /// # Arguments
    ///
    /// * `v` - The decision variable (must not be terminal)
    /// * `low` - Child followed when `v` is false
    /// * `high` - Child followed when `v` is true
    ///
    /// # Returns
    ///
    /// A reference to the (possibly existing) node. May be negated if canonicity
    /// required flipping the node.
    ///
    /// # Panics
    ///
    /// Panics if `v` is the terminal variable (`Var::ZERO`).
    ///
    /// # Invariants Enforced
    ///
    /// 1. High edge is always positive (complement only on low edge)
    /// 2. Redundant nodes eliminated (low == high → return child)
    /// 3. Identical nodes shared (hash consing)
    pub fn mk_node(&self, v: Var, low: Ref, high: Ref) -> Ref {
        // debug!("mk(v = {}, low = {}, high = {})", v, low, high);

        assert!(!v.is_terminal(), "Variable must not be Var::ZERO");

        // Handle canonicity
        if high.is_negated() {
            // debug!("mk: restoring canonicity");
            return -self.mk_node(v, -low, -high);
        }

        // Handle duplicates
        if low == high {
            // debug!("mk: duplicates {} == {}", low, high);
            return low;
        }

        // Auto-register the variable if needed
        self.register_variable(v.id());

        // Get the level for this variable (guaranteed to exist now)
        let level = self.get_level(v).expect("Variable should be registered");

        // Check if node exists in subtable (needs read access to nodes for chain traversal)
        {
            let nodes = self.nodes();
            let subtables = self.subtables();
            if let Some(index) = subtables[level.index()].find(low, high, &nodes) {
                return Ref::positive(index);
            }
        }

        // Node doesn't exist - allocate and insert
        let node = Node::new(v, low, high);
        let index = {
            let mut free_set = self.free_set_mut();
            if let Some(&idx) = free_set.iter().next() {
                // Reuse a freed slot
                free_set.remove(&idx);
                self.nodes_mut()[idx as usize] = node;
                idx
            } else {
                // Allocate new slot
                let mut nodes = self.nodes_mut();
                let idx = nodes.len() as u32;
                nodes.push(node);
                idx
            }
        };

        // Insert into subtable (needs mutable access to nodes for setting next pointer)
        {
            let mut nodes = self.nodes_mut();
            self.subtables_mut()[level.index()].insert(low, high, index, &mut nodes);
        }

        Ref::positive(index)
    }

    /// Creates a BDD representing a single Boolean variable.
    ///
    /// Returns a BDD that is true when the variable is true and false otherwise.
    /// This is the primary way to introduce variables into BDD expressions.
    ///
    /// # Arguments
    ///
    /// * `v` - Variable (must not be terminal). Can be a `Var` or `u32`.
    ///
    /// # Panics
    ///
    /// Panics if `v` is the terminal variable (`Var::ZERO`) or if passing `0u32`.
    ///
    /// # Examples
    ///
    /// ```
    /// use bdd_rs::bdd::Bdd;
    /// use bdd_rs::types::Var;
    ///
    /// let bdd = Bdd::default();
    ///
    /// // Using raw integers (backward compatible)
    /// let x1 = bdd.mk_var(1);
    /// let x2 = bdd.mk_var(2);
    ///
    /// // Using Var type
    /// let x3 = bdd.mk_var(Var::new(3));
    ///
    /// // Using allocate_variable
    /// let x4 = bdd.allocate_variable();
    /// let bdd_x4 = bdd.mk_var(x4);
    ///
    /// // Variables can be negated
    /// let not_x1 = -x1;
    ///
    /// // And combined with operations
    /// let f = bdd.apply_and(x1, x2);
    /// ```
    pub fn mk_var(&self, v: impl Into<Var>) -> Ref {
        let v = v.into();
        assert!(!v.is_terminal(), "Variable must not be terminal");

        // Register variable in ordering
        self.register_variable(v.id());

        self.mk_node(v, self.zero, self.one)
    }

    /// Creates a BDD representing a conjunction (AND) of literals.
    ///
    /// A cube is a conjunction of positive or negative literals.
    /// This is more efficient than manually creating multiple AND operations.
    ///
    /// # Arguments
    ///
    /// * `literals` - Iterator of literals. Each literal can be:
    ///   - A `Lit` (type-safe literal)
    ///   - An `i32` (DIMACS-style: positive = positive literal, negative = negated)
    ///
    /// # Returns
    ///
    /// A BDD representing the conjunction of all literals.
    ///
    /// # Examples
    ///
    /// ```
    /// use bdd_rs::bdd::Bdd;
    /// use bdd_rs::types::{Var, Lit};
    ///
    /// let bdd = Bdd::default();
    ///
    /// // Using i32 (DIMACS-style, backward compatible)
    /// let cube1 = bdd.mk_cube([1, -2, 3]);
    ///
    /// // Using Lit (type-safe) - produces identical result
    /// let x1 = Var::new(1);
    /// let x2 = Var::new(2);
    /// let x3 = Var::new(3);
    /// let cube2 = bdd.mk_cube([x1.pos(), x2.neg(), x3.pos()]);
    ///
    /// assert_eq!(cube1, cube2);
    /// ```
    pub fn mk_cube(&self, literals: impl IntoIterator<Item = impl Into<Lit>>) -> Ref {
        let mut literals: Vec<Lit> = literals.into_iter().map(|l| l.into()).collect();
        // Sort by variable ID to ensure consistent ordering
        literals.sort_by_key(|lit| lit.var().id());
        debug!("cube(literals = {:?})", literals);

        // Register all variables in sorted order BEFORE reversing
        // This ensures variables get the correct levels (lower ID = lower level = closer to root)
        for lit in &literals {
            self.register_variable(lit.var().id());
        }

        // Now reverse and build bottom-up
        literals.reverse();
        let mut current = self.one;
        for lit in literals {
            let var = lit.var();
            current = if lit.is_negative() {
                self.mk_node(var, current, self.zero)
            } else {
                self.mk_node(var, self.zero, current)
            };
        }
        current
    }

    /// Creates a BDD representing a disjunction (OR) of literals.
    ///
    /// A clause is a disjunction of positive or negative literals.
    /// This is more efficient than manually creating multiple OR operations.
    ///
    /// # Arguments
    ///
    /// * `literals` - Iterator of literals. Each literal can be:
    ///   - A `Lit` (type-safe literal)
    ///   - An `i32` (DIMACS-style: positive = positive literal, negative = negated)
    ///
    /// # Returns
    ///
    /// A BDD representing the disjunction of all literals.
    ///
    /// # Examples
    ///
    /// ```
    /// use bdd_rs::bdd::Bdd;
    /// use bdd_rs::types::{Var, Lit};
    ///
    /// let bdd = Bdd::default();
    ///
    /// // Using i32 (DIMACS-style, backward compatible)
    /// let clause1 = bdd.mk_clause([1, -2, 3]);
    ///
    /// // Using Lit (type-safe)
    /// let x1 = Var::new(1);
    /// let x2 = Var::new(2);
    /// let x3 = Var::new(3);
    /// let clause2 = bdd.mk_clause([x1.pos(), x2.neg(), x3.pos()]);
    ///
    /// assert_eq!(clause1, clause2);
    /// ```
    pub fn mk_clause(&self, literals: impl IntoIterator<Item = impl Into<Lit>>) -> Ref {
        let mut literals: Vec<Lit> = literals.into_iter().map(|l| l.into()).collect();
        // Sort by variable ID to ensure consistent ordering
        literals.sort_by_key(|lit| lit.var().id());
        debug!("clause(literals = {:?})", literals);

        // Register all variables in sorted order BEFORE reversing
        // This ensures variables get the correct levels (lower ID = lower level = closer to root)
        for lit in &literals {
            self.register_variable(lit.var().id());
        }

        // Now reverse and build bottom-up
        literals.reverse();
        let mut current = self.zero;
        for lit in literals {
            let var = lit.var();
            current = if lit.is_negative() {
                self.mk_node(var, self.one, current)
            } else {
                self.mk_node(var, current, self.one)
            };
        }
        current
    }
}

// ============================================================================
// Boolean operations
// ============================================================================

impl Bdd {
    /// Returns the top cofactors (Shannon expansion) with respect to a variable.
    ///
    /// For a BDD `f` and variable `v`, returns `(f₀, f₁)` where:
    /// - `f₀` is the negative cofactor (`f` with `v = false`)
    /// - `f₁` is the positive cofactor (`f` with `v = true`)
    ///
    /// This corresponds to the Shannon expansion: `f = (¬v ∧ f₀) ∨ (v ∧ f₁)`
    ///
    /// # Parameters
    ///
    /// * `node_ref` - The BDD to compute cofactors for
    /// * `v` - Variable index (must be non-zero and ≤ top variable of `node_ref`)
    ///
    /// # Returns
    ///
    /// A tuple `(f₀, f₁)` of the negative and positive cofactors.
    ///
    /// # Examples
    ///
    /// ```
    /// use bdd_rs::bdd::Bdd;
    /// use bdd_rs::types::Var;
    ///
    /// let bdd = Bdd::default();
    /// let x = bdd.mk_var(1);
    /// let y = bdd.mk_var(2);
    ///
    /// // f = x AND y
    /// let f = bdd.apply_and(x, y);
    ///
    /// // Cofactors with respect to x
    /// let (f0, f1) = bdd.top_cofactors(f, Var::new(1));
    /// assert_eq!(f0, bdd.zero);  // x=false: false AND y = false
    /// assert_eq!(f1, y);         // x=true: true AND y = y
    /// ```
    pub fn top_cofactors(&self, node_ref: Ref, v: Var) -> (Ref, Ref) {
        assert!(!v.is_terminal(), "Variable must not be Var::ZERO");

        if self.is_terminal(node_ref) {
            return (node_ref, node_ref);
        }

        let index = node_ref.index();
        let node = self.node(index);

        // Check if v comes before node.variable in the ordering
        if self.var_precedes(v, node.variable) {
            // 'node' does not depend on 'v' (v is at a higher level, not in this subtree)
            return (node_ref, node_ref);
        }
        assert_eq!(v, node.variable);
        if node_ref.is_negated() {
            (-node.low, -node.high)
        } else {
            (node.low, node.high)
        }
    }

    /// Apply the ITE operation to the arguments.
    ///
    /// ```text
    /// ITE(x, y, z) == (x ∧ y) ∨ (¬x ∧ z) == (x -> y) ∧ (¬x -> z)
    /// ```
    ///
    /// # Examples
    ///
    /// ```
    /// use bdd_rs::bdd::Bdd;
    ///
    /// let bdd = Bdd::default();
    /// let x = bdd.mk_var(1);
    /// let y = bdd.mk_var(2);
    /// let z = bdd.mk_var(3);
    /// let f = bdd.apply_ite(x, y, z);
    /// assert_eq!(f, bdd.mk_node(bdd.variable(x.index()), z, y));
    /// let  x_and_y = bdd.apply_and(x, y);
    /// let  not_x_and_z = bdd.apply_and(-x, z);
    /// assert_eq!(f, bdd.apply_or(x_and_y, not_x_and_z));
    /// ```
    pub fn apply_ite(&self, f: Ref, g: Ref, h: Ref) -> Ref {
        debug!("apply_ite(f = {}, g = {}, h = {})", f, g, h);

        // Base cases:
        //   ite(1,G,H) => G
        //   ite(0,G,H) => H
        if self.is_one(f) {
            debug!("ite(1,G,H) => G");
            return g;
        }
        if self.is_zero(f) {
            debug!("ite(0,G,H) => H");
            return h;
        }

        // From now on, F is known not to be a constant
        assert!(!self.is_terminal(f));

        // More base cases:
        //   ite(F,G,G) => G
        //   ite(F,1,0) => F
        //   ite(F,0,1) => ~F
        //   ite(F,1,~F) => 1
        //   ite(F,F,1) => 1
        //   ite(F,~F,0) => 0
        //   ite(F,0,F) => F
        if g == h {
            debug!("ite(F,G,G) => G");
            return g;
        }
        if self.is_one(g) && self.is_zero(h) {
            debug!("ite(F,1,0) => F");
            return f;
        }
        if self.is_zero(g) && self.is_one(h) {
            debug!("ite(F,0,1) => ~F");
            return -f;
        }
        if self.is_one(g) && h == -f {
            debug!("ite(F,1,~F) => 1");
            return self.one;
        }
        if g == f && self.is_one(h) {
            debug!("ite(F,F,1) => 1");
            return self.one;
        }
        if g == -f && self.is_zero(h) {
            debug!("ite(F,~F,0) => 0");
            return self.zero;
        }
        if self.is_zero(g) && h == f {
            debug!("ite(F,0,F) => F");
            return f;
        }

        // Standard triples:
        //   ite(F,F,H) => ite(F,1,H)
        //   ite(F,G,F) => ite(F,G,0)
        //   ite(F,~F,H) => ite(F,0,H)
        //   ite(F,G,~F) => ite(F,G,1)
        if g == f {
            debug!("ite(F,F,H) => ite(F,1,H)");
            return self.apply_ite(f, self.one, h);
        }
        if h == f {
            debug!("ite(F,G,F) => ite(F,G,0)");
            return self.apply_ite(f, g, self.zero);
        }
        if g == -f {
            debug!("ite(F,~F,H) => ite(F,0,H)");
            return self.apply_ite(f, self.zero, h);
        }
        if h == -f {
            debug!("ite(F,G,~F) => ite(F,G,1)");
            return self.apply_ite(f, g, self.one);
        }

        let i = self.variable(f.index());
        let j = self.variable(g.index());
        let k = self.variable(h.index());
        assert!(!i.is_terminal());

        // Equivalent pairs:
        //   ite(F,1,H) == ite(H,1,F) == F ∨ H
        //   ite(F,G,0) == ite(G,F,0) == F ∧ G
        //   ite(F,G,1) == ite(~G,~F,1) == F -> G
        //   ite(F,0,H) == ite(~H,0,~F) == ~F ∧ H
        //   ite(F,G,~G) == ite(G,F,~F)
        // (choose the one with the lowest variable)
        if self.is_one(g) && self.var_precedes(k, i) {
            assert!(!k.is_terminal());
            debug!("ite(F,1,H) => ite(H,1,F)");
            return self.apply_ite(h, self.one, f);
        }
        if self.is_zero(h) && self.var_precedes(j, i) {
            assert!(!j.is_terminal());
            debug!("ite(F,G,0) => ite(G,F,0)");
            return self.apply_ite(g, f, self.zero);
        }
        if self.is_one(h) && self.var_precedes(j, i) {
            assert!(!j.is_terminal());
            debug!("ite(F,G,1) => ite(~G,~F,1)");
            return self.apply_ite(-g, -f, self.one);
        }
        if self.is_zero(g) && self.var_precedes(k, i) {
            assert!(!k.is_terminal());
            debug!("ite(F,0,H) => ite(~H,0,~F)");
            return self.apply_ite(-h, self.zero, -f);
        }
        if g == -h && self.var_precedes(j, i) {
            assert!(!j.is_terminal());
            debug!("ite(F,G,~G) => ite(G,F,~F)");
            return self.apply_ite(g, f, -f);
        }

        // Make sure the first two pointers (f and g) are regular (not negated)
        let (mut f, mut g, mut h) = (f, g, h);

        // ite(~F,G,H) => ite(F,H,G)
        if f.is_negated() {
            debug!("ite(~F,G,H) => ite(F,H,G)");
            f = -f;
            std::mem::swap(&mut g, &mut h);
        }
        assert!(!f.is_negated());

        // ite(F,~G,H) => ~ite(F,G,~H)
        let mut n = false;
        if g.is_negated() {
            n = true;
            g = -g;
            h = -h;
        }
        assert!(!g.is_negated());

        let (f, g, h) = (f, g, h); // make immutable

        let key = OpKey::Ite(f, g, h);
        debug!("key = {:?}", key);
        if let Some(&res) = self.cache().get(&key) {
            debug!("cache: apply_ite(f = {}, g = {}, h = {}) -> {}", f, g, h, res);
            return if n { -res } else { res };
        }

        // Determine the top variable:
        let mut m = i;
        if !j.is_terminal() {
            m = self.top_variable(m, j);
        }
        if !k.is_terminal() {
            m = self.top_variable(m, k);
        }
        debug!("top variable = {}", m);
        assert!(!m.is_terminal());

        let (f0, f1) = self.top_cofactors(f, m);
        debug!("cofactors of f = {} are: f0 = {}, f1 = {}", f, f0, f1);
        let (g0, g1) = self.top_cofactors(g, m);
        debug!("cofactors of g = {} are: g0 = {}, g1 = {}", g, g0, g1);
        let (h0, h1) = self.top_cofactors(h, m);
        debug!("cofactors of h = {} are: h0 = {}, h1 = {}", h, h0, h1);

        let e = self.apply_ite(f0, g0, h0);
        let t = self.apply_ite(f1, g1, h1);
        debug!("cofactors of res: e = {}, t = {}", e, t);

        let res = self.mk_node(m, e, t);
        debug!("computed: apply_ite(f = {}, g = {}, h = {}) -> {}", f, g, h, res);
        self.cache_mut().insert(key, res);
        if n {
            -res
        } else {
            res
        }
    }

    fn maybe_constant(&self, node_ref: Ref) -> Option<bool> {
        if self.is_zero(node_ref) {
            Some(false)
        } else if self.is_one(node_ref) {
            Some(true)
        } else {
            None
        }
    }

    /// Checks if `ITE(f, g, h)` evaluates to a constant without building the BDD.
    ///
    /// Returns:
    /// - `Some(true)` if the result is always true (ONE)
    /// - `Some(false)` if the result is always false (ZERO)
    /// - `None` if the result depends on variable assignments
    ///
    /// This is useful for implication checking and other queries where we only
    /// care if the result is constant, not the full BDD structure.
    pub fn ite_constant(&self, f: Ref, g: Ref, h: Ref) -> Option<bool> {
        debug!("ite_constant(f = {}, g = {}, h = {})", f, g, h);

        // TODO: "trivial" cases

        // Base cases:
        //   ite(1,G,H) => G
        //   ite(0,G,H) => H
        if self.is_one(f) {
            debug!("ite(1,G,H) => G");
            // return g;
            return self.maybe_constant(g);
        }
        if self.is_zero(f) {
            debug!("ite(0,G,H) => H");
            // return h;
            return self.maybe_constant(h);
        }

        // From now on, F is known not to be a constant
        assert!(!self.is_terminal(f));

        // More base cases:
        //   ite(F,G,G) => G
        //   ite(F,1,0) => F
        //   ite(F,0,1) => ~F
        //   ite(F,1,~F) => 1
        //   ite(F,F,1) => 1
        //   ite(F,~F,0) => 0
        //   ite(F,0,F) => F
        if g == h {
            debug!("ite(F,G,G) => G");
            // return g;
            return self.maybe_constant(g);
        }
        if self.is_one(g) && self.is_zero(h) {
            debug!("ite(F,1,0) => F");
            // return f;
            return None;
        }
        if self.is_zero(g) && self.is_one(h) {
            debug!("ite(F,0,1) => ~F");
            // return -f;
            return None;
        }
        if self.is_one(g) && h == -f {
            debug!("ite(F,1,~F) => 1");
            // return self.one;
            return Some(true);
        }
        if g == f && self.is_one(h) {
            debug!("ite(F,F,1) => 1");
            // return self.one;
            return Some(true);
        }
        if g == -f && self.is_zero(h) {
            debug!("ite(F,~F,0) => 0");
            // return self.zero;
            return Some(false);
        }
        if self.is_zero(g) && h == f {
            debug!("ite(F,0,F) => F");
            // return f;
            return None;
        }

        // TODO: standard triples?

        let key = OpKey::Ite(f, g, h);
        if let Some(&res) = self.cache().get(&key) {
            debug!("cache: ite_constant(f = {}, g = {}, h = {}) -> {}", f, g, h, res);
            assert!(!self.is_terminal(res));
            return None;
        }

        let i = self.variable(f.index());
        let j = self.variable(g.index());
        let k = self.variable(h.index());
        assert!(!i.is_terminal());

        // Determine the top variable:
        let mut m = i;
        if !j.is_terminal() {
            m = self.top_variable(m, j);
        }
        if !k.is_terminal() {
            m = self.top_variable(m, k);
        }
        debug!("top variable = {}", m);
        assert!(!m.is_terminal());

        let (f0, f1) = self.top_cofactors(f, m);
        debug!("cofactors of f = {} are: f0 = {}, f1 = {}", f, f0, f1);
        let (g0, g1) = self.top_cofactors(g, m);
        debug!("cofactors of g = {} are: g0 = {}, g1 = {}", g, g0, g1);
        let (h0, h1) = self.top_cofactors(h, m);
        debug!("cofactors of h = {} are: h0 = {}, h1 = {}", h, h0, h1);

        let t = self.ite_constant(f1, g1, h1);
        if t.is_none() {
            return None;
        }
        let e = self.ite_constant(f0, g0, h0);
        if e != Some(true) {
            return None;
        }
        t
    }

    /// Checks if `f` logically implies `g` (i.e., `f → g` is a tautology).
    ///
    /// Returns `true` if for all assignments where `f` is true, `g` is also true.
    /// Equivalent to checking if `f ∧ ¬g` is unsatisfiable.
    ///
    /// This is more efficient than building the implication BDD and checking if it's ONE,
    /// as it can short-circuit when the result is determined.
    pub fn is_implies(&self, f: Ref, g: Ref) -> bool {
        debug!("is_implies(f = {}, g = {})", f, g);
        self.ite_constant(f, g, self.one) == Some(true)
    }

    /// Returns the negation of a BDD in O(1) time.
    ///
    /// Complement edges make negation trivial: just flip the complement bit.
    /// No new nodes are created.
    ///
    /// # Examples
    ///
    /// ```
    /// use bdd_rs::bdd::Bdd;
    ///
    /// let bdd = Bdd::default();
    /// let x = bdd.mk_var(1);
    /// let not_x = bdd.apply_not(x);
    ///
    /// // Equivalent to unary negation
    /// assert_eq!(not_x, -x);
    ///
    /// // Double negation
    /// assert_eq!(bdd.apply_not(not_x), x);
    /// ```
    pub fn apply_not(&self, f: Ref) -> Ref {
        debug!("apply_not(f = {})", f);
        -f
    }

    /// Computes the conjunction (AND) of two BDDs: `u ∧ v`.
    ///
    /// Implemented using [`apply_ite`](Bdd::apply_ite).
    ///
    /// # Examples
    ///
    /// ```
    /// use bdd_rs::bdd::Bdd;
    ///
    /// let bdd = Bdd::default();
    /// let x = bdd.mk_var(1);
    /// let y = bdd.mk_var(2);
    ///
    /// let and = bdd.apply_and(x, y);
    ///
    /// // AND is commutative
    /// assert_eq!(bdd.apply_and(x, y), bdd.apply_and(y, x));
    ///
    /// // AND with constants
    /// assert_eq!(bdd.apply_and(x, bdd.one), x);
    /// assert!(bdd.is_zero(bdd.apply_and(x, bdd.zero)));
    /// ```
    pub fn apply_and(&self, u: Ref, v: Ref) -> Ref {
        debug!("apply_and(u = {}, v = {})", u, v);
        self.apply_ite(u, v, self.zero)
    }

    /// Computes the disjunction (OR) of two BDDs: `u ∨ v`.
    ///
    /// Implemented using [`apply_ite`](Bdd::apply_ite).
    ///
    /// # Examples
    ///
    /// ```
    /// use bdd_rs::bdd::Bdd;
    ///
    /// let bdd = Bdd::default();
    /// let x = bdd.mk_var(1);
    /// let y = bdd.mk_var(2);
    ///
    /// let or = bdd.apply_or(x, y);
    ///
    /// // OR is commutative
    /// assert_eq!(bdd.apply_or(x, y), bdd.apply_or(y, x));
    ///
    /// // OR with constants
    /// assert_eq!(bdd.apply_or(x, bdd.zero), x);
    /// assert!(bdd.is_one(bdd.apply_or(x, bdd.one)));
    /// ```
    pub fn apply_or(&self, u: Ref, v: Ref) -> Ref {
        debug!("apply_or(u = {}, v = {})", u, v);
        self.apply_ite(u, self.one, v)
    }

    /// Computes the exclusive OR (XOR) of two BDDs: `u ⊕ v`.
    ///
    /// True when exactly one operand is true.
    ///
    /// Implemented using [`apply_ite`](Bdd::apply_ite).
    ///
    /// # Examples
    ///
    /// ```
    /// use bdd_rs::bdd::Bdd;
    ///
    /// let bdd = Bdd::default();
    /// let x = bdd.mk_var(1);
    /// let y = bdd.mk_var(2);
    ///
    /// let xor = bdd.apply_xor(x, y);
    ///
    /// // XOR is commutative
    /// assert_eq!(bdd.apply_xor(x, y), bdd.apply_xor(y, x));
    ///
    /// // XOR with itself is false
    /// assert!(bdd.is_zero(bdd.apply_xor(x, x)));
    ///
    /// // XOR is equivalent to inequality
    /// let neq = bdd.apply_and(bdd.apply_or(x, y), bdd.apply_not(bdd.apply_and(x, y)));
    /// assert_eq!(xor, neq);
    /// ```
    pub fn apply_xor(&self, u: Ref, v: Ref) -> Ref {
        debug!("apply_xor(u = {}, v = {})", u, v);
        self.apply_ite(u, -v, v)
    }

    /// Computes the equivalence (XNOR) of two BDDs: `u <=> v`.
    ///
    /// True when both operands have the same value.
    ///
    /// Implemented using [`apply_ite`](Bdd::apply_ite).
    ///
    /// # Examples
    ///
    /// ```
    /// use bdd_rs::bdd::Bdd;
    ///
    /// let bdd = Bdd::default();
    /// let x = bdd.mk_var(1);
    /// let y = bdd.mk_var(2);
    ///
    /// let eq = bdd.apply_eq(x, y);
    ///
    /// // Equivalence with itself is true
    /// assert!(bdd.is_one(bdd.apply_eq(x, x)));
    ///
    /// // Equivalence is the negation of XOR
    /// assert_eq!(eq, bdd.apply_not(bdd.apply_xor(x, y)));
    /// ```
    pub fn apply_eq(&self, u: Ref, v: Ref) -> Ref {
        debug!("apply_eq(u = {}, v = {})", u, v);
        self.apply_ite(u, v, -v)
    }

    /// Computes the implication of two BDDs: `u -> v`.
    ///
    /// Equivalent to `¬u ∨ v`.
    ///
    /// Implemented using [`apply_ite`](Bdd::apply_ite).
    ///
    /// # Examples
    ///
    /// ```
    /// use bdd_rs::bdd::Bdd;
    ///
    /// let bdd = Bdd::default();
    /// let x = bdd.mk_var(1);
    /// let y = bdd.mk_var(2);
    ///
    /// let implies = bdd.apply_imply(x, y);
    ///
    /// // x implies x is always true
    /// assert!(bdd.is_one(bdd.apply_imply(x, x)));
    ///
    /// // Equivalent to NOT x OR y
    /// let equivalent = bdd.apply_or(-x, y);
    /// assert_eq!(implies, equivalent);
    /// ```
    pub fn apply_imply(&self, u: Ref, v: Ref) -> Ref {
        debug!("apply_imply(u = {}, v = {})", u, v);
        self.apply_ite(u, v, self.one)
    }

    /// Computes the conjunction (AND) of multiple BDDs.
    ///
    /// More convenient than chaining multiple [`apply_and`](Bdd::apply_and) calls.
    ///
    /// # Examples
    ///
    /// ```
    /// use bdd_rs::bdd::Bdd;
    ///
    /// let bdd = Bdd::default();
    /// let x = bdd.mk_var(1);
    /// let y = bdd.mk_var(2);
    /// let z = bdd.mk_var(3);
    ///
    /// // AND of multiple variables
    /// let and_all = bdd.apply_and_many([x, y, z]);
    ///
    /// // Equivalent to:
    /// let manual = bdd.apply_and(bdd.apply_and(x, y), z);
    /// assert_eq!(and_all, manual);
    ///
    /// // Also equivalent to cube
    /// assert_eq!(and_all, bdd.mk_cube([1, 2, 3]));
    /// ```
    pub fn apply_and_many(&self, nodes: impl IntoIterator<Item = Ref>) -> Ref {
        debug!("apply_and_many(...)");
        let mut res = self.one;
        for node_ref in nodes.into_iter() {
            res = self.apply_and(res, node_ref);
        }
        res
    }

    /// Computes the disjunction (OR) of multiple BDDs.
    ///
    /// More convenient than chaining multiple [`apply_or`](Bdd::apply_or) calls.
    ///
    /// # Examples
    ///
    /// ```
    /// use bdd_rs::bdd::Bdd;
    ///
    /// let bdd = Bdd::default();
    /// let x = bdd.mk_var(1);
    /// let y = bdd.mk_var(2);
    /// let z = bdd.mk_var(3);
    ///
    /// // OR of multiple variables
    /// let or_all = bdd.apply_or_many([x, y, z]);
    ///
    /// // Equivalent to:
    /// let manual = bdd.apply_or(bdd.apply_or(x, y), z);
    /// assert_eq!(or_all, manual);
    ///
    /// // Also equivalent to clause
    /// assert_eq!(or_all, bdd.mk_clause([1, 2, 3]));
    /// ```
    pub fn apply_or_many(&self, nodes: impl IntoIterator<Item = Ref>) -> Ref {
        debug!("apply_or_many(...)");
        let mut res = self.zero;
        for node_ref in nodes.into_iter() {
            res = self.apply_or(res, node_ref);
        }
        res
    }
}

// ============================================================================
// Substitution and composition
// ============================================================================

impl Bdd {
    /// Substitutes a variable with a Boolean constant.
    ///
    /// Returns a new BDD where all occurrences of variable `v` are replaced with
    /// the constant `b`. This is also called the cofactor operation.
    ///
    /// # Arguments
    ///
    /// * `f` - The BDD to substitute in
    /// * `v` - Variable index to substitute (must be non-zero)
    /// * `b` - Boolean value to substitute (true or false)
    ///
    /// # Examples
    ///
    /// ```
    /// use bdd_rs::bdd::Bdd;
    /// use bdd_rs::types::Var;
    ///
    /// let bdd = Bdd::default();
    /// let x = bdd.mk_var(1);
    /// let y = bdd.mk_var(2);
    ///
    /// // f = (x = y) ∨ x
    /// let f = bdd.apply_or(bdd.apply_eq(x, y), x);
    ///
    /// // Substitute x with true (using raw integer)
    /// // f[x<-1] = (1 = y) ∨ 1  ==>  1
    /// let f_x_true = bdd.substitute(f, 1, true);
    /// assert!(bdd.is_one(f_x_true)); // Result is always true
    ///
    /// // Substitute y with false (using Var)
    /// // f[y<-0] = (x = 0) ∨ x  ==>  1
    /// let f_y_false = bdd.substitute(f, Var::new(2), false);
    /// assert!(bdd.is_one(f_y_false)); // Result is always true
    /// ```
    // f|v<-b
    pub fn substitute(&self, f: Ref, v: impl Into<Var>, b: bool) -> Ref {
        let v = v.into();
        let mut cache = HashMap::new();
        self.substitute_(f, v, b, &mut cache)
    }

    fn substitute_(&self, f: Ref, v: Var, b: bool, cache: &mut HashMap<Ref, Ref>) -> Ref {
        assert!(!v.is_terminal(), "Variable must not be terminal");

        if self.is_terminal(f) {
            return f;
        }

        let i = self.variable(f.index());

        if self.var_precedes(v, i) {
            // 'v' comes before 'i' in ordering, so 'f' does not depend on 'v'
            return f;
        }

        if v == i {
            // Note: here, we do not need to wrap it with restrict(...).
            return if b { self.high_node(f) } else { self.low_node(f) };
        }

        if let Some(&res) = cache.get(&f) {
            return res;
        }

        assert!(self.var_precedes(i, v));
        let low = self.substitute_(self.low_node(f), v, b, cache);
        let high = self.substitute_(self.high_node(f), v, b, cache);
        let res = self.mk_node(i, low, high);
        cache.insert(f, res);
        res
    }

    /// Substitutes multiple variables with boolean values simultaneously.
    ///
    /// This is equivalent to applying [`substitute`](Bdd::substitute) multiple times,
    /// but more efficient as it performs all substitutions in a single traversal.
    ///
    /// # Parameters
    ///
    /// * `f` - The BDD to substitute variables in
    /// * `values` - A map from variable indices to their boolean values
    ///
    /// # Examples
    ///
    /// ```
    /// use bdd_rs::bdd::Bdd;
    /// use bdd_rs::types::Var;
    /// use std::collections::HashMap;
    ///
    /// let bdd = Bdd::default();
    /// let x = bdd.mk_var(1);
    /// let y = bdd.mk_var(2);
    /// let f = bdd.apply_and(x, y);
    ///
    /// let mut values = HashMap::new();
    /// values.insert(Var::new(1), true);  // x = true
    /// values.insert(Var::new(2), false); // y = false
    ///
    /// let result = bdd.substitute_multi(f, &values);
    /// assert_eq!(result, bdd.zero); // true AND false = false
    /// ```
    pub fn substitute_multi(&self, f: Ref, values: &HashMap<Var, bool>) -> Ref {
        let mut cache = HashMap::new();
        self.substitute_multi_(f, values, &mut cache)
    }

    fn substitute_multi_(&self, f: Ref, values: &HashMap<Var, bool>, cache: &mut HashMap<Ref, Ref>) -> Ref {
        debug!("restrict_multi(f = {}, values = {:?})", f, values);

        if self.is_terminal(f) {
            return f;
        }

        if values.is_empty() {
            return f;
        }

        if let Some(&res) = cache.get(&f) {
            return res;
        }

        let i = self.variable(f.index());
        let res = if let Some(&b) = values.get(&i) {
            if b {
                // `i` needs to be assigned true
                self.substitute_multi_(self.high_node(f), values, cache)
            } else {
                // `i` needs to be assigned false
                self.substitute_multi_(self.low_node(f), values, cache)
            }
        } else {
            // `i` does not need to be assigned
            let low = self.substitute_multi_(self.low_node(f), values, cache);
            let high = self.substitute_multi_(self.high_node(f), values, cache);
            self.mk_node(i, low, high)
        };
        cache.insert(f, res);
        res
    }

    /// Computes the cofactor of a BDD with respect to a cube.
    ///
    /// A cube is a conjunction of literals. This operation substitutes each
    /// variable in the cube with its corresponding value (positive = true, negative = false).
    ///
    /// # Parameters
    ///
    /// * `f` - The BDD to cofactor
    /// * `cube` - Literals representing the cube (positive for true, negative for false)
    ///
    /// # Examples
    ///
    /// ```
    /// use bdd_rs::bdd::Bdd;
    /// use bdd_rs::types::{Var, Lit};
    ///
    /// let bdd = Bdd::default();
    /// let x = bdd.mk_var(1);
    /// let y = bdd.mk_var(2);
    /// let f = bdd.apply_or(x, y);
    ///
    /// // Cofactor with respect to x=true, y=false (using DIMACS-style integers)
    /// let result = bdd.cofactor_cube(f, [1, -2]);
    /// assert_eq!(result, bdd.one); // true OR false = true
    ///
    /// // Or using Lit type directly
    /// let result = bdd.cofactor_cube(f, [Var::new(1).pos(), Var::new(2).neg()]);
    /// assert_eq!(result, bdd.one);
    /// ```
    pub fn cofactor_cube(&self, f: Ref, cube: impl IntoIterator<Item = impl Into<Lit>>) -> Ref {
        // Filter out variables not in the ordering and sort by level
        let mut lits: Vec<Lit> = cube
            .into_iter()
            .map(|l| l.into())
            .filter(|lit| self.get_level(lit.var()).is_some())
            .collect();
        lits.sort_by_key(|lit| self.get_level(lit.var()).unwrap().index());
        let mut cache = HashMap::new();
        self.cofactor_cube_(f, &lits, &mut cache)
    }

    fn cofactor_cube_(&self, f: Ref, cube: &[Lit], cache: &mut HashMap<(usize, Ref), Ref>) -> Ref {
        if cube.is_empty() {
            return f;
        }

        if self.is_terminal(f) {
            return f;
        }

        let key = (cube.len(), f);
        if let Some(&res) = cache.get(&key) {
            return res;
        }

        let t = self.variable(f.index()); // top variable of `f`
        let lit = cube[0];
        let u = lit.var();

        // Both t and u must have levels:
        // - t is in the BDD, so it must have a level
        // - u was pre-filtered to only include variables with levels
        let Some(tl) = self.get_level(t) else {
            unreachable!("BDD variable {} must have a level", t);
        };
        let Some(ul) = self.get_level(u) else {
            unreachable!("Cube variable {} must have a level", u);
        };

        let res = match tl.cmp(&ul) {
            Ordering::Greater => {
                // `t` is at a greater (lower) level than `u`, so `f` doesn't depend on `u`
                self.cofactor_cube_(f, &cube[1..], cache)
            }
            Ordering::Equal => {
                // `t == u`: `u` is the top variable of `f`
                let branch = if lit.is_positive() { self.high_node(f) } else { self.low_node(f) };
                self.cofactor_cube_(branch, &cube[1..], cache)
            }
            Ordering::Less => {
                // `t` is at a smaller (higher) level than `u`
                let f0 = self.low_node(f);
                let f1 = self.high_node(f);
                let low = self.cofactor_cube_(f0, cube, cache);
                let high = self.cofactor_cube_(f1, cube, cache);
                self.mk_node(t, low, high)
            }
        };
        cache.insert(key, res);
        res
    }

    /// Composes a BDD by substituting a variable with another BDD: `f|v<-g`.
    ///
    /// Returns a new BDD where all occurrences of variable `v` in `f` are replaced
    /// with the BDD `g`. This is also known as functional composition.
    ///
    /// # Arguments
    ///
    /// * `f` - The BDD to compose
    /// * `v` - Variable to substitute (must not be terminal)
    /// * `g` - BDD to substitute for the variable
    ///
    /// # Examples
    ///
    /// ```
    /// use bdd_rs::bdd::Bdd;
    /// use bdd_rs::types::Var;
    ///
    /// let bdd = Bdd::default();
    /// let x = bdd.mk_var(1);
    /// let y = bdd.mk_var(2);
    /// let z = bdd.mk_var(3);
    ///
    /// // f = x AND z
    /// let f = bdd.apply_and(x, z);
    ///
    /// // Replace x with (y XOR z) - using raw integer
    /// let g = bdd.apply_xor(y, z);
    /// let result = bdd.compose(f, 1, g);
    ///
    /// // Or using Var type
    /// let result = bdd.compose(f, Var::new(1), g);
    ///
    /// // Result is (y XOR z) AND z, which simplifies to (NOT y AND z)
    /// ```
    pub fn compose(&self, f: Ref, v: impl Into<Var>, g: Ref) -> Ref {
        let v = v.into();
        let mut cache = Cache::new(16);
        self.compose_(f, v, g, &mut cache)
    }

    fn compose_(&self, f: Ref, v: Var, g: Ref, cache: &mut Cache<(Ref, Ref), Ref>) -> Ref {
        // TODO: compose(f, v, g) = ITE(g, restrict(f, v, true), restrict(f, v, false))

        debug!("compose(f = {}, v = {}, g = {})", f, v, g);

        if self.is_terminal(f) {
            return f;
        }

        let i = self.variable(f.index());
        assert!(!i.is_terminal());
        if self.var_precedes(v, i) {
            // 'v' comes before 'i' in ordering, so 'f' does not depend on 'v'
            return f;
        }

        let key = (f, g);
        if let Some(&res) = cache.get(&key) {
            return res;
        }

        let res = if v == i {
            let node = self.node(f.index());
            let res = self.apply_ite(g, node.high, node.low);
            if f.is_negated() {
                -res
            } else {
                res
            }
        } else {
            assert!(self.var_precedes(i, v));

            let m = if self.is_terminal(g) {
                i
            } else {
                self.top_variable(i, self.variable(g.index()))
            };
            assert!(!m.is_terminal());

            let (f0, f1) = self.top_cofactors(f, m);
            let (g0, g1) = self.top_cofactors(g, m);
            let h0 = self.compose_(f0, v, g0, cache);
            let h1 = self.compose_(f1, v, g1, cache);

            self.mk_node(m, h0, h1)
        };
        cache.insert(key, res);
        res
    }

    /// Computes the generalized cofactor (constrain operator): `f|g`.
    ///
    /// The constrain operator restricts function `f` to the domain where `g` is true,
    /// simplifying `f` while preserving its behavior on inputs satisfying `g`.
    /// This is also known as the *generalized cofactor* of `f` with respect to `g`.
    ///
    /// # Mathematical Definition
    ///
    /// The constrain operator `f|g` is defined as:
    /// - `f|1 = f` (no restriction)
    /// - `f|0 = 0` (empty domain)
    /// - `f|g` simplifies `f` by assuming `g` is true
    ///
    /// For any assignment where `g = 1`, we have `(f|g) = f`.
    /// For assignments where `g = 0`, the value of `(f|g)` is don't-care.
    ///
    /// # Properties
    ///
    /// - `f|1 = f`
    /// - `f|0 = 0`
    /// - `f|f = 1`
    /// - `f|~f = 0`
    /// - If `f` is a terminal, `f|g = f`
    ///
    /// # Parameters
    ///
    /// * `f` - The function to be constrained
    /// * `g` - The constraint (domain restriction)
    ///
    /// # Returns
    ///
    /// A BDD reference representing `f|g` (f constrained by g).
    ///
    /// # Examples
    ///
    /// ```
    /// use bdd_rs::bdd::Bdd;
    ///
    /// let bdd = Bdd::default();
    ///
    /// // Example 1: Basic properties
    /// let x = bdd.mk_var(1);
    /// let f = bdd.mk_var(2);
    ///
    /// // f|1 = f
    /// assert_eq!(bdd.constrain(f, bdd.one), f);
    ///
    /// // f|0 = 0
    /// assert_eq!(bdd.constrain(f, bdd.zero), bdd.zero);
    ///
    /// // f|f = 1
    /// assert_eq!(bdd.constrain(x, x), bdd.one);
    ///
    /// // Example 2: Simplification
    /// // f = x1*x3 + ~x1*(x2^x3)
    /// // g = x1*x2 + ~x2*~x3
    /// // f|g = x1*x2*x3 (simplified form of f restricted to g's domain)
    /// let x1 = bdd.mk_var(1);
    /// let x2 = bdd.mk_var(2);
    /// let x3 = bdd.mk_var(3);
    ///
    /// let f = bdd.apply_or(
    ///     bdd.apply_and(x1, x3),
    ///     bdd.apply_and(-x1, bdd.apply_xor(x2, x3))
    /// );
    /// let g = bdd.apply_or(
    ///     bdd.apply_and(x1, x2),
    ///     bdd.apply_and(-x2, -x3)
    /// );
    ///
    /// let fg = bdd.constrain(f, g);
    /// let expected = bdd.mk_cube([1, 2, 3]); // x1*x2*x3
    /// assert_eq!(fg, expected);
    /// ```
    pub fn constrain(&self, f: Ref, g: Ref) -> Ref {
        debug!("constrain(f = {}, g = {})", f, g);

        if self.is_zero(g) {
            debug!("g is zero => f|g = 0");
            return self.zero;
        }
        if self.is_one(g) {
            debug!("g is one => f|g = f");
            return f;
        }
        if self.is_terminal(f) {
            debug!("f is terminal => f|g = f");
            return f;
        }
        if f == g {
            debug!("f = g => f|g = 1");
            return self.one;
        }
        if f == -g {
            debug!("f = ~g => f|g = 0");
            return self.zero;
        }

        let key = OpKey::Constrain(f, g);
        if let Some(&res) = self.cache().get(&key) {
            debug!("cache: constrain(f = {}, g = {}) -> {}", f, g, res);
            return res;
        }

        // TODO: is it necessary to compute min var, or we can just use var(g)?
        let i = self.variable(f.index());
        let j = self.variable(g.index());
        let v = self.top_variable(i, j);
        debug!("top variable = {}", v);

        let (f0, f1) = self.top_cofactors(f, v);
        let (g0, g1) = self.top_cofactors(g, v);

        if self.is_zero(g1) {
            debug!("g1 is zero");
            return self.constrain(f0, g0);
        }
        if self.is_zero(g0) {
            debug!("g0 is zero");
            return self.constrain(f1, g1);
        }

        if f0 == f1 {
            debug!("f0 == f1");
            let low = self.constrain(f, g0);
            let high = self.constrain(f, g1);
            return self.mk_node(v, low, high);
        }

        let low = self.constrain(f0, g0);
        let high = self.constrain(f1, g1);
        // TODO: replace 'mk_node' with 'ITE'?
        let res = self.mk_node(v, low, high);
        debug!("computed: constrain(f = {}, g = {}) -> {}", f, g, res);

        self.cache_mut().insert(key, res);
        res
    }

    /// Restricts a BDD by setting variables where the constraint is constant.
    ///
    /// The restrict operator `f↓g` simplifies `f` by setting variables to constants
    /// based on `g`. Unlike [`constrain`](Bdd::constrain), restrict only substitutes
    /// variables that are constant in `g`, making it a partial evaluation.
    ///
    /// # Properties
    ///
    /// - `f↓1 = f`
    /// - `f↓0 = 0`
    /// - `f↓f = 1`
    /// - `f↓~f = 0`
    ///
    /// # Parameters
    ///
    /// * `f` - The function to restrict
    /// * `g` - The constraint defining variable assignments
    ///
    /// # Returns
    ///
    /// A BDD representing `f` restricted by `g`.
    ///
    /// # Examples
    ///
    /// ```
    /// use bdd_rs::bdd::Bdd;
    ///
    /// let bdd = Bdd::default();
    /// let x = bdd.mk_var(1);
    /// let y = bdd.mk_var(2);
    ///
    /// // f = x OR y
    /// let f = bdd.apply_or(x, y);
    ///
    /// // Restrict f by setting x = true
    /// let result = bdd.restrict(f, x);
    /// assert_eq!(result, bdd.one); // (true OR y) = true
    /// ```
    pub fn restrict(&self, f: Ref, g: Ref) -> Ref {
        debug!("restrict(f = {}, g = {})", f, g);

        if self.is_zero(g) {
            log::warn!("g is zero => f|g = 0");
            return self.zero;
        }
        if self.is_one(g) || self.is_terminal(f) {
            return f;
        }
        if f == g {
            return self.one;
        }
        if f == -g {
            return self.zero;
        }

        let key = OpKey::Restrict(f, g);
        if let Some(&res) = self.cache().get(&key) {
            debug!("cache: restrict(f = {}, g = {}) -> {}", f, g, res);
            return res;
        }

        let i = self.variable(f.index());
        let j = self.variable(g.index());
        let v = self.top_variable(i, j);

        let (f0, f1) = self.top_cofactors(f, v);
        let (g0, g1) = self.top_cofactors(g, v);

        if self.is_zero(g1) {
            return self.restrict(f0, g0);
        }
        if self.is_zero(g0) {
            return self.restrict(f1, g1);
        }

        let res = if v == i {
            let low = self.restrict(f0, g0);
            let high = self.restrict(f1, g1);
            self.mk_node(v, low, high)
        } else {
            self.restrict(f, self.apply_ite(g1, self.one, g0))
        };
        self.cache_mut().insert(key, res);
        res
    }
}

// ============================================================================
// Variable renaming
// ============================================================================

impl Bdd {
    /// Renames variables according to an **order-preserving** permutation mapping.
    ///
    /// **IMPORTANT**: This function requires that the permutation preserves the variable
    /// ordering to maintain the OBDD invariant. If `old_var1 < old_var2` and both are
    /// in the permutation, then `new_var1 < new_var2` must hold.
    ///
    /// # Arguments
    ///
    /// * `f` - The BDD to rename variables in
    /// * `permutation` - HashMap mapping old variables to new ones.
    ///   Variables not in the map remain unchanged.
    ///
    /// # Panics
    ///
    /// Panics if the permutation is not order-preserving.
    ///
    /// # Returns
    ///
    /// A new BDD with variables renamed according to the permutation.
    ///
    /// # Examples
    ///
    /// ```
    /// use bdd_rs::bdd::Bdd;
    /// use bdd_rs::types::Var;
    /// use std::collections::HashMap;
    ///
    /// let bdd = Bdd::default();
    /// // Pre-allocate all variables in order [1, 2, 3]
    /// let x1 = bdd.mk_var(1);
    /// let x2 = bdd.mk_var(2);
    /// let x3 = bdd.mk_var(3);
    ///
    /// // f = x1 ∧ ¬x2
    /// let f = bdd.apply_and(x1, -x2);
    ///
    /// // Order-preserving rename: x1→x2, x2→x3 (1<2 and 2<3, so order preserved)
    /// let mut perm = HashMap::new();
    /// perm.insert(Var::new(1), Var::new(2));
    /// perm.insert(Var::new(2), Var::new(3));
    /// let g = bdd.rename_vars(f, &perm);
    ///
    /// // Verify: g = x2 ∧ ¬x3
    /// let expected = bdd.apply_and(x2, -x3);
    /// assert_eq!(g, expected);
    /// ```
    pub fn rename_vars(&self, f: Ref, permutation: &HashMap<Var, Var>) -> Ref {
        // Validate that all variables in the permutation are registered in the ordering
        for (old_var, new_var) in permutation.iter() {
            assert!(
                self.get_level(*old_var).is_some(),
                "Old variable {} is not registered in the ordering. \
                All variables must be pre-allocated before rename.",
                old_var
            );
            assert!(
                self.get_level(*new_var).is_some(),
                "New variable {} is not registered in the ordering. \
                All variables must be pre-allocated before rename.",
                new_var
            );
        }

        // Validate that the permutation is order-preserving:
        // If old_i precedes old_j in the ordering, then new_i must precede new_j.
        //   (old_i < old_j) => (new_i < new_j)
        let mut sorted_pairs: Vec<_> = permutation.iter().collect();
        // Sort by level of the OLD variables
        sorted_pairs.sort_by(|&(old_a, _), &(old_b, _)| {
            if self.var_precedes(*old_a, *old_b) {
                std::cmp::Ordering::Less
            } else if self.var_precedes(*old_b, *old_a) {
                std::cmp::Ordering::Greater
            } else {
                std::cmp::Ordering::Equal
            }
        });

        for i in 0..sorted_pairs.len() {
            for j in i + 1..sorted_pairs.len() {
                let (old_i, new_i) = sorted_pairs[i];
                let (old_j, new_j) = sorted_pairs[j];
                // old_i precedes old_j (by construction of sorted_pairs)
                // so new_i must also precede new_j for order preservation
                assert!(
                    self.var_precedes(*new_i, *new_j),
                    "Permutation is not order-preserving: {}→{} and {}→{} violates ordering invariant \
                    (new variable {} should precede {} in the ordering).",
                    old_i,
                    new_i,
                    old_j,
                    new_j,
                    new_i,
                    new_j
                );
            }
        }

        let mut cache = Cache::new(16);
        self.rename_vars_(f, permutation, &mut cache)
    }

    fn rename_vars_(&self, f: Ref, permutation: &HashMap<Var, Var>, cache: &mut Cache<Ref, Ref>) -> Ref {
        // Terminals pass through unchanged
        if self.is_terminal(f) {
            return f;
        }

        // Check cache (cache on the original reference including negation)
        if let Some(&result) = cache.get(&f) {
            return result;
        }

        // Handle negation: rename the positive node and negate the result
        let is_negated = f.is_negated();
        let f_positive = if is_negated { -f } else { f };

        // Get the variable and children
        let index = f_positive.index();
        let v = self.variable(index);
        let low = self.low(index);
        let high = self.high(index);

        // Recursively rename variables in children
        let low_new = self.rename_vars_(low, permutation, cache);
        let high_new = self.rename_vars_(high, permutation, cache);

        // Apply permutation to variable (or keep original if not in map)
        let v_new = permutation.get(&v).copied().unwrap_or(v);

        // Create new node with renamed variable
        let result_positive = self.mk_node(v_new, low_new, high_new);
        let result = if is_negated { -result_positive } else { result_positive };

        cache.insert(f, result);
        result
    }
}

// ============================================================================
// Quantification
// ============================================================================

impl Bdd {
    /// Performs existential quantification over a set of variables.
    ///
    /// Returns a new BDD where all occurrences of the specified variables are existentially
    /// quantified out. This is equivalent to the disjunction over all possible assignments
    /// to those variables:
    ///
    /// `∃x.f = f|x=0 ∨ f|x=1`
    ///
    /// For multiple variables:
    /// `∃{x₁,...,xₙ}.f = ⋁ f|x₁=b₁,...,xₙ=bₙ`
    ///
    /// This operation is fundamental for many symbolic algorithms, including:
    /// - Computing image/preimage in model checking
    /// - Relational product computation
    /// - Variable elimination in quantified Boolean formulas
    ///
    /// # Implementation
    ///
    /// This is a one-pass efficient implementation that performs quantification during
    /// a single recursive traversal, rather than computing two cofactors and ORing them.
    /// Variables are eliminated as soon as they are encountered in the BDD.
    ///
    /// # Parameters
    ///
    /// * `f` - The BDD to quantify
    /// * `vars` - Variables to existentially quantify out
    ///
    /// # Returns
    ///
    /// A BDD representing `∃vars.f`
    ///
    /// # Examples
    ///
    /// ```
    /// use bdd_rs::bdd::Bdd;
    /// use bdd_rs::types::Var;
    ///
    /// let bdd = Bdd::default();
    /// let x = bdd.mk_var(1);
    /// let y = bdd.mk_var(2);
    ///
    /// // f = x AND y
    /// let f = bdd.apply_and(x, y);
    ///
    /// // Quantify out x: ∃x.(x ∧ y) = y (using raw integer)
    /// let result = bdd.exists(f, [1]);
    /// assert_eq!(result, y);
    ///
    /// // Quantify out both: ∃x,y.(x ∧ y) = true (using Var)
    /// let result = bdd.exists(f, [Var::new(1), Var::new(2)]);
    /// assert_eq!(result, bdd.one);
    /// ```
    ///
    /// # Performance
    ///
    /// The method uses internal caching to avoid recomputation. For best performance,
    /// the variable list should be sorted, though this is not required for correctness.
    pub fn exists(&self, f: Ref, vars: impl IntoIterator<Item = impl Into<Var>>) -> Ref {
        // Filter out variables not in the ordering and sort by level
        let mut vars_sorted: Vec<Var> = vars
            .into_iter()
            .map(|v| v.into())
            .filter(|&v| self.get_level(v).is_some())
            .collect();
        if vars_sorted.is_empty() {
            return f;
        }
        vars_sorted.sort_by_key(|&v| self.get_level(v).unwrap().index());
        let mut cache = Cache::new(16);
        self.exists_(f, &vars_sorted, 0, &mut cache)
    }

    fn exists_(&self, node: Ref, vars: &[Var], var_idx: usize, cache: &mut Cache<(Ref, usize), Ref>) -> Ref {
        debug!("exists(node = {}, vars = {:?}, var_idx = {})", node, vars, var_idx);

        if self.is_terminal(node) {
            return node;
        }

        // If we've exhausted all variables to quantify, return the node
        if var_idx >= vars.len() {
            return node;
        }

        let key = (node, var_idx);
        if let Some(&res) = cache.get(&key) {
            debug!("cache: exists({:?}) -> {}", key, res);
            return res;
        }

        let v = self.variable(node.index());
        let current_var = vars[var_idx];

        let res = if self.var_precedes(v, current_var) {
            // Node's variable precedes the current quantification variable in the ordering
            // Recurse on both children
            let low = self.low_node(node);
            let high = self.high_node(node);
            let r0 = self.exists_(low, vars, var_idx, cache);
            let r1 = self.exists_(high, vars, var_idx, cache);
            self.mk_node(v, r0, r1)
        } else if v == current_var {
            // Found the variable to quantify out
            // Compute f|v=0 ∨ f|v=1
            let low = self.low_node(node);
            let high = self.high_node(node);
            let r0 = self.exists_(low, vars, var_idx + 1, cache);
            let r1 = self.exists_(high, vars, var_idx + 1, cache);
            self.apply_or(r0, r1)
        } else {
            // current_var precedes v: the quantification variable doesn't appear in this subtree
            // Skip to the next quantification variable
            self.exists_(node, vars, var_idx + 1, cache)
        };

        cache.insert(key, res);
        debug!("computed: exists({:?}) -> {}", key, res);
        res
    }

    /// Performs universal quantification over a set of variables.
    ///
    /// Returns a new BDD where all occurrences of the specified variables are universally
    /// quantified out. This is equivalent to the conjunction over all possible assignments
    /// to those variables:
    ///
    /// `∀x.f = f|x=0 ∧ f|x=1`
    ///
    /// For multiple variables:
    /// `∀{x₁,...,xₙ}.f = ⋀ f|x₁=b₁,...,xₙ=bₙ`
    ///
    /// Universal quantification can be expressed in terms of existential quantification:
    /// `∀x.f = ¬∃x.¬f`
    ///
    /// # Parameters
    ///
    /// * `f` - The BDD to quantify
    /// * `vars` - Variables to universally quantify out
    ///
    /// # Returns
    ///
    /// A BDD representing `∀vars.f`
    ///
    /// # Examples
    ///
    /// ```
    /// use bdd_rs::bdd::Bdd;
    ///
    /// let bdd = Bdd::default();
    /// let x = bdd.mk_var(1);
    /// let y = bdd.mk_var(2);
    ///
    /// // f = x OR y
    /// let f = bdd.apply_or(x, y);
    ///
    /// // Quantify out x: ∀x.(x ∨ y) = y
    /// let result = bdd.forall(f, [1]);
    /// assert_eq!(result, y);
    ///
    /// // Quantify out both: ∀x,y.(x ∨ y) = false
    /// let result = bdd.forall(f, [1, 2]);
    /// assert_eq!(result, bdd.zero);
    /// ```
    pub fn forall(&self, f: Ref, vars: impl IntoIterator<Item = impl Into<Var>>) -> Ref {
        let vars: Vec<Var> = vars.into_iter().map(|v| v.into()).collect();
        // ∀x.f = ¬∃x.¬f
        -self.exists(-f, vars)
    }

    /// Computes the relational product of two BDDs with existential quantification.
    ///
    /// The relational product combines conjunction and existential quantification in one
    /// efficient operation:
    ///
    /// `relProduct(u, v, vars) = ∃vars.(u ∧ v)`
    ///
    /// This is more efficient than computing `exists(apply_and(u, v), vars)` because
    /// quantification is performed during the conjunction operation, potentially producing
    /// a much smaller intermediate result.
    ///
    /// # Applications
    ///
    /// Relational product is fundamental in symbolic model checking and other applications:
    /// - **Image computation**: Computing successor states in state transition systems
    /// - **Reachability analysis**: Finding all reachable states
    /// - **Relational composition**: Composing two relations
    ///
    /// # Parameters
    ///
    /// * `u` - First BDD operand
    /// * `v` - Second BDD operand
    /// * `vars` - Variables to existentially quantify out
    ///
    /// # Returns
    ///
    /// A BDD representing `∃vars.(u ∧ v)`
    ///
    /// # Examples
    ///
    /// ```
    /// use bdd_rs::bdd::Bdd;
    ///
    /// let bdd = Bdd::default();
    /// let x = bdd.mk_var(1);
    /// let y = bdd.mk_var(2);
    /// let z = bdd.mk_var(3);
    ///
    /// // Relation 1: x implies y
    /// let r1 = bdd.apply_imply(x, y);
    /// // Relation 2: y implies z
    /// let r2 = bdd.apply_imply(y, z);
    ///
    /// // Compose relations by eliminating the intermediate variable y
    /// // Result: x implies z
    /// let composed = bdd.rel_product(r1, r2, [2]);
    /// let expected = bdd.apply_imply(x, z);
    /// assert_eq!(composed, expected);
    /// ```
    ///
    /// # Performance
    ///
    /// This operation is significantly more efficient than computing the AND first and
    /// then quantifying, especially when the intermediate result would be large.
    pub fn rel_product(&self, u: Ref, v: Ref, vars: impl IntoIterator<Item = impl Into<Var>>) -> Ref {
        // Filter out variables not in the ordering and sort by level
        let mut vars_sorted: Vec<Var> = vars
            .into_iter()
            .map(|x| x.into())
            .filter(|&v| self.get_level(v).is_some())
            .collect();
        if vars_sorted.is_empty() {
            return self.apply_and(u, v);
        }
        vars_sorted.sort_by_key(|&v| self.get_level(v).unwrap().index());
        let mut cache = Cache::new(16);
        self.rel_product_(u, v, &vars_sorted, 0, &mut cache)
    }

    fn rel_product_(&self, u: Ref, v: Ref, vars: &[Var], var_idx: usize, cache: &mut Cache<(Ref, Ref, usize), Ref>) -> Ref {
        debug!("rel_product(u = {}, v = {}, vars = {:?}, var_idx = {})", u, v, vars, var_idx);

        // Terminal cases
        if self.is_zero(u) || self.is_zero(v) {
            return self.zero;
        }
        if self.is_one(u) && self.is_one(v) {
            return self.one;
        }
        if self.is_one(u) {
            return self.exists_(v, vars, var_idx, &mut Cache::new(16));
        }
        if self.is_one(v) {
            return self.exists_(u, vars, var_idx, &mut Cache::new(16));
        }

        let key = (u, v, var_idx);
        if let Some(&res) = cache.get(&key) {
            debug!("cache: rel_product({:?}) -> {}", key, res);
            return res;
        }

        let i = self.variable(u.index());
        let j = self.variable(v.index());
        let m = self.top_variable(i, j);

        let (u0, u1) = self.top_cofactors(u, m);
        let (v0, v1) = self.top_cofactors(v, m);

        let res = if var_idx < vars.len() && m == vars[var_idx] {
            // This variable should be quantified out
            let h0 = self.rel_product_(u0, v0, vars, var_idx + 1, cache);
            let h1 = self.rel_product_(u1, v1, vars, var_idx + 1, cache);
            self.apply_or(h0, h1)
        } else {
            // Keep this variable
            let h0 = self.rel_product_(u0, v0, vars, var_idx, cache);
            let h1 = self.rel_product_(u1, v1, vars, var_idx, cache);
            self.mk_node(m, h0, h1)
        };

        cache.insert(key, res);
        debug!("computed: rel_product({:?}) -> {}", key, res);
        res
    }
}

// ============================================================================
// Analysis
// ============================================================================

impl Bdd {
    /// Returns all node indices reachable from the given BDD references.
    ///
    /// This performs a depth-first traversal from the root nodes to collect all reachable
    /// node indices. The terminal node (index 1) is always included in the result.
    ///
    /// # Arguments
    ///
    /// * `nodes` - An iterable collection of BDD references to start the traversal from
    ///
    /// # Returns
    ///
    /// A `HashSet<u32>` containing all unique node indices reachable from the given roots,
    /// including the terminal node (index 1).
    ///
    /// # Examples
    ///
    /// ```
    /// use bdd_rs::bdd::Bdd;
    ///
    /// let bdd = Bdd::default();
    /// let x = bdd.mk_var(1);
    /// let y = bdd.mk_var(2);
    ///
    /// // Single variable: the variable node + terminal
    /// let desc = bdd.descendants([x]);
    /// assert_eq!(desc.len(), 2);
    /// assert!(desc.contains(&x.index()));
    /// assert!(desc.contains(&1)); // terminal
    ///
    /// // AND of two variables
    /// let f = bdd.apply_and(x, y);
    /// let desc = bdd.descendants([f]);
    /// assert!(desc.contains(&f.index()));
    /// assert!(desc.contains(&y.index()));
    /// assert!(desc.contains(&1)); // terminal
    /// ```
    ///
    /// # Multiple Roots
    ///
    /// ```
    /// use bdd_rs::bdd::Bdd;
    ///
    /// let bdd = Bdd::default();
    /// let x = bdd.mk_var(1);
    /// let y = bdd.mk_var(2);
    /// let z = bdd.mk_var(3);
    ///
    /// let f1 = bdd.apply_and(x, y);
    /// let f2 = bdd.apply_and(y, z);
    ///
    /// // Descendants from multiple roots (shared nodes counted once)
    /// let desc = bdd.descendants([f1, f2]);
    /// assert!(desc.contains(&f1.index()));
    /// assert!(desc.contains(&f2.index()));
    /// assert!(desc.contains(&y.index())); // shared
    /// ```
    pub fn descendants(&self, nodes: impl IntoIterator<Item = Ref>) -> HashSet<u32> {
        let mut visited = HashSet::new();
        visited.insert(self.one.index());
        let mut stack = Vec::from_iter(nodes.into_iter().map(|node_ref| node_ref.index()));

        while let Some(i) = stack.pop() {
            if visited.insert(i) {
                let node = self.node(i);
                let low = node.low.index();
                if low != 1 {
                    stack.push(low);
                }
                let high = node.high.index();
                if high != 1 {
                    stack.push(high);
                }
            }
        }

        visited
    }

    /// Returns the number of nodes in a BDD.
    ///
    /// This counts all unique nodes reachable from the given node, including the terminal.
    ///
    /// # Examples
    ///
    /// ```
    /// use bdd_rs::bdd::Bdd;
    ///
    /// let bdd = Bdd::default();
    /// let x = bdd.mk_var(1);
    /// let y = bdd.mk_var(2);
    ///
    /// // Single variable
    /// assert_eq!(bdd.size(x), 2);
    ///
    /// // AND of two variables
    /// let and = bdd.apply_and(x, y);
    /// assert_eq!(bdd.size(and), 3);
    ///
    /// // Tautology (just the terminal)
    /// assert_eq!(bdd.size(bdd.one), 1);
    /// ```
    pub fn size(&self, node_ref: Ref) -> u64 {
        debug!("size(f = {})", node_ref);
        if let Some(&size) = self.size_cache().get(&node_ref) {
            debug!("cache: size({}) -> {}", node_ref, size);
            return size;
        }
        let size = self.descendants([node_ref]).len() as u64;
        debug!("computed: size({}) -> {}", node_ref, size);
        self.size_cache_mut().insert(node_ref, size);
        size
    }
}

// ============================================================================
// Memory management
// ============================================================================

impl Bdd {
    /// Performs garbage collection to reclaim unused BDD nodes.
    ///
    /// This removes all nodes that are not reachable from the provided roots.
    /// The operation also clears all caches. Only call this when you have identified
    /// all BDD nodes that should be kept.
    ///
    /// # Arguments
    ///
    /// * `roots` - Slice of BDD references that should be preserved
    ///
    /// # Examples
    ///
    /// ```
    /// use bdd_rs::bdd::Bdd;
    ///
    /// let bdd = Bdd::default();
    /// let x = bdd.mk_var(1);
    /// let y = bdd.mk_var(2);
    ///
    /// // Create some temporary BDDs
    /// let _temp1 = bdd.apply_and(x, y);
    /// let _temp2 = bdd.apply_or(x, y);
    ///
    /// // Keep only the important result
    /// let important = bdd.apply_xor(x, y);
    ///
    /// // Collect garbage, keeping only 'important'
    /// bdd.collect_garbage(&[important]);
    /// // Nodes from temp1 and temp2 are now reclaimed
    /// ```
    pub fn collect_garbage(&self, roots: &[Ref]) {
        debug!("Collecting garbage...");

        self.cache_mut().clear();
        self.size_cache_mut().clear();

        let num_nodes = self.nodes().len();

        // Mark alive nodes using bit vector
        let alive = self.mark_alive(roots, num_nodes);

        // Collect dead node indices and remove from subtables
        let dead_indices: Vec<u32> = {
            let mut nodes = self.nodes_mut();
            let mut subtables = self.subtables_mut();
            let level_map = self.level_map();
            let free_set = self.free_set();

            (2..num_nodes as u32)
                .filter(|&idx| {
                    // Skip if already free or alive
                    if free_set.contains(&idx) || alive[idx as usize] {
                        return false;
                    }

                    // Dead node: remove from its subtable
                    let node = &nodes[idx as usize];
                    let var = node.variable;
                    if !var.is_terminal() {
                        if let Some(&level) = level_map.get(&var) {
                            let low = node.low;
                            let high = node.high;
                            subtables[level.index()].remove(low, high, &mut nodes);
                        }
                    }
                    true
                })
                .collect()
        };

        // Add dead indices to free set for reuse
        self.free_set_mut().extend(dead_indices);

        debug!("Garbage collection complete");
    }

    /// Mark all nodes reachable from roots using a bit vector.
    ///
    /// Returns a vector where `result[i]` is true if node `i` is alive.
    fn mark_alive(&self, roots: &[Ref], num_nodes: usize) -> Vec<bool> {
        let mut alive = vec![false; num_nodes];
        alive[1] = true; // Terminal node is always alive

        let mut stack: Vec<u32> = roots.iter().map(|r| r.index()).collect();

        while let Some(idx) = stack.pop() {
            if alive[idx as usize] {
                continue;
            }
            alive[idx as usize] = true;

            let node = self.node(idx);
            let low_idx = node.low.index();
            let high_idx = node.high.index();

            if !alive[low_idx as usize] {
                stack.push(low_idx);
            }
            if !alive[high_idx as usize] {
                stack.push(high_idx);
            }
        }

        alive
    }
}

// ============================================================================
// Variable reordering
// ============================================================================

impl Bdd {
    /// Swaps two adjacent levels in the variable ordering.
    ///
    /// This is the fundamental operation for dynamic variable reordering.
    /// Nodes at the two levels are restructured to reflect the new ordering.
    ///
    /// For high-level reordering operations, see [`sift_all_variables`](Self::sift_all_variables)
    /// which uses this function internally.
    ///
    /// # Algorithm (CUDD-style swap)
    ///
    /// For each node at level with var_x whose children depend on var_y:
    /// 1. Extract four grandchildren: f00, f01, f10, f11 (where fij = f[x=i, y=j])
    /// 2. Rebuild with var_y on top, var_x below:
    ///    - new_y0 = mk_node(var_x, f00, f10)  -- when y=0
    ///    - new_y1 = mk_node(var_x, f01, f11)  -- when y=1
    ///    - result = mk_node(var_y, new_y0, new_y1)
    /// 3. Update all references to the old node
    ///
    /// # Arguments
    ///
    /// * `level` - The first level to swap (swaps level with level+1)
    ///
    /// # Returns
    ///
    /// A mapping from old node indices to new node references.
    /// Callers should use [`apply_mapping`](Self::apply_mapping) or
    /// [`remap_roots`](Self::remap_roots) to update any BDD roots they hold.
    ///
    /// # Examples
    ///
    /// ```
    /// use bdd_rs::bdd::Bdd;
    /// use bdd_rs::types::Level;
    ///
    /// let bdd = Bdd::default();
    /// let x = bdd.mk_var(1);
    /// let y = bdd.mk_var(2);
    /// let mut f = bdd.apply_and(x, y);
    ///
    /// // Swap levels 0 and 1
    /// let mapping = bdd.swap_adjacent_inplace(Level::new(0)).unwrap();
    ///
    /// // Update f using the mapping
    /// f = bdd.apply_mapping(f, &mapping);
    /// ```
    pub fn swap_adjacent_inplace(&self, level: Level) -> Result<HashMap<u32, Ref>, String> {
        if level.next().index() >= self.num_levels() {
            return Err(format!(
                "Level {} out of bounds (only {} levels)",
                level.next().index(),
                self.num_levels()
            ));
        }

        let var_x = self
            .get_variable_at_level(level)
            .ok_or_else(|| format!("No variable at level {}", level.index()))?;
        let var_y = self
            .get_variable_at_level(level.next())
            .ok_or_else(|| format!("No variable at level {}", level.next().index()))?;

        debug!("Swap: var {} (level {}) <-> var {} (level {})", var_x, level, var_y, level.next());

        // Get nodes at level_x (these have var_x)
        let nodes_at_x = self.get_nodes_at_level(level);
        debug!("  Nodes at level {}: {} nodes", level.index(), nodes_at_x.len());

        // Build a mapping from old node index to new reference
        let mut mapping: HashMap<u32, Ref> = HashMap::new();

        // Transform each node with var_x
        for &node_idx in &nodes_at_x {
            let node = self.node(node_idx);

            // Verify variable
            if node.variable != var_x {
                debug!("Warning: node {} has variable {} but expected {}", node_idx, node.variable, var_x);
                continue;
            }

            // Apply any already-computed mappings to the children
            let low = self.apply_mapping(node.low, &mapping);
            let high = self.apply_mapping(node.high, &mapping);

            // Extract grandchildren (Shannon expansion with respect to var_y)
            let (f_x0_y0, f_x0_y1) = self.extract_grandchildren(low, var_y);
            let (f_x1_y0, f_x1_y1) = self.extract_grandchildren(high, var_y);

            // Rebuild: y on top, x below
            // When y=0: mk_node(x, f_x0_y0, f_x1_y0)
            // When y=1: mk_node(x, f_x0_y1, f_x1_y1)
            let new_y0 = self.mk_node(var_x, f_x0_y0, f_x1_y0);
            let new_y1 = self.mk_node(var_x, f_x0_y1, f_x1_y1);
            let new_node = self.mk_node(var_y, new_y0, new_y1);

            mapping.insert(node_idx, new_node);
            debug!("  Mapped {} -> {}", node_idx, new_node);
        }

        // Update nodes at higher levels (closer to root) that reference swapped nodes.
        // We process from level-1 up to level 0.
        for l in (0..level.index()).rev() {
            let current_level = Level::new(l);
            let var_at_level = self.get_variable_at_level(current_level).expect("Level should have variable");
            let nodes_at_l = self.get_nodes_at_level(current_level);

            for &node_idx in &nodes_at_l {
                let node = self.node(node_idx);

                // Check if any child is in the mapping
                let new_low = self.apply_mapping(node.low, &mapping);
                let new_high = self.apply_mapping(node.high, &mapping);

                if new_low != node.low || new_high != node.high {
                    // This node's children changed, create a new node
                    let new_node = self.mk_node(var_at_level, new_low, new_high);
                    mapping.insert(node_idx, new_node);
                    debug!("  Updated ancestor {} -> {}", node_idx, new_node);
                }
            }
        }

        // Swap ordering metadata
        self.var_order_mut().swap(level.index(), level.next().index());
        self.level_map_mut().insert(var_x, level.next());
        self.level_map_mut().insert(var_y, level);

        // Rebuild subtables from scratch (simpler and more correct)
        self.rebuild_subtables();

        // Clear operation caches (they may contain stale results)
        self.cache_mut().clear();
        self.size_cache_mut().clear();

        debug!("Swap complete");

        Ok(mapping)
    }

    /// Applies a node mapping to a reference, handling negation.
    ///
    /// If the reference's index is in the mapping, returns the mapped value
    /// with negation preserved. Otherwise returns the original reference.
    pub fn apply_mapping(&self, r: Ref, mapping: &HashMap<u32, Ref>) -> Ref {
        if let Some(&new_ref) = mapping.get(&r.index()) {
            if r.is_negated() {
                -new_ref
            } else {
                new_ref
            }
        } else {
            r
        }
    }

    /// Extracts the two cofactors of a function with respect to a variable.
    ///
    /// This is a key helper for the swap algorithm. When swapping variables x and y,
    /// we need to extract the "grandchildren" of a node: the cofactors of a child
    /// with respect to the variable being moved up.
    ///
    /// # Arguments
    ///
    /// * `f` - The BDD reference to extract cofactors from
    /// * `var_y` - The variable to cofactor with respect to
    ///
    /// # Returns
    ///
    /// A tuple (f|_{var_y=0}, f|_{var_y=1}):
    /// - If f has top variable var_y: returns (low child, high child)
    /// - If f is terminal or has different top variable: returns (f, f)
    fn extract_grandchildren(&self, f: Ref, var_y: Var) -> (Ref, Ref) {
        if self.is_terminal(f) {
            return (f, f);
        }

        let node = self.node(f.index());

        if node.variable == var_y {
            // This node has var_y, extract its children
            let low = self.low_node(f);
            let high = self.high_node(f);
            (low, high)
        } else {
            // This node doesn't have var_y, both "grandchildren" are the same
            (f, f)
        }
    }

    /// Rebuilds all subtables from the current node storage.
    ///
    /// Scans all allocated nodes and re-populates the per-level subtables.
    /// This is called after variable reordering when node-to-level mappings change.
    fn rebuild_subtables(&self) {
        debug!("Rebuilding subtables");

        let var_order = self.var_order();

        // Create fresh subtables for each level
        let mut new_subtables: Vec<Subtable> = var_order.iter().map(|&v| Subtable::new(v)).collect();
        drop(var_order);

        // Collect (level, low, high, index) for all non-free nodes first
        let entries: Vec<(usize, Ref, Ref, u32)> = {
            let nodes = self.nodes();
            let free_set = self.free_set();
            let level_map = self.level_map();

            (2..nodes.len())
                .filter_map(|index| {
                    let idx = index as u32;
                    if free_set.contains(&idx) {
                        return None;
                    }

                    let node = &nodes[index];
                    let var = node.variable;

                    // Skip terminal nodes (variable 0)
                    if var.is_terminal() {
                        return None;
                    }

                    level_map.get(&var).map(|&level| (level.index(), node.low, node.high, idx))
                })
                .collect()
        };

        // Now insert with mutable access to nodes
        {
            let mut nodes = self.nodes_mut();
            for (level_idx, low, high, index) in entries {
                new_subtables[level_idx].insert(low, high, index, &mut nodes);
            }
        }

        *self.subtables_mut() = new_subtables;
        debug!("subtables rebuilt");
    }
}

// ============================================================================
// Serialization
// ============================================================================

impl Bdd {
    pub fn to_bracket_string(&self, node_ref: Ref) -> String {
        let mut visited = HashSet::new();
        self.node_to_str(node_ref, &mut visited)
    }

    fn node_to_str(&self, node_ref: Ref, visited: &mut HashSet<u32>) -> String {
        if self.is_zero(node_ref) {
            return "⊥".to_string();
        } else if self.is_one(node_ref) {
            return "⊤".to_string();
        }

        if !visited.insert(node_ref.index()) {
            return format!("{}", node_ref);
        }

        let index = node_ref.index();
        let Node { variable, low, high, .. } = self.node(index);

        format!(
            "{}:({}, {}, {})",
            node_ref,
            variable,
            self.node_to_str(high, visited),
            self.node_to_str(low, visited),
        )
    }
}

#[cfg(test)]
mod tests {
    use test_log::test;

    use super::*;

    #[test]
    fn test_var() {
        let bdd = Bdd::default();

        let x = bdd.mk_var(1);

        assert_eq!(bdd.variable(x.index()), Var::new(1));
        assert_eq!(bdd.high_node(x), bdd.one);
        assert_eq!(bdd.low_node(x), bdd.zero);
    }

    #[test]
    fn test_not_var() {
        let bdd = Bdd::default();

        let x = bdd.mk_var(1);
        let not_x = -x;

        assert_eq!(bdd.variable(not_x.index()), Var::new(1));
        assert_eq!(bdd.high_node(not_x), bdd.zero);
        assert_eq!(bdd.low_node(not_x), bdd.one);
    }

    #[test]
    fn test_terminal() {
        let bdd = Bdd::default();

        assert_eq!(bdd.is_terminal(bdd.zero), true);
        assert_eq!(bdd.is_zero(bdd.zero), true);
        assert_eq!(bdd.is_one(bdd.zero), false);

        assert_eq!(bdd.is_terminal(bdd.one), true);
        assert_eq!(bdd.is_zero(bdd.one), false);
        assert_eq!(bdd.is_one(bdd.one), true);

        assert_eq!(bdd.variable(bdd.zero.index()), Var::ZERO);
        assert_eq!(bdd.low(bdd.zero.index()).index(), 0);
        assert_eq!(bdd.high(bdd.zero.index()).index(), 0);

        assert_eq!(bdd.variable(bdd.one.index()), Var::ZERO);
        assert_eq!(bdd.low(bdd.one.index()).index(), 0);
        assert_eq!(bdd.high(bdd.one.index()).index(), 0);
    }

    #[test]
    fn test_cube() {
        let bdd = Bdd::default();

        let x1 = bdd.mk_var(1);
        let x2 = bdd.mk_var(2);
        let x3 = bdd.mk_var(3);

        let f = bdd.apply_and(bdd.apply_and(x1, x2), x3);
        let cube = bdd.mk_cube([1, 2, 3]);
        assert_eq!(f, cube);

        let f = bdd.apply_and(bdd.apply_and(x1, -x2), -x3);
        let cube = bdd.mk_cube([1, -2, -3]);
        assert_eq!(f, cube);
    }

    #[test]
    fn test_clause() {
        let bdd = Bdd::default();

        let x1 = bdd.mk_var(1);
        let x2 = bdd.mk_var(2);
        let x3 = bdd.mk_var(3);

        let f = bdd.apply_or(bdd.apply_or(x1, x2), x3);
        let clause = bdd.mk_clause([1, 2, 3]);
        assert_eq!(f, clause);

        let f = bdd.apply_or(bdd.apply_or(x1, -x2), -x3);
        let clause = bdd.mk_clause([1, -2, -3]);
        assert_eq!(f, clause);
    }

    #[test]
    fn test_de_morgan_and() {
        let bdd = Bdd::default();

        let x = bdd.mk_var(1);
        let y = bdd.mk_var(2);

        let f = -bdd.apply_and(x, y);
        let g = bdd.apply_or(-x, -y);
        assert_eq!(f, g);
    }

    #[test]
    fn test_de_morgan_or() {
        let bdd = Bdd::default();

        let x = bdd.mk_var(1);
        let y = bdd.mk_var(2);

        let f = -bdd.apply_or(x, y);
        let g = bdd.apply_and(-x, -y);
        assert_eq!(f, g);
    }

    #[test]
    fn test_xor_itself() {
        let bdd = Bdd::default();

        let x = bdd.mk_var(1);
        let y = bdd.mk_var(2);
        let f = bdd.apply_and(x, y);

        let res = bdd.apply_xor(f, f);
        assert_eq!(res, bdd.zero);
    }

    #[test]
    fn test_xor_contrary() {
        let bdd = Bdd::default();

        let x = bdd.mk_var(1);
        let y = bdd.mk_var(2);
        let f = bdd.apply_and(x, y);

        let res = bdd.apply_xor(f, -f);
        assert_eq!(res, bdd.one);
    }

    #[test]
    fn test_apply_ite() {
        let bdd = Bdd::default();

        // Terminal cases
        let g = bdd.mk_var(2);
        let h = bdd.mk_var(3);
        assert_eq!(bdd.apply_ite(bdd.one, g, h), g);
        assert_eq!(bdd.apply_ite(bdd.zero, g, h), h);

        // Functions
        let f = bdd.mk_node(Var::new(4), bdd.one, h);
        assert_eq!(bdd.apply_ite(f, f, h), bdd.apply_or(f, h));
        assert_eq!(bdd.apply_ite(f, g, f), bdd.apply_and(f, g));
        assert_eq!(bdd.apply_ite(f, -g, bdd.one), -bdd.apply_and(f, g));
        assert_eq!(bdd.apply_ite(f, bdd.zero, -h), -bdd.apply_or(f, h));

        // Constants
        let f = bdd.mk_var(5);
        assert_eq!(bdd.apply_ite(f, g, g), g);
        assert_eq!(bdd.apply_ite(f, bdd.one, bdd.zero), f);
        assert_eq!(bdd.apply_ite(f, bdd.zero, bdd.one), -f);

        // General case
        let f = bdd.mk_var(6);
        let g = bdd.mk_var(7);
        let h = bdd.mk_var(8);
        let result = bdd.mk_node(bdd.variable(f.index()), -g, -h);
        assert_eq!(bdd.apply_ite(-f, -g, -h), result);
    }

    #[test]
    fn test_cofactor_cube() {
        let bdd = Bdd::default();

        let f = bdd.mk_cube([1, 2, 3]);
        println!("f = {}", bdd.to_bracket_string(f));

        assert_eq!(bdd.cofactor_cube(f, [1]), bdd.mk_cube([2, 3]));
        assert_eq!(bdd.cofactor_cube(f, [2]), bdd.mk_cube([1, 3]));
        assert_eq!(bdd.cofactor_cube(f, [3]), bdd.mk_cube([1, 2]));
        assert_eq!(bdd.cofactor_cube(f, [-1]), bdd.zero);
        assert_eq!(bdd.cofactor_cube(f, [-2]), bdd.zero);
        assert_eq!(bdd.cofactor_cube(f, [-3]), bdd.zero);

        assert_eq!(bdd.cofactor_cube(f, [1, 2]), bdd.mk_cube([3]));
        assert_eq!(bdd.cofactor_cube(f, [1, 3]), bdd.mk_cube([2]));
        assert_eq!(bdd.cofactor_cube(f, [2, 3]), bdd.mk_cube([1]));
        assert_eq!(bdd.cofactor_cube(f, [1, -2]), bdd.zero);
        assert_eq!(bdd.cofactor_cube(f, [1, -3]), bdd.zero);
        assert_eq!(bdd.cofactor_cube(f, [2, -3]), bdd.zero);
        assert_eq!(bdd.cofactor_cube(f, [-1, 2]), bdd.zero);
        assert_eq!(bdd.cofactor_cube(f, [-1, 3]), bdd.zero);
        assert_eq!(bdd.cofactor_cube(f, [-2, 3]), bdd.zero);

        assert_eq!(bdd.cofactor_cube(f, [1, 2, 3]), bdd.one);
        assert_eq!(bdd.cofactor_cube(f, [1, 2, -3]), bdd.zero);
        assert_eq!(bdd.cofactor_cube(f, [1, -2, 3]), bdd.zero);
        assert_eq!(bdd.cofactor_cube(f, [1, -2, -3]), bdd.zero);
        assert_eq!(bdd.cofactor_cube(f, [-1, 2, 3]), bdd.zero);
        assert_eq!(bdd.cofactor_cube(f, [-1, 2, -3]), bdd.zero);
        assert_eq!(bdd.cofactor_cube(f, [-1, -2, 3]), bdd.zero);
        assert_eq!(bdd.cofactor_cube(f, [-1, -2, -3]), bdd.zero);

        assert_eq!(bdd.cofactor_cube(f, std::iter::empty::<i32>()), f);
        assert_eq!(bdd.cofactor_cube(bdd.one, [1]), bdd.one);
        assert_eq!(bdd.cofactor_cube(bdd.zero, [1]), bdd.zero);
        assert_eq!(bdd.cofactor_cube(bdd.one, [-1]), bdd.one);
        assert_eq!(bdd.cofactor_cube(bdd.zero, [-1]), bdd.zero);
    }

    impl Bdd {
        fn build_example(&self) -> Ref {
            let x1 = self.mk_var(1);
            let x2 = self.mk_var(2);
            let x3 = self.mk_var(3);

            // x1 ∨ (x2 ∧ x3)
            let f = self.apply_or(self.apply_and(x1, x2), x3);

            f
        }
    }

    #[test]
    fn test_constrain_base() {
        let bdd = Bdd::default();
        {
            let f = bdd.build_example();
            let g = bdd.one;
            let result = bdd.constrain(f, g);
            assert_eq!(result, f); // When g is 1, the result should be f.
        }
        {
            let f = bdd.build_example();
            let g = f;
            let result = bdd.constrain(f, g);
            assert_eq!(result, bdd.one); // When g is f, the result should be 1.
        }
        {
            let f = bdd.zero;
            let g = bdd.build_example();
            let result = bdd.constrain(f, g);
            assert_eq!(result, bdd.zero); // When f is 0, the result should be 0.
        }
    }

    // Somenzi, 1999
    #[test]
    fn test_constrain_example1() {
        let bdd = Bdd::default();

        // Pre-register variables in correct order (x1 at level 0, x2 at level 1, x3 at level 2)
        bdd.mk_var(1);
        bdd.mk_var(2);
        bdd.mk_var(3);

        let s = bdd.mk_node(Var::new(3), -bdd.one, bdd.one);
        let p = bdd.mk_node(Var::new(2), -s, s);
        let r = bdd.mk_node(Var::new(2), s, bdd.one);
        let q = bdd.mk_node(Var::new(2), -s, bdd.one);
        let t = bdd.mk_node(Var::new(2), -bdd.one, s);

        println!("s = {}", bdd.to_bracket_string(s));
        println!("p = {}", bdd.to_bracket_string(p));
        println!("r = {}", bdd.to_bracket_string(r));
        println!("q = {}", bdd.to_bracket_string(q));
        println!("t = {}", bdd.to_bracket_string(t));

        let f = bdd.mk_node(Var::new(1), -p, s);
        println!("f = {}", bdd.to_bracket_string(f));
        let g = bdd.mk_node(Var::new(1), -r, q);
        println!("g = {}", bdd.to_bracket_string(g));
        let h = bdd.mk_node(Var::new(1), -bdd.one, t);
        println!("h = {}", bdd.to_bracket_string(h));

        let fg = bdd.constrain(f, g);
        println!("f|g = {}", bdd.to_bracket_string(fg));

        assert_eq!(fg, h, "h = constrain(f, g)");
    }

    #[test]
    fn test_constrain_example2() {
        let bdd = Bdd::default();

        // f = x1*x3 + ~x1*(x2^x3)
        // g = x1*x2 + ~x2*~x3
        // h = f|g = x1*x2*x3
        // where:
        //   * is AND
        //   + is OR
        //   ^ is XOR
        //   ~ is NOT
        //   | is 'constrain'

        let x1 = bdd.mk_var(1);
        let x2 = bdd.mk_var(2);
        let x3 = bdd.mk_var(3);

        // f = x1*x3 + ~x1*(x2^x3)
        let f = bdd.apply_or(bdd.apply_and(x1, x3), bdd.apply_and(-x1, bdd.apply_xor(x2, x3)));

        // g = x1*x2 + ~x2*~x3
        let g = bdd.apply_or(bdd.apply_and(x1, x2), bdd.apply_and(-x2, -x3));

        // h = x1*x2*x3
        let h = bdd.mk_cube([1, 2, 3]);

        // f|g == h
        let fg = bdd.constrain(f, g);
        assert_eq!(fg, h);
    }

    // Somenzi, 1999
    #[test]
    fn test_restrict() {
        let bdd = Bdd::default();

        let x = bdd.mk_var(1);
        let _y = bdd.mk_var(2);
        let z = bdd.mk_var(3);

        let s = bdd.mk_node(Var::new(3), -bdd.one, bdd.one);
        let p = bdd.mk_node(Var::new(2), -s, s);
        let r = bdd.mk_node(Var::new(2), s, bdd.one);
        let q = bdd.mk_node(Var::new(2), -s, bdd.one);
        let t = bdd.mk_node(Var::new(2), -bdd.one, s);

        println!("s = {}", bdd.to_bracket_string(s));
        println!("p = {}", bdd.to_bracket_string(p));
        println!("r = {}", bdd.to_bracket_string(r));
        println!("q = {}", bdd.to_bracket_string(q));
        println!("t = {}", bdd.to_bracket_string(t));

        let f = bdd.mk_node(Var::new(1), -p, s);
        println!("f = {}", bdd.to_bracket_string(f));
        let g = bdd.mk_node(Var::new(1), -r, q);
        println!("g = {}", bdd.to_bracket_string(g));
        let h = bdd.apply_and(x, z);
        println!("h = {}", bdd.to_bracket_string(h));

        let fg = bdd.restrict(f, g);
        println!("f||g = {}", bdd.to_bracket_string(fg));
        assert_eq!(fg, h, "h = restrict(f, g)");
    }

    #[test]
    fn test_negation_in_ite_cache() {
        let bdd = Bdd::default();

        let x1 = bdd.mk_var(1);
        println!("x1 = {}", bdd.to_bracket_string(x1));
        let x2 = bdd.mk_var(2);
        println!("x2 = {}", bdd.to_bracket_string(x2));

        let f = bdd.apply_xor(x1, x2);
        println!("f = {}", bdd.to_bracket_string(f));
        let g = bdd.apply_xor(x1, x2);
        println!("g = {}", bdd.to_bracket_string(g));

        let f = bdd.apply_xor(x1, -x2);
        println!("f = {}", bdd.to_bracket_string(f));
        let g = bdd.apply_xor(x1, -x2);
        println!("g = {}", bdd.to_bracket_string(g));
        assert_eq!(f, g);
    }

    #[test]
    fn test_substitute() {
        let bdd = Bdd::default();

        let x1 = bdd.mk_var(1);
        let x2 = bdd.mk_var(2);
        let x3 = bdd.mk_var(3);

        // f = (x1 == x2) | x3
        let f = bdd.apply_or(bdd.apply_eq(x1, x2), x3);
        println!("f of size {} = {}", bdd.size(f), bdd.to_bracket_string(f));

        // f[x2<-0] = (x1 == 0) | x3 = ~x1 | x3
        let f_x2_zero = bdd.substitute(f, 2, false); // f|x2<-0
        println!("f|x2<-0 of size {} = {}", bdd.size(f_x2_zero), bdd.to_bracket_string(f_x2_zero));

        // g = ~x1 | x3
        let g = bdd.apply_or(-x1, x3);
        println!("g of size {} = {}", bdd.size(g), bdd.to_bracket_string(g));

        assert_eq!(f_x2_zero, g);
    }

    #[test]
    fn test_substitute_multi() {
        let bdd = Bdd::default();

        let x1 = bdd.mk_var(1);
        let x2 = bdd.mk_var(2);
        let x3 = bdd.mk_var(3);
        let x4 = bdd.mk_var(4);

        let values = HashMap::from([(Var::new(2), true), (Var::new(4), false)]);
        println!("values = {:?}", values);

        let f = bdd.apply_and_many([-x1, x2, x3, -x4]);
        println!("f of size {} = {}", bdd.size(f), bdd.to_bracket_string(f));

        let g = bdd.substitute_multi(f, &values); // result of f|(x2<-1,x4<-0)
        println!("g of size {} = {}", bdd.size(g), bdd.to_bracket_string(g));

        let h = bdd.apply_and(-x1, x3); // expected
        println!("h of size {} = {}", bdd.size(h), bdd.to_bracket_string(h));

        assert_eq!(g, h);
    }

    #[test]
    fn test_compose() {
        let bdd = Bdd::default();

        let x1 = bdd.mk_var(1);
        let x2 = bdd.mk_var(2);
        let x3 = bdd.mk_var(3);

        let f = bdd.apply_and(bdd.apply_eq(x1, x2), x3);
        println!("f of size {} = {}", bdd.size(f), bdd.to_bracket_string(f));

        let g = -bdd.apply_eq(x1, x2);
        println!("g of size {} = {}", bdd.size(g), bdd.to_bracket_string(g));

        let h = bdd.compose(f, bdd.variable(x3.index()).id(), g);
        println!("h of size {} = {}", bdd.size(h), bdd.to_bracket_string(h));
        assert!(bdd.is_zero(h));
    }

    #[test]
    fn test_ite_constant() {
        let bdd = Bdd::default();

        let x1 = bdd.mk_var(1);
        let x2 = bdd.mk_var(2);

        let f = bdd.apply_and(x1, x2);
        println!("f = x1&x2 of size {} = {}", bdd.size(f), bdd.to_bracket_string(f));

        println!("is_implies(f, x1) = {}", bdd.is_implies(f, x1));
        println!("is_implies(f, x2) = {}", bdd.is_implies(f, x2));
        println!("is_implies(f, -x1) = {}", bdd.is_implies(f, -x1));
        println!("is_implies(f, -x2) = {}", bdd.is_implies(f, -x2));
        println!("is_implies(f, x1&x2 = {}", bdd.is_implies(f, bdd.apply_and(x1, x2)));
        println!("is_implies(f, x1|x2 = {}", bdd.is_implies(f, bdd.apply_or(x1, x2)));

        assert!(bdd.is_implies(f, x1));
        assert!(bdd.is_implies(f, x2));
        assert!(!bdd.is_implies(f, -x1));
        assert!(!bdd.is_implies(f, -x2));
        assert!(bdd.is_implies(f, bdd.apply_and(x1, x2)));
        assert!(bdd.is_implies(f, bdd.apply_or(x1, x2)));
        assert!(bdd.is_implies(x1, bdd.one));
        assert!(bdd.is_implies(x2, bdd.one));
        assert!(bdd.is_implies(bdd.zero, x1));
        assert!(bdd.is_implies(bdd.zero, x2));
        assert!(bdd.is_implies(x1, bdd.apply_or(x1, x2)));
        assert!(bdd.is_implies(x2, bdd.apply_or(x1, x2)));
    }

    #[test]
    fn test_one_sat() {
        let bdd = Bdd::default();

        let f = bdd.mk_cube([1, -2, -3]);
        println!("f = {} of size {}", f, bdd.size(f));
        let model = bdd.one_sat(f);
        println!("model = {:?}", model);
        assert_eq!(model, Some(vec![1, -2, -3]));

        let g = bdd.apply_and(f, -bdd.mk_cube(model.unwrap()));
        println!("g = {} of size {}", g, bdd.size(g));
        let model = bdd.one_sat(g);
        println!("model = {:?}", model);
        assert_eq!(model, None);
    }

    #[test]
    fn test_one_sat_many() {
        let bdd = Bdd::default();

        let mut all_cubes = Vec::new();

        for &s1 in &[1, -1] {
            for &s2 in &[1, -1] {
                for &s3 in &[1, -1] {
                    all_cubes.push([1 * s1, 2 * s2, 3 * s3]);
                }
            }
        }

        for cube in all_cubes {
            println!("Testing cube: {:?}", cube);

            let f = bdd.mk_cube(cube);
            println!("f = {} of size {}", f, bdd.size(f));
            let model = bdd.one_sat(f);
            println!("model = {:?}", model);
            assert_eq!(model, Some(cube.to_vec()));

            let g = bdd.apply_and(f, -bdd.mk_cube(model.unwrap()));
            println!("g = {} of size {}", g, bdd.size(g));
            let model = bdd.one_sat(g);
            println!("model = {:?}", model);
            assert_eq!(model, None);
        }
    }

    #[test]
    fn test_all_paths_1() {
        let bdd = Bdd::default();

        let f = bdd.mk_cube([1, -2, 3]);
        println!("f = {} of size {}", f, bdd.size(f));
        let paths = bdd.paths(f).collect::<Vec<_>>();
        println!("paths: {}", paths.len());
        for path in paths.iter() {
            println!("path = {:?}", path);
        }
        assert_eq!(paths.len(), 1);
        assert_eq!(paths[0], vec![1, -2, 3]);
    }

    #[test]
    fn test_all_paths_2() {
        let bdd = Bdd::default();

        let c1 = bdd.mk_cube([1, -2, 3]);
        let c2 = bdd.mk_cube([1, 2, -3]);
        let f = bdd.apply_or(c1, c2);
        println!("f = {} of size {}", f, bdd.size(f));
        let paths = bdd.paths(f).collect::<Vec<_>>();
        println!("paths: {}", paths.len());
        for path in paths.iter() {
            println!("path = {:?}", path);
        }
        assert_eq!(paths.len(), 2);
        assert!(paths.contains(&vec![1, -2, 3]));
        assert!(paths.contains(&vec![1, 2, -3]));
    }

    #[test]
    fn test_all_paths_one() {
        let bdd = Bdd::default();

        let f = bdd.one;
        println!("f = {} of size {}", f, bdd.size(f));
        let paths = bdd.paths(f).collect::<Vec<_>>();
        println!("paths: {}", paths.len());
        for path in paths.iter() {
            println!("path = {:?}", path);
        }
        assert_eq!(paths.len(), 1);
        assert_eq!(paths[0], vec![]);
    }

    #[test]
    fn test_all_paths_zero() {
        let bdd = Bdd::default();

        let f = bdd.zero;
        println!("f = {} of size {}", f, bdd.size(f));
        let paths = bdd.paths(f).collect::<Vec<_>>();
        println!("paths: {}", paths.len());
        for path in paths.iter() {
            println!("path = {:?}", path);
        }
        assert_eq!(paths.len(), 0);
    }

    #[test]
    fn test_all_paths_to_zero() {
        let bdd = Bdd::default();

        let f = bdd.mk_cube([-1, -2, -3]);
        println!("f = {} of size {}", bdd.to_bracket_string(f), bdd.size(f));
        println!("~f = {} of size {}", bdd.to_bracket_string(-f), bdd.size(-f));
        let paths = bdd.paths(-f).collect::<Vec<_>>();
        println!("paths to one for {}: {}", -f, paths.len());
        for path in paths.iter() {
            println!("path = {:?}", path);
        }

        let paths = bdd.paths(f).collect::<Vec<_>>();
        println!("paths to one for {}: {}", f, paths.len());
        for path in paths.iter() {
            println!("path = {:?}", path);
        }
    }

    #[test]
    fn test_descendants_terminal() {
        let bdd = Bdd::default();

        // Terminal zero (index 1) has no descendants except itself
        let desc = bdd.descendants([bdd.zero]);
        println!("descendants of zero: {:?}", desc);
        assert_eq!(desc.len(), 1);
        assert!(desc.contains(&1));

        // Terminal one (index 1) has itself as descendant
        let desc = bdd.descendants([bdd.one]);
        println!("descendants of one: {:?}", desc);
        assert_eq!(desc.len(), 1);
        assert!(desc.contains(&1));

        // Both terminals together
        let desc = bdd.descendants([bdd.zero, bdd.one]);
        assert_eq!(desc.len(), 1);
        assert!(desc.contains(&1));
    }

    #[test]
    fn test_descendants_single_var() {
        let bdd = Bdd::default();

        let x = bdd.mk_var(1);
        // Variable node x1 points to: high=one (1), low=zero (negated 1)
        // So descendants should be: x.index() and 1 (terminal)
        let desc = bdd.descendants([x]);
        assert_eq!(desc.len(), 2);
        assert!(desc.contains(&x.index()));
        assert!(desc.contains(&1)); // terminal
    }

    #[test]
    fn test_descendants_negated_var() {
        let bdd = Bdd::default();

        let x = bdd.mk_var(1);
        let not_x = -x;

        // Negated reference points to same node, so descendants are the same
        let desc = bdd.descendants([not_x]);
        assert_eq!(desc.len(), 2);
        assert!(desc.contains(&x.index()));
        assert!(desc.contains(&1)); // terminal
    }

    #[test]
    fn test_descendants_and() {
        let bdd = Bdd::default();

        let x1 = bdd.mk_var(1);
        let x2 = bdd.mk_var(2);
        let f = bdd.apply_and(x1, x2);

        // f = x1 AND x2 creates a structure:
        // f_node -> (low=negated 1, high=x2_node)
        // x2_node -> (low=negated 1, high=1)
        let desc = bdd.descendants([f]);

        // Should include: f's index, x2's index, and terminal (1)
        assert!(desc.contains(&f.index()));
        assert!(desc.contains(&x2.index()));
        assert!(desc.contains(&1));

        // Should be at least 3 nodes
        assert!(desc.len() >= 3);
    }

    #[test]
    fn test_descendants_or() {
        let bdd = Bdd::default();

        let x1 = bdd.mk_var(1);
        let x2 = bdd.mk_var(2);
        let f = bdd.apply_or(x1, x2);

        let desc = bdd.descendants([f]);

        // Should include the root and all reachable nodes
        assert!(desc.contains(&f.index()));
        assert!(desc.contains(&1)); // terminal
        assert!(desc.len() >= 2);
    }

    #[test]
    fn test_descendants_cube() {
        let bdd = Bdd::default();

        let f = bdd.mk_cube([1, 2, 3]);
        let desc = bdd.descendants([f]);

        // Cube x1 AND x2 AND x3 creates a chain:
        // x1_node -> x2_node -> x3_node -> terminal
        assert!(desc.contains(&f.index()));
        assert!(desc.contains(&1)); // terminal

        // Should have at least 4 nodes: 3 variable nodes + 1 terminal
        assert!(desc.len() >= 4);
    }

    #[test]
    fn test_descendants_multiple_roots() {
        let bdd = Bdd::default();

        let x1 = bdd.mk_var(1);
        let x2 = bdd.mk_var(2);
        let x3 = bdd.mk_var(3);

        let f1 = bdd.apply_and(x1, x2);
        let f2 = bdd.apply_and(x2, x3);

        // Get descendants from both roots
        let desc = bdd.descendants([f1, f2]);

        // Should include nodes from both formulas
        assert!(desc.contains(&f1.index()));
        assert!(desc.contains(&f2.index()));
        assert!(desc.contains(&x2.index())); // shared node
        assert!(desc.contains(&1)); // terminal
    }

    #[test]
    fn test_descendants_shared_structure() {
        let bdd = Bdd::default();

        let x1 = bdd.mk_var(1);
        let x2 = bdd.mk_var(2);

        let f1 = bdd.apply_and(x1, x2);
        let f2 = bdd.apply_or(x1, x2);

        // Both formulas share x1 and x2 nodes
        let desc1 = bdd.descendants([f1]);
        let desc2 = bdd.descendants([f2]);
        let desc_both = bdd.descendants([f1, f2]);

        // Union should not double-count shared nodes
        let union_size = desc1.union(&desc2).count();
        assert_eq!(desc_both.len(), union_size);
    }

    #[test]
    fn test_descendants_empty() {
        let bdd = Bdd::default();

        // Empty iterator should return just the terminal 1 (added by default)
        let desc = bdd.descendants(std::iter::empty());
        assert_eq!(desc.len(), 1);
        assert!(desc.contains(&1));
    }

    #[test]
    fn test_descendants_complex_formula() {
        let bdd = Bdd::default();

        let x1 = bdd.mk_var(1);
        let x2 = bdd.mk_var(2);
        let x3 = bdd.mk_var(3);

        // (x1 XOR x2) AND x3
        let xor = bdd.apply_xor(x1, x2);
        let f = bdd.apply_and(xor, x3);

        let desc = bdd.descendants([f]);

        // Should include all nodes in the formula
        assert!(desc.contains(&f.index()));
        assert!(desc.contains(&1)); // terminal

        // XOR creates a larger structure
        assert!(desc.len() >= 4);
    }

    #[test]
    fn test_descendants_size_consistency() {
        let bdd = Bdd::default();

        let f = bdd.mk_cube([1, 2, 3]);

        // descendants should return the same count as size
        let desc = bdd.descendants([f]);
        let size = bdd.size(f);

        assert_eq!(desc.len() as u64, size);
    }

    #[test]
    fn test_descendants_negated_edges() {
        let bdd = Bdd::default();

        // Create a formula with negations
        let x1 = bdd.mk_var(1);
        let x2 = bdd.mk_var(2);
        let f = bdd.apply_and(-x1, -x2);

        let desc = bdd.descendants([f]);

        // Negated edges don't create new nodes, just traverse to existing ones
        assert!(desc.contains(&f.index()));
        assert!(desc.contains(&1)); // terminal
    }

    #[test]
    fn test_to_bracket_string_terminal() {
        let bdd = Bdd::default();

        println!("zero = {}", bdd.to_bracket_string(bdd.zero));
        assert_eq!(bdd.to_bracket_string(bdd.zero), "⊥");

        println!("one = {}", bdd.to_bracket_string(bdd.one));
        assert_eq!(bdd.to_bracket_string(bdd.one), "⊤");
    }

    #[test]
    fn test_to_bracket_string_1() {
        let bdd = Bdd::default();

        // x1 ∧ x2
        let x1 = bdd.mk_var(1);
        let x2 = bdd.mk_var(2);
        let f = bdd.apply_and(x1, x2);
        println!("f = x1 ∧ x2 = {}", bdd.to_bracket_string(f));
        assert_eq!(bdd.to_bracket_string(f), "@4:(x1, @3:(x2, ⊤, ⊥), ⊥)");
    }

    #[test]
    fn test_to_bracket_string_2() {
        let bdd = Bdd::default();

        // ~x1 ∨ (~x2 ∧ x3)
        let x1 = bdd.mk_var(1);
        let x2 = bdd.mk_var(2);
        let x3 = bdd.mk_var(3);
        let f = bdd.apply_or(-x1, bdd.apply_and(-x2, x3));
        println!("f = ~x1 ∨ (~x2 ∧ x3) = {}", bdd.to_bracket_string(f));
        assert_eq!(bdd.to_bracket_string(f), "~@6:(x1, @5:(x2, ⊤, ~@4:(x3, ⊤, ⊥)), ⊥)");
    }

    #[test]
    fn test_exists_single() {
        let bdd = Bdd::default();

        let x1 = bdd.mk_var(1);
        let x2 = bdd.mk_var(2);

        // f = x1 ∧ x2
        let f = bdd.apply_and(x1, x2);
        println!("f = x1 ∧ x2 = {}", bdd.to_bracket_string(f));

        // ∃x1.(x1 ∧ x2) = x2
        let result = bdd.exists(f, [1]);
        println!("∃x1.f = {}", bdd.to_bracket_string(result));
        assert_eq!(result, x2);

        // ∃x2.(x1 ∧ x2) = x1
        let result = bdd.exists(f, [2]);
        println!("∃x2.f = {}", bdd.to_bracket_string(result));
        assert_eq!(result, x1);
    }

    #[test]
    fn test_exists_multiple() {
        let bdd = Bdd::default();

        let x1 = bdd.mk_var(1);
        let x2 = bdd.mk_var(2);
        let x3 = bdd.mk_var(3);

        // f = x1 ∧ x2 ∧ x3
        let f = bdd.apply_and(bdd.apply_and(x1, x2), x3);
        println!("f = x1 ∧ x2 ∧ x3 = {}", bdd.to_bracket_string(f));

        // ∃x1,x3.(x1 ∧ x2 ∧ x3) = x2
        let result = bdd.exists(f, [1, 3]);
        println!("∃x1,x3.f = {}", bdd.to_bracket_string(result));
        assert_eq!(result, x2);

        // ∃x1,x2,x3.(x1 ∧ x2 ∧ x3) = 1
        let result = bdd.exists(f, [1, 2, 3]);
        println!("∃x1,x2,x3.f = {}", bdd.to_bracket_string(result));
        assert_eq!(result, bdd.one);
    }

    #[test]
    fn test_exists_or() {
        let bdd = Bdd::default();

        let x1 = bdd.mk_var(1);
        let x2 = bdd.mk_var(2);

        // f = x1 ∨ x2
        let f = bdd.apply_or(x1, x2);
        println!("f = x1 ∨ x2 = {}", bdd.to_bracket_string(f));

        // ∃x1.(x1 ∨ x2) = 1
        let result = bdd.exists(f, [1]);
        println!("∃x1.f = {}", bdd.to_bracket_string(result));
        assert_eq!(result, bdd.one);

        // ∃x2.(x1 ∨ x2) = 1
        let result = bdd.exists(f, [2]);
        println!("∃x2.f = {}", bdd.to_bracket_string(result));
        assert_eq!(result, bdd.one);
    }

    #[test]
    fn test_exists_complex() {
        let bdd = Bdd::default();

        let x1 = bdd.mk_var(1);
        let x2 = bdd.mk_var(2);
        let x3 = bdd.mk_var(3);

        // f = (x1 ∧ x2) ∨ (¬x1 ∧ x3)
        let c1 = bdd.apply_and(x1, x2);
        let c2 = bdd.apply_and(-x1, x3);
        let f = bdd.apply_or(c1, c2);
        println!("f = (x1 ∧ x2) ∨ (¬x1 ∧ x3) = {}", bdd.to_bracket_string(f));

        // ∃x1.f = x2 ∨ x3
        let result = bdd.exists(f, [1]);
        let expected = bdd.apply_or(x2, x3);
        println!("∃x1.f = {}", bdd.to_bracket_string(result));
        println!("expected = {}", bdd.to_bracket_string(expected));
        assert_eq!(result, expected);
    }

    #[test]
    fn test_exists_empty_vars() {
        let bdd = Bdd::default();

        let x1 = bdd.mk_var(1);
        let x2 = bdd.mk_var(2);
        let f = bdd.apply_and(x1, x2);

        // Quantifying no variables should return the same formula
        let result = bdd.exists(f, std::iter::empty::<Var>());
        assert_eq!(result, f);
    }

    #[test]
    fn test_exists_independent_vars() {
        let bdd = Bdd::default();

        let x1 = bdd.mk_var(1);
        let x2 = bdd.mk_var(2);

        // f = x1 ∧ x2 (doesn't depend on x3, x4, x5)
        let f = bdd.apply_and(x1, x2);
        println!("f = x1 ∧ x2 = {}", bdd.to_bracket_string(f));

        // Quantify out x3 (which doesn't appear): should return the same formula
        let result = bdd.exists(f, [3]);
        println!("∃x3.f = {}", bdd.to_bracket_string(result));
        assert_eq!(result, f, "Quantifying independent variable should return same BDD");

        // Quantify out x3, x4, x5 (none appear): should return the same formula
        let result = bdd.exists(f, [3, 4, 5]);
        println!("∃x3,x4,x5.f = {}", bdd.to_bracket_string(result));
        assert_eq!(result, f, "Quantifying multiple independent variables should return same BDD");

        // Mix of dependent and independent variables
        // Quantify out x1, x3: ∃x1,x3.(x1 ∧ x2) = x2
        let result = bdd.exists(f, [1, 3]);
        println!("∃x1,x3.f = {}", bdd.to_bracket_string(result));
        assert_eq!(result, x2, "Should correctly handle mix of dependent and independent variables");

        // Independent variables before dependent ones
        // Quantify out x3, x1, x5, x2 (x3,x5 don't appear)
        let result = bdd.exists(f, [3, 1, 5, 2]);
        println!("∃x3,x1,x5,x2.f = {}", bdd.to_bracket_string(result));
        assert_eq!(result, bdd.one, "Should handle unsorted mix correctly");
    }

    #[test]
    fn test_forall_single() {
        let bdd = Bdd::default();

        let x1 = bdd.mk_var(1);
        let x2 = bdd.mk_var(2);

        // f = x1 ∨ x2
        let f = bdd.apply_or(x1, x2);
        println!("f = x1 ∨ x2 = {}", bdd.to_bracket_string(f));

        // ∀x1.(x1 ∨ x2) = x2
        let result = bdd.forall(f, [1]);
        println!("∀x1.f = {}", bdd.to_bracket_string(result));
        assert_eq!(result, x2);

        // ∀x2.(x1 ∨ x2) = x1
        let result = bdd.forall(f, [2]);
        println!("∀x2.f = {}", bdd.to_bracket_string(result));
        assert_eq!(result, x1);
    }

    #[test]
    fn test_forall_multiple() {
        let bdd = Bdd::default();

        let x1 = bdd.mk_var(1);
        let x2 = bdd.mk_var(2);
        let x3 = bdd.mk_var(3);

        // f = x1 ∨ x2 ∨ x3
        let f = bdd.apply_or(bdd.apply_or(x1, x2), x3);
        println!("f = x1 ∨ x2 ∨ x3 = {}", bdd.to_bracket_string(f));

        // ∀x1,x3.(x1 ∨ x2 ∨ x3) = x2
        let result = bdd.forall(f, [1, 3]);
        println!("∀x1,x3.f = {}", bdd.to_bracket_string(result));
        assert_eq!(result, x2);

        // ∀x1,x2,x3.(x1 ∨ x2 ∨ x3) = 0
        let result = bdd.forall(f, [1, 2, 3]);
        println!("∀x1,x2,x3.f = {}", bdd.to_bracket_string(result));
        assert_eq!(result, bdd.zero);
    }

    #[test]
    fn test_forall_and() {
        let bdd = Bdd::default();

        let x1 = bdd.mk_var(1);
        let x2 = bdd.mk_var(2);

        // f = x1 ∧ x2
        let f = bdd.apply_and(x1, x2);
        println!("f = x1 ∧ x2 = {}", bdd.to_bracket_string(f));

        // ∀x1.(x1 ∧ x2) = 0
        let result = bdd.forall(f, [1]);
        println!("∀x1.f = {}", bdd.to_bracket_string(result));
        assert_eq!(result, bdd.zero);

        // ∀x2.(x1 ∧ x2) = 0
        let result = bdd.forall(f, [2]);
        println!("∀x2.f = {}", bdd.to_bracket_string(result));
        assert_eq!(result, bdd.zero);
    }

    #[test]
    fn test_rel_product_simple() {
        let bdd = Bdd::default();

        let x = bdd.mk_var(1);
        let y = bdd.mk_var(2);
        let z = bdd.mk_var(3);

        // r1: x → y  (x implies y)
        let r1 = bdd.apply_imply(x, y);
        println!("r1 = x → y = {}", bdd.to_bracket_string(r1));

        // r2: y → z  (y implies z)
        let r2 = bdd.apply_imply(y, z);
        println!("r2 = y → z = {}", bdd.to_bracket_string(r2));

        // Compose: eliminate y to get x → z
        let result = bdd.rel_product(r1, r2, [2]);
        println!("∃y.(r1 ∧ r2) = {}", bdd.to_bracket_string(result));

        let expected = bdd.apply_imply(x, z);
        println!("expected = x → z = {}", bdd.to_bracket_string(expected));
        assert_eq!(result, expected);
    }

    #[test]
    fn test_rel_product_vs_exists() {
        let bdd = Bdd::default();

        let x1 = bdd.mk_var(1);
        let x2 = bdd.mk_var(2);
        let x3 = bdd.mk_var(3);

        let f = bdd.apply_and(x1, x2);
        let g = bdd.apply_or(x2, x3);

        // Using rel_product
        let result1 = bdd.rel_product(f, g, [2]);
        println!("rel_product(f, g, [2]) = {}", bdd.to_bracket_string(result1));

        // Using exists(and(...))
        let result2 = bdd.exists(bdd.apply_and(f, g), [2]);
        println!("exists(f ∧ g, [2]) = {}", bdd.to_bracket_string(result2));

        // They should be equal
        assert_eq!(result1, result2);
    }

    #[test]
    fn test_rel_product_empty_vars() {
        let bdd = Bdd::default();

        let x1 = bdd.mk_var(1);
        let x2 = bdd.mk_var(2);

        let f = bdd.apply_and(x1, x2);
        let g = bdd.mk_var(3);

        // Relational product with no variables to eliminate is just AND
        let result = bdd.rel_product(f, g, std::iter::empty::<Var>());
        let expected = bdd.apply_and(f, g);
        assert_eq!(result, expected);
    }

    #[test]
    fn test_rel_product_terminals() {
        let bdd = Bdd::default();

        let x = bdd.mk_var(1);

        // rel_product with zero should be zero
        let result = bdd.rel_product(bdd.zero, x, [1]);
        assert_eq!(result, bdd.zero);

        let result = bdd.rel_product(x, bdd.zero, [1]);
        assert_eq!(result, bdd.zero);

        // rel_product(1, 1, []) = 1
        let result = bdd.rel_product(bdd.one, bdd.one, std::iter::empty::<Var>());
        assert_eq!(result, bdd.one);
    }

    #[test]
    #[should_panic(expected = "Permutation is not order-preserving")]
    fn test_rename_vars_not_order_preserving() {
        let bdd = Bdd::default();

        // Pre-allocate both variables
        let x1 = bdd.mk_var(1);
        let _x2 = bdd.mk_var(2);

        // Rename x1→x2, x2→x1 (swap) - NOT order-preserving!
        let mut perm = HashMap::new();
        perm.insert(Var::new(1), Var::new(2));
        perm.insert(Var::new(2), Var::new(1));

        // This should panic
        let _result = bdd.rename_vars(x1, &perm);
    }

    #[test]
    fn test_rename_vars_chain() {
        let bdd = Bdd::default();

        // Pre-allocate all variables so ordering is [1, 2, 3]
        let x1 = bdd.mk_var(1);
        let x2 = bdd.mk_var(2);
        let x3 = bdd.mk_var(3);

        // f = x1 ∧ ¬x2
        let f = bdd.apply_and(x1, -x2);

        // Chain rename: x1→x2, x2→x3
        // This is order-preserving: 1<2 maps to 2<3
        let mut perm = HashMap::new();
        perm.insert(Var::new(1), Var::new(2));
        perm.insert(Var::new(2), Var::new(3));

        let g = bdd.rename_vars(f, &perm); // g = x2 ∧ ¬x3

        // Create expected: x2 ∧ ¬x3
        let expected = bdd.apply_and(x2, -x3);

        assert_eq!(g, expected);
    }

    #[test]
    fn test_rename_vars_backward() {
        let bdd = Bdd::default();

        // Pre-allocate variables in natural order so the ordering is [1, 2, 3]
        let _x1 = bdd.mk_var(1);
        let x2 = bdd.mk_var(2);
        let x3 = bdd.mk_var(3);
        let f = bdd.apply_and(x2, x3); // f(x2, x3) = x2 ∧ x3

        // Current ordering: [1, 2, 3]
        // f uses only x2 (level 1) and x3 (level 2)

        // Backward rename: x2→x1, x3→x2
        // This is order-preserving: x2 < x3 in ordering, and x1 < x2 in ordering
        let mut perm = HashMap::new();
        perm.insert(Var::new(2), Var::new(1));
        perm.insert(Var::new(3), Var::new(2));

        let g = bdd.rename_vars(f, &perm); // g(x1, x2) = x1 ∧ x2

        // Verify it computes x1 ∧ x2 by checking all truth table entries
        assert!(bdd.is_zero(bdd.cofactor_cube(g, [-1, -2]))); // g[0,0] = 0
        assert!(bdd.is_zero(bdd.cofactor_cube(g, [-1, 2]))); // g[0,1] = 0
        assert!(bdd.is_zero(bdd.cofactor_cube(g, [1, -2]))); // g[1,0] = 0
        assert!(bdd.is_one(bdd.cofactor_cube(g, [1, 2]))); // g[1,1] = 1
    }

    #[test]
    fn test_rename_vars_shift() {
        let bdd = Bdd::default();

        // Pre-allocate all variables in order [1, 2, 3, 4]
        let x1 = bdd.mk_var(1);
        let x2 = bdd.mk_var(2);
        let _x3 = bdd.mk_var(3);
        let _x4 = bdd.mk_var(4);
        let f = bdd.apply_and(x1, x2); // f(x1, x2) = x1 ∧ x2

        // Shift: x1→x3, x2→x4 (order-preserving: 1<2 maps to 3<4)
        let mut perm = HashMap::new();
        perm.insert(Var::new(1), Var::new(3));
        perm.insert(Var::new(2), Var::new(4));

        let g = bdd.rename_vars(f, &perm); // g(x3, x4) = x3 ∧ x4

        // Verify it computes x3 ∧ x4 by checking all truth table entries
        assert!(bdd.is_zero(bdd.cofactor_cube(g, [-3, -4]))); // g[0,0] = 0
        assert!(bdd.is_zero(bdd.cofactor_cube(g, [-3, 4]))); // g[0,1] = 0
        assert!(bdd.is_zero(bdd.cofactor_cube(g, [3, -4]))); // g[1,0] = 0
        assert!(bdd.is_one(bdd.cofactor_cube(g, [3, 4]))); // g[1,1] = 1
    }

    #[test]
    #[should_panic(expected = "Permutation is not order-preserving")]
    fn test_rename_vars_partial() {
        let bdd = Bdd::default();

        let x1 = bdd.mk_var(1);
        let x2 = bdd.mk_var(2);
        let x3 = bdd.mk_var(3);
        let f = bdd.apply_and(bdd.apply_and(x1, x2), x3); // x1 ∧ x2 ∧ x3

        // Only rename x1→x2, x2→x1 (swap), leave x3 unchanged - NOT order-preserving!
        let mut perm = HashMap::new();
        perm.insert(Var::new(1), Var::new(2));
        perm.insert(Var::new(2), Var::new(1));

        // This should panic
        let _g = bdd.rename_vars(f, &perm);
    }

    #[test]
    #[should_panic(expected = "Permutation is not order-preserving")]
    fn test_rename_vars_negation() {
        let bdd = Bdd::default();

        let x1 = bdd.mk_var(1);
        let x2 = bdd.mk_var(2);
        let f = bdd.apply_and(-x1, x2); // ¬x1 ∧ x2

        // Swap x1↔x2 - NOT order-preserving!
        let mut perm = HashMap::new();
        perm.insert(Var::new(1), Var::new(2));
        perm.insert(Var::new(2), Var::new(1));

        // This should panic
        let _g = bdd.rename_vars(f, &perm);
    }

    #[test]
    #[should_panic(expected = "Permutation is not order-preserving")]
    fn test_rename_vars_cyclic() {
        let bdd = Bdd::default();

        let x1 = bdd.mk_var(1);
        let x2 = bdd.mk_var(2);
        let x3 = bdd.mk_var(3);

        // f = x1 ∨ x2 ∨ x3
        let f = bdd.apply_or(bdd.apply_or(x1, x2), x3);

        // Cyclic rename: x1→x2, x2→x3, x3→x1 (a cycle!) - NOT order-preserving!
        let mut perm = HashMap::new();
        perm.insert(Var::new(1), Var::new(2));
        perm.insert(Var::new(2), Var::new(3));
        perm.insert(Var::new(3), Var::new(1));

        // This should panic
        let _g = bdd.rename_vars(f, &perm);
    }
}
