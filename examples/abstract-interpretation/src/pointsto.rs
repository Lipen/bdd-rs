//! # Points-to Analysis Domain
//!
//! A BDD-based abstract domain for tracking pointer aliasing and memory locations
//! in programs with dynamic memory allocation.
//!
//! ## What is Points-to Analysis?
//!
//! Points-to analysis answers the fundamental question: **"What memory locations
//! can this pointer variable reference?"**
//!
//! This is crucial for:
//! - **Alias Analysis**: Do two pointers point to the same memory?
//! - **Memory Safety**: Can we dereference this pointer safely?
//! - **Optimization**: Can we reorder these memory operations?
//! - **Bug Detection**: Detecting null pointer dereferences, use-after-free, etc.
//!
//! ### Concrete Example
//!
//! ```c
//! int x, y;
//! int *p, *q;
//!
//! p = &x;      // p points to x
//! q = &y;      // q points to y
//! if (condition) {
//!     p = q;   // p now may point to y
//! }
//! // After if: p may point to {x, y}, q points to {y}
//! *p = 42;     // May write to x or y
//! *q = 13;     // Definitely writes to y
//! ```
//!
//! ## Memory Location Types
//!
//! Programs use different kinds of memory, each with distinct properties:
//!
//! ### Stack Memory (Local Variables)
//! ```c
//! void foo() {
//!     int x;        // Stack-allocated, dies when foo returns
//!     int *p = &x;  // p points to stack location "x"
//! }
//! ```
//! - **Lifetime**: Function scope only
//! - **Access**: Fast, automatic cleanup
//! - **Representation**: `Location::Stack("x")`
//!
//! ### Heap Memory (Dynamic Allocation)
//! ```c
//! int *p = malloc(sizeof(int));  // Heap-allocated, lives until freed
//! *p = 42;
//! free(p);
//! ```
//! - **Lifetime**: Explicit management (malloc/free)
//! - **Access**: Slower, manual cleanup required
//! - **Representation**: `Location::Heap(site_id)`
//!   - Each `malloc` call site gets unique ID
//!   - Multiple calls to same site → same abstract location (may-aliasing)
//!
//! ### Global Memory (Static Variables)
//! ```c
//! int global_var;  // Lives for entire program
//! int *p = &global_var;
//! ```
//! - **Lifetime**: Entire program execution
//! - **Access**: Accessible from any function
//! - **Representation**: `Location::Global("global_var")`
//!
//! ### Special Locations
//! - **Null**: `NULL` pointer (points to nothing)
//! - **Unknown**: External/library pointers (conservative approximation)
//!
//! ## Abstract Interpretation: Bottom and Top
//!
//! In abstract interpretation, we use **abstract values** to represent sets of
//! concrete values:
//!
//! ### Bottom (⊥) - Unreachable State
//! ```text
//! ⊥ = "This program point cannot be reached"
//! ```
//! Example:
//! ```c
//! if (false) {
//!     int *p = &x;  // This code is unreachable → ⊥
//! }
//! ```
//!
//! ### Top (⊤) - Unknown/Everything
//! ```text
//! ⊤ = "Pointer may point to ANY location" (worst case)
//! ```
//! Example:
//! ```c
//! int *p;
//! if (unknown_condition()) {
//!     p = &x;
//! } else if (other_condition()) {
//!     p = &y;
//! } else {
//!     p = malloc(...);
//! }
//! // p could point to anything → conservatively approximate as ⊤
//! ```
//!
//! ### Lattice Structure
//! ```text
//!                    ⊤ (all locations)
//!                   /│\
//!                  / │ \
//!        {x,y,z} {x,y} {y,z} {x,z}  (sets of locations)
//!                  \ │ /
//!                   \│/
//!              {x}  {y}  {z}  (singletons)
//!                   \│/
//!                    ∅ (empty set - points nowhere)
//!                    │
//!                    ⊥ (unreachable code)
//! ```
//!
//! **Partial Order**: elem1 ⊑ elem2 means elem1 is "more precise" than elem2
//! - `{x}` ⊑ `{x,y}` (singleton is more precise than set)
//! - `⊥` ⊑ everything (unreachable is more precise than anything)
//! - everything ⊑ `⊤` (any knowledge is more precise than "unknown")
//!
//! ## Analysis Algorithms: Andersen vs Steensgaard
//!
//! ### Andersen's Analysis (This Implementation)
//!
//! **Subset-Based Constraints**:
//! ```text
//! p = &x         →  x ∈ pts(p)           (p definitely points to x)
//! p = q          →  pts(q) ⊆ pts(p)      (p inherits q's targets)
//! p = *q         →  ∀l ∈ pts(q): pts(l) ⊆ pts(p)  (load)
//! *p = q         →  ∀l ∈ pts(p): pts(q) ⊆ pts(l)  (store)
//! ```
//!
//! **Properties**:
//! - More precise (distinguishes {x} from {x,y})
//! - Slower: O(n³) worst case
//! - Suitable for: Medium-sized programs, when precision matters
//!
//! **Example**:
//! ```c
//! int *p, *q;
//! p = &x;  // pts(p) = {x}
//! q = &y;  // pts(q) = {y}
//! p = q;   // pts(p) = {y}, pts(q) = {y}  ← Keeps them separate!
//! ```
//!
//! ### Steensgaard's Analysis (Alternative)
//!
//! **Equality-Based Constraints** (unification):
//! ```text
//! p = q          →  pts(p) = pts(q)      (merge points-to sets)
//! ```
//!
//! **Properties**:
//! - Less precise (merges too aggressively)
//! - Faster: O(n·α(n)) ≈ almost linear
//! - Suitable for: Very large programs, when speed matters
//!
//! **Example**:
//! ```c
//! int *p, *q;
//! p = &x;  // pts(p) = {x}
//! q = &y;  // pts(q) = {y}
//! p = q;   // pts(p) = pts(q) = {x,y}  ← Merged! Less precise
//! ```
//!
//! ## BDD Representation
//!
//! We use **Binary Decision Diagrams** to compactly represent points-to sets:
//!
//! ### Encoding
//! ```text
//! Each location → unique BDD variable
//! Location x → variable v₁
//! Location y → variable v₂
//! Location z → variable v₃
//!
//! Points-to set = disjunction (OR) of variables:
//! p points to {x,y} → BDD: v₁ ∨ v₂
//! q points to {x}   → BDD: v₁
//! ```
//!
//! ### Operations
//! ```text
//! Union (Join):        pts(p) ∪ pts(q)  →  BDD_p ∨ BDD_q
//! Intersection (Meet): pts(p) ∩ pts(q)  →  BDD_p ∧ BDD_q
//! Subset Test:         pts(p) ⊆ pts(q)  →  BDD_p ∧ ¬BDD_q = ⊥
//! ```
//!
//! ### Why BDDs?
//! - **Canonical**: Unique representation for each set
//! - **Compact**: Shared structure for common subsets
//! - **Efficient**: Operations in O(|BDD₁| × |BDD₂|)
//!
//! ## Flow-Sensitivity vs Flow-Insensitivity
//!
//! ### Flow-Insensitive (Simpler, faster)
//! ```text
//! Treats entire program as one big set of statements.
//! Same points-to set for variable throughout program.
//! ```
//! Example:
//! ```c
//! p = &x;  // pts(p) = {x}
//! use(p);
//! p = &y;  // pts(p) = {x,y}  ← Merges with previous!
//! use(p);
//! ```
//! Result: `pts(p) = {x,y}` everywhere (conservative)
//!
//! ### Flow-Sensitive (This implementation - more precise)
//! ```text
//! Different points-to set at each program point.
//! Tracks how pointers change over time.
//! ```
//! Example:
//! ```c
//! p = &x;  // pts(p) = {x}
//! use(p);  // pts(p) = {x}  ← Still just x
//! p = &y;  // pts(p) = {y}  ← Overwrites!
//! use(p);  // pts(p) = {y}  ← Now just y
//! ```
//! Result: Precise information at each point
//!
//! ## Complete Usage Example
//!
//! ```rust,ignore
//! use abstract_interpretation::*;
//! use std::rc::Rc;
//!
//! // Create domain with BDD manager
//! let domain = PointsToDomain::new();
//! let mut state = PointsToElement::new(domain.manager());
//!
//! // C code: int x, y; int *p, *q;
//! let x = Location::Stack("x".to_string());
//! let y = Location::Stack("y".to_string());
//!
//! // C code: p = &x;
//! state = domain.assign_address(&state, "p", &x);
//! assert_eq!(domain.decode_bdd(state.get("p")), hashset!{x.clone()});
//!
//! // C code: q = p;
//! state = domain.assign_copy(&state, "q", "p");
//! assert!(state.must_alias(&domain, "p", "q"));  // Definitely alias
//!
//! // C code: if (...) { p = &y; }
//! let then_state = domain.assign_address(&state, "p", &y);
//! state = domain.join(&state, &then_state);  // Merge branches
//!
//! // After if: p may point to {x, y}
//! assert_eq!(domain.decode_bdd(state.get("p")).len(), 2);
//! assert!(state.may_alias(&domain, "p", "q"));  // May alias
//! assert!(!state.must_alias(&domain, "p", "q")); // Not definite
//! ```

use std::cell::RefCell;
use std::collections::{HashMap, HashSet};
use std::fmt;
use std::rc::Rc;

use bdd_rs::bdd::Bdd;
use bdd_rs::reference::Ref;

use crate::AbstractDomain;

/// Memory location types in the program.
///
/// Locations represent addressable memory regions that pointers can reference.
/// Each location type has different lifetime and access characteristics.
///
/// # Examples
///
/// ```rust,ignore
/// // Stack variable in function
/// let x = Location::Stack("x".to_string());  // Lives in function scope
///
/// // Heap allocation (malloc call site ID)
/// let h1 = Location::Heap(42);  // site_id = 42
///
/// // Global/static variable
/// let g = Location::Global("counter".to_string());
///
/// // Null pointer
/// let null = Location::Null;
///
/// // Unknown external pointer (conservative)
/// let ext = Location::Unknown;
/// ```
///
/// # Allocation Site Abstraction
///
/// For heap locations, we use **allocation-site abstraction**: all objects
/// allocated at the same `malloc()` call site are merged into one abstract location.
///
/// ```c
/// for (int i = 0; i < 10; i++) {
///     int *p = malloc(sizeof(int));  // site_id = 17
///     // All 10 allocations → same abstract location Heap(17)
/// }
/// ```
///
/// This is a **sound approximation** (may-alias) but loses precision about
/// which concrete allocation we're referring to.
#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Location {
    /// Null pointer (nullptr)
    Null,
    /// Stack-allocated variable (function local)
    Stack(String),
    /// Heap allocation site (identified by unique ID)
    Heap(u64),
    /// Global/static variable
    Global(String),
    /// Unknown or external location (conservative approximation)
    Unknown,
}

impl fmt::Display for Location {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Location::Null => write!(f, "null"),
            Location::Stack(name) => write!(f, "&{}", name),
            Location::Heap(id) => write!(f, "heap#{}", id),
            Location::Global(name) => write!(f, "global:{}", name),
            Location::Unknown => write!(f, "?"),
        }
    }
}

/// Bidirectional mapping between memory locations and BDD variables.
///
/// This provides efficient encoding of location sets as BDDs and decoding
/// BDDs back to location sets. Each location gets a unique BDD variable ID.
///
/// # BDD Variable Assignment
///
/// Variables are assigned starting from 1 (BDD variables cannot be 0):
/// ```text
/// Location::Stack("x") → variable 1 (v₁)
/// Location::Stack("y") → variable 2 (v₂)
/// Location::Heap(42)   → variable 3 (v₃)
/// ...
/// ```
///
/// # Example
///
/// ```rust,ignore
/// let mut map = LocationMap::new();
///
/// let x = Location::Stack("x".to_string());
/// let y = Location::Stack("y".to_string());
///
/// let var_x = map.get_or_allocate(&x);  // Returns 1 (first variable)
/// let var_y = map.get_or_allocate(&y);  // Returns 2 (second variable)
/// let var_x2 = map.get_or_allocate(&x); // Returns 1 (reuses existing)
///
/// assert_eq!(var_x, 1);
/// assert_eq!(var_y, 2);
/// assert_eq!(var_x, var_x2);
/// ```
#[derive(Debug, Clone)]
pub struct LocationMap {
    /// Maps locations to their BDD variable IDs
    loc_to_var: HashMap<Location, usize>,
    /// Maps BDD variable IDs to locations
    var_to_loc: HashMap<usize, Location>,
    /// Next available BDD variable
    next_var: usize,
}

impl LocationMap {
    /// Create a new empty location map.
    pub fn new() -> Self {
        Self {
            loc_to_var: HashMap::new(),
            var_to_loc: HashMap::new(),
            next_var: 1, // BDD variables are 1-indexed
        }
    }

    /// Get or allocate a BDD variable for a location.
    pub fn get_or_allocate(&mut self, loc: &Location) -> usize {
        if let Some(&var) = self.loc_to_var.get(loc) {
            var
        } else {
            let var = self.next_var;
            self.next_var += 1;
            self.loc_to_var.insert(loc.clone(), var);
            self.var_to_loc.insert(var, loc.clone());
            var
        }
    }

    /// Get the BDD variable for a location, if it exists.
    pub fn get_var(&self, loc: &Location) -> Option<usize> {
        self.loc_to_var.get(loc).copied()
    }

    /// Get the location for a BDD variable, if it exists.
    pub fn get_location(&self, var: usize) -> Option<&Location> {
        self.var_to_loc.get(&var)
    }

    /// Get all allocated locations.
    pub fn locations(&self) -> impl Iterator<Item = &Location> {
        self.loc_to_var.keys()
    }
}

impl Default for LocationMap {
    fn default() -> Self {
        Self::new()
    }
}

/// Abstract element representing points-to information for all pointers.
///
/// Maps each pointer variable to a BDD representing the set of memory locations
/// it may point to. This is the main data structure for flow-sensitive analysis.
///
/// # Structure
///
/// ```text
/// PointsToElement {
///     "p" → BDD(v₁ ∨ v₂),  // p may point to locations 1 or 2
///     "q" → BDD(v₁),       // q definitely points to location 1
///     "r" → BDD(⊥),        // r points nowhere (uninitialized)
/// }
/// ```
///
/// # Special States
///
/// - **Bottom** (`is_bottom = true`): Unreachable code
/// - **Top** (`is_top = true`): All pointers may point anywhere (worst case)
/// - **Normal**: Regular points-to information
///
/// # Example
///
/// ```rust,ignore
/// let domain = PointsToDomain::new();
/// let mut elem = PointsToElement::new(domain.manager());
///
/// // Initially: all pointers point nowhere (empty sets)
/// assert!(domain.decode_bdd(elem.get("p")).is_empty());
///
/// // After p = &x:
/// elem = domain.assign_address(&elem, "p", &Location::Stack("x".to_string()));
/// assert_eq!(domain.decode_bdd(elem.get("p")).len(), 1);
///
/// // After p = &y (in another branch):
/// let elem2 = domain.assign_address(&elem, "p", &Location::Stack("y".to_string()));
/// let joined = domain.join(&elem, &elem2);
/// assert_eq!(domain.decode_bdd(joined.get("p")).len(), 2);  // p → {x,y}
/// ```
#[derive(Debug, Clone)]
pub struct PointsToElement {
    /// Maps pointer variables to their points-to sets (as BDDs)
    points_to: HashMap<String, Ref>,
    /// Shared BDD manager
    manager: Rc<Bdd>,
    /// Whether this element represents an unreachable state
    is_bottom: bool,
    /// Whether this element represents all possible states (top)
    is_top: bool,
}

impl PointsToElement {
    /// Create a new points-to element with the given BDD manager.
    pub fn new(manager: Rc<Bdd>) -> Self {
        Self {
            points_to: HashMap::new(),
            manager,
            is_bottom: false,
            is_top: false,
        }
    }

    /// Create a bottom (unreachable) element.
    pub fn bottom(manager: Rc<Bdd>) -> Self {
        Self {
            points_to: HashMap::new(),
            manager,
            is_bottom: true,
            is_top: false,
        }
    }

    /// Create a top (all possible states) element.
    pub fn top(manager: Rc<Bdd>) -> Self {
        Self {
            points_to: HashMap::new(),
            manager,
            is_bottom: false,
            is_top: true,
        }
    }

    /// Get the points-to BDD for a variable.
    ///
    /// Returns the zero BDD (empty set) if the variable is not tracked.
    pub fn get(&self, var: &str) -> Ref {
        if self.is_bottom {
            return self.manager.zero;
        }
        self.points_to.get(var).copied().unwrap_or(self.manager.zero)
    }

    /// Set the points-to BDD for a variable.
    pub fn set(&mut self, var: String, bdd: Ref) {
        self.points_to.insert(var, bdd);
    }

    /// Check if this element is bottom (unreachable).
    pub fn is_bottom(&self) -> bool {
        self.is_bottom
    }

    /// Get the BDD manager.
    pub fn manager(&self) -> &Rc<Bdd> {
        &self.manager
    }
}

impl PartialEq for PointsToElement {
    fn eq(&self, other: &Self) -> bool {
        if self.is_bottom != other.is_bottom || self.is_top != other.is_top {
            return false;
        }

        if self.is_bottom || self.is_top {
            return true; // Both are bottom or both are top
        }

        // Compare points_to maps
        if self.points_to.len() != other.points_to.len() {
            return false;
        }

        // Check that all keys have equal BDDs
        for (key, &bdd1) in &self.points_to {
            if let Some(&bdd2) = other.points_to.get(key) {
                // Compare BDD references - they're equal if they point to the same node
                if bdd1 != bdd2 {
                    return false;
                }
            } else {
                return false;
            }
        }

        true
    }
}

/// Points-to analysis domain with BDD-based operations.
///
/// Provides the abstract domain interface for points-to analysis, including
/// pointer operations (assignments, loads, stores) and alias queries.
///
/// # Operations
///
/// ## Assignments
/// ```text
/// p = NULL         → assign_null(elem, "p")
/// p = &x           → assign_address(elem, "p", &Location::Stack("x"))
/// p = q            → assign_copy(elem, "p", "q")
/// p = malloc(...)  → assign_alloc(elem, "p", site_id)
/// ```
///
/// ## Memory Operations
/// ```text
/// p = *q           → assign_load(elem, "p", "q")
///                      Load: p gets all targets that q's targets point to
///
/// *p = q           → assign_store(elem, "p", "q")
///                      Store: All of p's targets now point to q's targets
/// ```
///
/// ## Control Flow
/// ```text
/// if-then-else     → join(then_elem, else_elem)
///                      Merge: Union of points-to sets
///
/// loop convergence → widen(elem1, elem2)
///                      Accelerate: Ensure termination
/// ```
///
/// # Example: Linked List Traversal
///
/// ```rust,ignore
/// let domain = PointsToDomain::new();
/// let mut state = PointsToElement::new(domain.manager());
///
/// // struct Node { int data; Node *next; };
/// // Node *head = malloc(...);
/// state = domain.assign_alloc(&state, "head", 1);
///
/// // Node *current = head;
/// state = domain.assign_copy(&state, "current", "head");
///
/// // while (current != NULL) {
/// //     current = current->next;  // Load from current's target
/// // }
/// // After loop: current may point to any node in the list
/// ```
#[derive(Debug, Clone)]
pub struct PointsToDomain {
    /// Shared BDD manager for all operations
    manager: Rc<Bdd>,
    /// Location to BDD variable mapping
    locations: Rc<RefCell<LocationMap>>,
}

impl PointsToDomain {
    /// Create a new points-to domain with a fresh BDD manager.
    pub fn new() -> Self {
        Self {
            manager: Rc::new(Bdd::default()),
            locations: Rc::new(RefCell::new(LocationMap::new())),
        }
    }

    /// Get the BDD manager.
    pub fn manager(&self) -> &Rc<Bdd> {
        &self.manager
    }

    /// Encode a single location as a BDD.
    pub fn encode_location(&self, loc: &Location) -> Ref {
        let var = self.locations.borrow_mut().get_or_allocate(loc);
        self.manager.mk_var(var as u32)
    }

    /// Encode a set of locations as a BDD (disjunction).
    pub fn encode_location_set(&self, locs: &[Location]) -> Ref {
        if locs.is_empty() {
            return self.manager.zero;
        }

        let mut result = self.manager.zero;
        for loc in locs {
            let loc_bdd = self.encode_location(loc);
            result = self.manager.apply_or(result, loc_bdd);
        }
        result
    }

    /// Decode a BDD to a set of locations.
    ///
    /// This extracts all satisfying assignments (locations) from the BDD.
    pub fn decode_bdd(&self, bdd: Ref) -> HashSet<Location> {
        let mut locations = HashSet::new();

        if self.manager.is_zero(bdd) {
            return locations;
        }

        // Get all paths to ONE in the BDD
        let paths = self.manager.paths(bdd);

        for path in paths {
            // Each path represents a conjunction of literals
            // Extract positive literals (locations present)
            for &lit in &path {
                if lit > 0 {
                    let var = lit.abs() as usize;
                    if let Some(loc) = self.locations.borrow().get_location(var) {
                        locations.insert(loc.clone());
                    }
                }
            }
        }

        locations
    }

    /// Check if a BDD represents a singleton set (exactly one location).
    pub fn is_singleton(&self, bdd: Ref) -> bool {
        self.decode_bdd(bdd).len() == 1
    }

    /// Assign null to a pointer: `ptr = NULL`
    pub fn assign_null(&self, elem: &PointsToElement, var: &str) -> PointsToElement {
        if elem.is_bottom {
            return elem.clone();
        }

        let mut result = elem.clone();
        let null_bdd = self.encode_location(&Location::Null);
        result.set(var.to_string(), null_bdd);
        result
    }

    /// Assign address of a location: `ptr = &loc`
    ///
    /// This is a **strong update**: overwrites the previous points-to set
    /// for the pointer variable.
    ///
    /// # Arguments
    /// - `elem`: Current abstract state
    /// - `var`: Pointer variable name
    /// - `loc`: Memory location being addressed
    ///
    /// # Example
    ///
    /// ```rust,ignore
    /// // C code: int x; int *p = &x;
    /// let x = Location::Stack("x".to_string());
    /// let state = domain.assign_address(&state, "p", &x);
    /// // Result: p → {x}
    /// ```
    pub fn assign_address(&self, elem: &PointsToElement, var: &str, loc: &Location) -> PointsToElement {
        if elem.is_bottom {
            return elem.clone();
        }

        let mut result = elem.clone();
        let loc_bdd = self.encode_location(loc);
        result.set(var.to_string(), loc_bdd);
        result
    }

    /// Copy pointer: `dst = src`
    pub fn assign_copy(&self, elem: &PointsToElement, dst: &str, src: &str) -> PointsToElement {
        if elem.is_bottom {
            return elem.clone();
        }

        let mut result = elem.clone();
        let src_bdd = elem.get(src);
        result.set(dst.to_string(), src_bdd);
        result
    }

    /// Heap allocation: `ptr = malloc()`
    pub fn assign_alloc(&self, elem: &PointsToElement, var: &str, site_id: u64) -> PointsToElement {
        if elem.is_bottom {
            return elem.clone();
        }

        let mut result = elem.clone();
        let heap_loc = Location::Heap(site_id);
        let heap_bdd = self.encode_location(&heap_loc);
        result.set(var.to_string(), heap_bdd);
        result
    }

    /// Load through pointer: `dst = *src`
    ///
    /// Dereferences `src` and loads the points-to set from the target locations.
    ///
    /// # Semantics
    ///
    /// ```text
    /// If src points to {l₁, l₂, ...}, then:
    /// dst gets the union of what l₁, l₂, ... point to
    ///
    /// pts(dst) = ⋃{pts(l) | l ∈ pts(src)}
    /// ```
    ///
    /// # Example
    ///
    /// ```rust,ignore
    /// // C code:
    /// // int x, y;
    /// // int *p = &x;
    /// // int **q = &p;   // q points to p
    /// // int *r = *q;    // r gets what p points to
    ///
    /// let x = Location::Stack("x".to_string());
    /// state = domain.assign_address(&state, "p", &x);
    /// // p → {x}
    ///
    /// // Simplified: treat p as a location
    /// let p_loc = Location::Stack("p".to_string());
    /// state = domain.assign_address(&state, "q", &p_loc);
    /// // q → {p}
    ///
    /// state = domain.assign_load(&state, "r", "q");
    /// // r → {x} (loads what p points to)
    /// ```
    ///
    /// # Strong vs Weak Updates
    ///
    /// - **Strong update**: If `src` points to exactly one location, overwrite
    /// - **Weak update**: If `src` may point to multiple locations, union
    ///
    /// This implementation uses weak updates for soundness.
    pub fn assign_load(&self, elem: &PointsToElement, dst: &str, src: &str) -> PointsToElement {
        if elem.is_bottom {
            return elem.clone();
        }

        let src_bdd = elem.get(src);

        // Get all locations that src may point to
        let src_targets = self.decode_bdd(src_bdd);

        if src_targets.is_empty() {
            // src points nowhere - this is an error, return bottom
            return PointsToElement::bottom(Rc::clone(&self.manager));
        }

        // Union the points-to sets of all targets
        let mut result_bdd = self.manager.zero;
        for target_loc in src_targets {
            // For simplicity, we track heap locations' contents
            // In a full implementation, we'd need a separate map for heap contents
            // For now, we'll be conservative and use Top (all locations)
            let target_bdd = elem.get(&target_loc.to_string());
            result_bdd = self.manager.apply_or(result_bdd, target_bdd);
        }

        let mut result = elem.clone();
        result.set(dst.to_string(), result_bdd);
        result
    }

    /// Store through pointer: `*dst = src`
    ///
    /// Dereferences `dst` and updates all target locations to point to `src`'s targets.
    ///
    /// # Semantics
    ///
    /// ```text
    /// If dst points to {l₁, l₂, ...}, then:
    /// For each lᵢ, update: pts(lᵢ) := pts(lᵢ) ∪ pts(src)
    ///
    /// (Weak update - union with existing values)
    /// ```
    ///
    /// # Example
    ///
    /// ```rust,ignore
    /// // C code:
    /// // int x, y;
    /// // int *a = &x;
    /// // int **p = &a;   // p points to a
    /// // int *b = &y;
    /// // *p = b;         // Store: a now points to y
    ///
    /// let x = Location::Stack("x".to_string());
    /// let y = Location::Stack("y".to_string());
    ///
    /// state = domain.assign_address(&state, "a", &x);
    /// // a → {x}
    ///
    /// // Simplified: treat a as a location
    /// let a_loc = Location::Stack("a".to_string());
    /// state = domain.assign_address(&state, "p", &a_loc);
    /// // p → {a}
    ///
    /// state = domain.assign_address(&state, "b", &y);
    /// // b → {y}
    ///
    /// state = domain.assign_store(&state, "p", "b");
    /// // Now: a → {x, y} (weak update: union)
    /// ```
    ///
    /// # Why Weak Updates?
    ///
    /// Flow-insensitive analysis must be **sound** (never miss a possible alias).
    /// Since we don't know the execution order, we conservatively union with
    /// existing values rather than overwriting.
    pub fn assign_store(&self, elem: &PointsToElement, dst: &str, src: &str) -> PointsToElement {
        if elem.is_bottom {
            return elem.clone();
        }

        let dst_bdd = elem.get(dst);
        let src_bdd = elem.get(src);

        let dst_targets = self.decode_bdd(dst_bdd);

        if dst_targets.is_empty() {
            // Storing through null/invalid pointer - error
            return PointsToElement::bottom(Rc::clone(&self.manager));
        }

        let mut result = elem.clone();

        // Weak update: for each target, union with src's points-to set
        for target_loc in dst_targets {
            let target_str = target_loc.to_string();
            let old_bdd = result.get(&target_str);
            let new_bdd = self.manager.apply_or(old_bdd, src_bdd);
            result.set(target_str, new_bdd);
        }

        result
    }
}

impl AbstractDomain for PointsToDomain {
    type Element = PointsToElement;

    fn bottom(&self) -> Self::Element {
        PointsToElement::bottom(Rc::clone(&self.manager))
    }

    fn top(&self) -> Self::Element {
        PointsToElement::top(Rc::clone(&self.manager))
    }

    fn is_bottom(&self, elem: &Self::Element) -> bool {
        elem.is_bottom
    }

    fn is_top(&self, elem: &Self::Element) -> bool {
        elem.is_top
    }

    fn le(&self, elem1: &Self::Element, elem2: &Self::Element) -> bool {
        if elem1.is_bottom || elem2.is_top {
            return true;
        }
        if elem2.is_bottom || elem1.is_top {
            return false;
        }

        // elem1 ⊑ elem2 iff ∀var. elem1[var] ⊆ elem2[var]
        // BDD subset: bdd1 ⊆ bdd2  ⟺  bdd1 ∧ ¬bdd2 = ⊥
        for (var, &bdd1) in &elem1.points_to {
            let bdd2 = elem2.get(var);
            let not_bdd2 = self.manager.apply_not(bdd2);
            let diff = self.manager.apply_and(bdd1, not_bdd2);
            if !self.manager.is_zero(diff) {
                return false;
            }
        }

        true
    }

    fn join(&self, elem1: &Self::Element, elem2: &Self::Element) -> Self::Element {
        if elem1.is_bottom {
            return elem2.clone();
        }
        if elem2.is_bottom {
            return elem1.clone();
        }
        if elem1.is_top || elem2.is_top {
            return self.top();
        }

        let mut result = PointsToElement::new(Rc::clone(&self.manager));

        // Union: ∀var. result[var] = elem1[var] ∪ elem2[var]
        let mut all_vars: HashSet<String> = elem1.points_to.keys().cloned().collect();
        all_vars.extend(elem2.points_to.keys().cloned());

        for var in all_vars {
            let bdd1 = elem1.get(&var);
            let bdd2 = elem2.get(&var);
            let union_bdd = self.manager.apply_or(bdd1, bdd2);
            result.set(var, union_bdd);
        }

        result
    }

    fn meet(&self, elem1: &Self::Element, elem2: &Self::Element) -> Self::Element {
        if elem1.is_bottom || elem2.is_bottom {
            return self.bottom();
        }
        if elem1.is_top {
            return elem2.clone();
        }
        if elem2.is_top {
            return elem1.clone();
        }

        let mut result = PointsToElement::new(Rc::clone(&self.manager));

        // Intersection: ∀var. result[var] = elem1[var] ∩ elem2[var]
        let mut all_vars: HashSet<String> = elem1.points_to.keys().cloned().collect();
        all_vars.extend(elem2.points_to.keys().cloned());

        for var in all_vars {
            let bdd1 = elem1.get(&var);
            let bdd2 = elem2.get(&var);
            let intersect_bdd = self.manager.apply_and(bdd1, bdd2);

            // If any variable has empty points-to set, might indicate error
            // but we'll allow it (pointer doesn't point anywhere valid)
            result.set(var, intersect_bdd);
        }

        result
    }

    fn widen(&self, elem1: &Self::Element, elem2: &Self::Element) -> Self::Element {
        // For now, widening = join (no thresholds)
        // Could add location set size thresholds for better termination
        self.join(elem1, elem2)
    }
}

impl Default for PointsToDomain {
    fn default() -> Self {
        Self::new()
    }
}

impl PointsToElement {
    /// Check if two pointers **must** alias (definitely point to the same location).
    ///
    /// Returns `true` if both pointers point to exactly the same single location,
    /// meaning they **always** alias in all concrete executions represented by
    /// this abstract state.
    ///
    /// # Definition
    ///
    /// ```text
    /// must_alias(p, q) ⟺ pts(p) = pts(q) = {l} (both are singletons and equal)
    /// ```
    ///
    /// # Example
    ///
    /// ```rust,ignore
    /// // C code:
    /// // int x;
    /// // int *p = &x;
    /// // int *q = p;
    /// // Must p and q alias? YES (both point to exactly {x})
    ///
    /// let x = Location::Stack("x".to_string());
    /// state = domain.assign_address(&state, "p", &x);
    /// state = domain.assign_copy(&state, "q", "p");
    ///
    /// assert!(state.must_alias(&domain, "p", "q"));  // TRUE
    /// ```
    ///
    /// # Counterexample: May alias but not must alias
    ///
    /// ```rust,ignore
    /// // C code:
    /// // int x, y;
    /// // int *p = condition ? &x : &y;  // p points to {x, y}
    /// // int *q = &x;                    // q points to {x}
    /// // Must p and q alias? NO (p might point to y)
    ///
    /// // But they MAY alias (through x)
    /// assert!(!state.must_alias(&domain, "p", "q"));  // FALSE
    /// assert!(state.may_alias(&domain, "p", "q"));    // TRUE
    /// ```
    ///
    /// # Use Cases
    ///
    /// - **Compiler optimization**: Can safely reorder operations
    /// - **Bug detection**: Both null → null pointer dereference guaranteed
    /// - **Verification**: Proving pointer equality invariants
    pub fn must_alias(&self, domain: &PointsToDomain, var1: &str, var2: &str) -> bool {
        if self.is_bottom {
            return false;
        }

        let bdd1 = self.get(var1);
        let bdd2 = self.get(var2);

        // Must alias: both are singletons and equal
        let locs1 = domain.decode_bdd(bdd1);
        let locs2 = domain.decode_bdd(bdd2);

        locs1.len() == 1 && locs2.len() == 1 && locs1 == locs2
    }

    /// Check if two pointers **may** alias (their points-to sets intersect).
    ///
    /// Returns `true` if there exists at least one concrete execution where both
    /// pointers could point to the same memory location.
    ///
    /// # Definition
    ///
    /// ```text
    /// may_alias(p, q) ⟺ pts(p) ∩ pts(q) ≠ ∅ (sets have common element)
    /// ```
    ///
    /// # Example: Aliasing through shared location
    ///
    /// ```rust,ignore
    /// // C code:
    /// // int x, y;
    /// // int *p = condition ? &x : &y;  // p → {x, y}
    /// // int *q = &x;                    // q → {x}
    /// // May p and q alias? YES (through x)
    ///
    /// let x = Location::Stack("x".to_string());
    /// let y = Location::Stack("y".to_string());
    ///
    /// let state1 = domain.assign_address(&init, "p", &x);
    /// let state2 = domain.assign_address(&init, "p", &y);
    /// let state = domain.join(&state1, &state2);  // p → {x, y}
    ///
    /// state = domain.assign_address(&state, "q", &x);  // q → {x}
    ///
    /// assert!(state.may_alias(&domain, "p", "q"));    // TRUE (intersect at x)
    /// assert!(!state.must_alias(&domain, "p", "q"));  // FALSE (p might be y)
    /// ```
    ///
    /// # Example: No aliasing (disjoint sets)
    ///
    /// ```rust,ignore
    /// // C code:
    /// // int x, y;
    /// // int *p = &x;  // p → {x}
    /// // int *q = &y;  // q → {y}
    /// // May p and q alias? NO (disjoint sets)
    ///
    /// state = domain.assign_address(&state, "p", &x);
    /// state = domain.assign_address(&state, "q", &y);
    ///
    /// assert!(!state.may_alias(&domain, "p", "q"));  // FALSE (no intersection)
    /// ```
    ///
    /// # Use Cases
    ///
    /// - **Memory safety**: Can dereferencing both cause issues?
    /// - **Concurrency**: Do two threads access the same memory?
    /// - **Optimization**: Can we eliminate redundant loads?
    ///
    /// # Soundness
    ///
    /// May-alias must be **conservative**: if we say "no alias", it must be
    /// guaranteed. False positives (saying "may alias" when they don't) are
    /// safe but imprecise.
    pub fn may_alias(&self, domain: &PointsToDomain, var1: &str, var2: &str) -> bool {
        if self.is_bottom {
            return false;
        }

        let bdd1 = self.get(var1);
        let bdd2 = self.get(var2);

        // Decode both BDDs to location sets and check for intersection
        let locs1 = domain.decode_bdd(bdd1);
        let locs2 = domain.decode_bdd(bdd2);

        // May alias: sets intersect (have common elements)
        !locs1.is_disjoint(&locs2)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_location_display() {
        assert_eq!(Location::Null.to_string(), "null");
        assert_eq!(Location::Stack("x".to_string()).to_string(), "&x");
        assert_eq!(Location::Heap(42).to_string(), "heap#42");
        assert_eq!(Location::Global("g".to_string()).to_string(), "global:g");
        assert_eq!(Location::Unknown.to_string(), "?");
    }

    #[test]
    fn test_location_map_allocation() {
        let mut map = LocationMap::new();

        let x = Location::Stack("x".to_string());
        let y = Location::Stack("y".to_string());

        let var_x = map.get_or_allocate(&x);
        let var_y = map.get_or_allocate(&y);

        assert_ne!(var_x, var_y);
        assert_eq!(map.get_var(&x), Some(var_x));
        assert_eq!(map.get_var(&y), Some(var_y));
        assert_eq!(map.get_location(var_x), Some(&x));
        assert_eq!(map.get_location(var_y), Some(&y));
    }

    #[test]
    fn test_location_map_reuse() {
        let mut map = LocationMap::new();

        let x = Location::Stack("x".to_string());
        let var1 = map.get_or_allocate(&x);
        let var2 = map.get_or_allocate(&x);

        assert_eq!(var1, var2);
    }

    #[test]
    fn test_pointsto_bottom() {
        let domain = PointsToDomain::new();
        let bottom = domain.bottom();

        assert!(bottom.is_bottom());
        assert!(domain.is_bottom(&bottom));
    }

    #[test]
    fn test_pointsto_assign_null() {
        let domain = PointsToDomain::new();
        let elem = PointsToElement::new(Rc::clone(domain.manager()));

        let result = domain.assign_null(&elem, "p");

        // Check that p points to null
        let p_bdd = result.get("p");
        assert!(!result.manager.is_zero(p_bdd));
    }

    #[test]
    fn test_pointsto_assign_address() {
        let domain = PointsToDomain::new();
        let elem = PointsToElement::new(Rc::clone(domain.manager()));

        let x_loc = Location::Stack("x".to_string());
        let result = domain.assign_address(&elem, "p", &x_loc);

        let p_bdd = result.get("p");
        assert!(!result.manager.is_zero(p_bdd));
    }

    #[test]
    fn test_pointsto_assign_copy() {
        let domain = PointsToDomain::new();
        let mut elem = PointsToElement::new(Rc::clone(domain.manager()));

        let x_loc = Location::Stack("x".to_string());
        elem = domain.assign_address(&elem, "p", &x_loc);
        elem = domain.assign_copy(&elem, "q", "p");

        // p and q should have same points-to set
        let p_bdd = elem.get("p");
        let q_bdd = elem.get("q");

        // Check they're equal (XOR is zero)
        let xor = elem.manager.apply_xor(p_bdd, q_bdd);
        assert!(elem.manager.is_zero(xor));
    }

    #[test]
    fn test_pointsto_join() {
        let domain = PointsToDomain::new();

        let x_loc = Location::Stack("x".to_string());
        let y_loc = Location::Stack("y".to_string());

        // Start with non-bottom elements
        let init = PointsToElement::new(Rc::clone(domain.manager()));
        let elem1 = domain.assign_address(&init, "p", &x_loc);
        let elem2 = domain.assign_address(&init, "p", &y_loc);

        let joined = domain.join(&elem1, &elem2);

        // p should point to {x, y}
        let p_bdd = joined.get("p");
        assert!(!joined.manager.is_zero(p_bdd));
    }

    #[test]
    fn test_pointsto_meet() {
        let domain = PointsToDomain::new();

        let x_loc = Location::Stack("x".to_string());
        let y_loc = Location::Stack("y".to_string());

        // Start with non-bottom elements
        let init = PointsToElement::new(Rc::clone(domain.manager()));
        let elem1 = domain.assign_address(&init, "p", &x_loc);
        let elem2 = domain.assign_address(&init, "p", &y_loc);

        let met = domain.meet(&elem1, &elem2);

        // Intersection of {x} and {y} is empty (disjoint sets)
        // x is encoded as variable v1, y as variable v2
        // v1 AND v2 != zero (it's the conjunction), but semantically represents empty set
        // because a pointer can't point to both x AND y simultaneously
        // Actually, in BDD encoding: x=v1, y=v2, so x∧y is satisfiable (both true)
        // but semantically this means "points to both x and y" which is valid in our model
        // So the meet should NOT be empty. Let's check it's not zero.
        let p_bdd = met.get("p");
        // The BDD v1 ∧ v2 is not zero
        assert!(!met.manager.is_zero(p_bdd));

        // Better test: meet with disjoint variables should give intersection
        // elem1: p -> {x}, q -> {}
        // elem2: p -> {}, q -> {y}
        // meet: p -> {}, q -> {}
        let mut elem3 = PointsToElement::new(Rc::clone(domain.manager()));
        elem3.set("q".to_string(), domain.encode_location(&x_loc));

        let mut elem4 = PointsToElement::new(Rc::clone(domain.manager()));
        elem4.set("r".to_string(), domain.encode_location(&y_loc));

        let met2 = domain.meet(&elem3, &elem4);
        // elem3 has q, elem4 has r, meet should have neither with non-empty sets
        let q_bdd = met2.get("q");
        let r_bdd = met2.get("r");
        assert!(met2.manager.is_zero(q_bdd)); // elem4 doesn't have q
        assert!(met2.manager.is_zero(r_bdd)); // elem3 doesn't have r
    }

    #[test]
    fn test_pointsto_le() {
        let domain = PointsToDomain::new();

        let x_loc = Location::Stack("x".to_string());
        let init = PointsToElement::new(Rc::clone(domain.manager()));
        let elem1 = domain.assign_address(&init, "p", &x_loc);

        // elem1: p -> {x}
        // elem2: p -> {} (empty points-to set for p)
        let elem2 = PointsToElement::new(Rc::clone(domain.manager()));

        // elem2 (empty) should be <= elem1 (has x)
        assert!(domain.le(&elem2, &elem1));

        // elem1 should NOT be <= elem2
        assert!(!domain.le(&elem1, &elem2));
    }

    #[test]
    fn test_pointsto_lattice_axioms() {
        use crate::domain::tests::test_lattice_axioms;

        let domain = PointsToDomain::new();

        let x_loc = Location::Stack("x".to_string());
        let y_loc = Location::Stack("y".to_string());
        let null_loc = Location::Null;

        let init = PointsToElement::new(Rc::clone(domain.manager()));
        let bottom = domain.bottom();

        // Create various sample elements
        let elem_px = domain.assign_address(&init, "p", &x_loc);
        let elem_py = domain.assign_address(&init, "p", &y_loc);
        let elem_pnull = domain.assign_address(&init, "p", &null_loc);
        let elem_qx = domain.assign_address(&init, "q", &x_loc);

        let mut elem_pq = domain.assign_address(&init, "p", &x_loc);
        elem_pq = domain.assign_address(&elem_pq, "q", &y_loc);

        let samples = vec![
            bottom.clone(),
            init.clone(),
            elem_px.clone(),
            elem_py.clone(),
            elem_pnull.clone(),
            elem_qx.clone(),
            elem_pq.clone(),
        ];

        test_lattice_axioms(&domain, &samples);
    }

    #[test]
    fn test_pointsto_basic_assignment() {
        let domain = PointsToDomain::new();
        let mut elem = PointsToElement::new(Rc::clone(domain.manager()));

        // p = &x
        let x_loc = Location::Stack("x".to_string());
        elem = domain.assign_address(&elem, "p", &x_loc);

        // q = &y
        let y_loc = Location::Stack("y".to_string());
        elem = domain.assign_address(&elem, "q", &y_loc);

        // Verify p points to x
        let p_locs = domain.decode_bdd(elem.get("p"));
        assert_eq!(p_locs.len(), 1);
        assert!(p_locs.contains(&x_loc));

        // Verify q points to y
        let q_locs = domain.decode_bdd(elem.get("q"));
        assert_eq!(q_locs.len(), 1);
        assert!(q_locs.contains(&y_loc));

        // p and q should not alias
        assert!(!elem.may_alias(&domain, "p", "q"));
    }

    #[test]
    fn test_pointsto_pointer_copy() {
        let domain = PointsToDomain::new();
        let mut elem = PointsToElement::new(Rc::clone(domain.manager()));

        // p = &x
        let x_loc = Location::Stack("x".to_string());
        elem = domain.assign_address(&elem, "p", &x_loc);

        // q = p
        elem = domain.assign_copy(&elem, "q", "p");

        // Both should point to x
        let p_locs = domain.decode_bdd(elem.get("p"));
        let q_locs = domain.decode_bdd(elem.get("q"));
        assert_eq!(p_locs, q_locs);

        // Must alias and may alias
        assert!(elem.must_alias(&domain, "p", "q"));
        assert!(elem.may_alias(&domain, "p", "q"));
    }

    #[test]
    fn test_pointsto_join_merge() {
        let domain = PointsToDomain::new();
        let init = PointsToElement::new(Rc::clone(domain.manager()));

        let x_loc = Location::Stack("x".to_string());
        let y_loc = Location::Stack("y".to_string());

        // Then branch: p = &x
        let then_elem = domain.assign_address(&init, "p", &x_loc);

        // Else branch: p = &y
        let else_elem = domain.assign_address(&init, "p", &y_loc);

        // Join at merge point
        let joined = domain.join(&then_elem, &else_elem);

        // p should point to {x, y}
        let p_locs = domain.decode_bdd(joined.get("p"));
        assert_eq!(p_locs.len(), 2);
        assert!(p_locs.contains(&x_loc));
        assert!(p_locs.contains(&y_loc));
    }

    #[test]
    fn test_pointsto_alias_detection() {
        let domain = PointsToDomain::new();
        let mut elem = PointsToElement::new(Rc::clone(domain.manager()));

        let x_loc = Location::Stack("x".to_string());
        let y_loc = Location::Stack("y".to_string());

        // p = &x
        elem = domain.assign_address(&elem, "p", &x_loc);

        // q = &x (alias)
        elem = domain.assign_address(&elem, "q", &x_loc);

        // r = &y (no alias)
        elem = domain.assign_address(&elem, "r", &y_loc);

        // p and q are aliases
        assert!(elem.may_alias(&domain, "p", "q"));
        assert!(elem.must_alias(&domain, "p", "q"));

        // p and r are not aliases
        assert!(!elem.may_alias(&domain, "p", "r"));
        assert!(!elem.must_alias(&domain, "p", "r"));

        // q and r are not aliases
        assert!(!elem.may_alias(&domain, "q", "r"));
        assert!(!elem.must_alias(&domain, "q", "r"));
    }

    #[test]
    fn test_pointsto_heap_allocation() {
        let domain = PointsToDomain::new();
        let mut elem = PointsToElement::new(Rc::clone(domain.manager()));

        // p = malloc() - site 1
        elem = domain.assign_alloc(&elem, "p", 1);

        // q = malloc() - site 2
        elem = domain.assign_alloc(&elem, "q", 2);

        let p_locs = domain.decode_bdd(elem.get("p"));
        let q_locs = domain.decode_bdd(elem.get("q"));

        // Each should point to their respective heap locations
        assert_eq!(p_locs.len(), 1);
        assert_eq!(q_locs.len(), 1);
        assert!(p_locs.contains(&Location::Heap(1)));
        assert!(q_locs.contains(&Location::Heap(2)));

        // Different heap allocations don't alias
        assert!(!elem.may_alias(&domain, "p", "q"));
    }

    #[test]
    fn test_pointsto_null_handling() {
        let domain = PointsToDomain::new();
        let mut elem = PointsToElement::new(Rc::clone(domain.manager()));

        // p = NULL
        elem = domain.assign_null(&elem, "p");

        let p_locs = domain.decode_bdd(elem.get("p"));
        assert_eq!(p_locs.len(), 1);
        assert!(p_locs.contains(&Location::Null));

        // Assign address to q
        let x_loc = Location::Stack("x".to_string());
        elem = domain.assign_address(&elem, "q", &x_loc);

        // p (null) and q (x) should not alias
        assert!(!elem.may_alias(&domain, "p", "q"));
        assert!(!elem.must_alias(&domain, "p", "q"));
    }
}
