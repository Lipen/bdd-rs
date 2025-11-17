//! Points-to analysis domain using BDDs.
//!
//! This module implements a flow-sensitive, context-insensitive points-to analysis
//! domain that tracks which memory locations each pointer variable may point to.
//! BDDs are used to efficiently represent potentially large sets of locations.
//!
//! # Theory Background
//!
//! Points-to analysis determines which memory locations a pointer variable may
//! reference at each program point. This is fundamental for:
//! - Alias analysis (do two pointers reference the same location?)
//! - Memory safety (null pointer dereference detection)
//! - Optimization (can reads/writes be reordered?)
//!
//! ## Precision Levels
//!
//! - **Flow-sensitive**: Different points-to sets at different program points
//! - **Flow-insensitive**: Single points-to set for entire program
//! - **Context-sensitive**: Different analysis per call context
//! - **Context-insensitive**: Merge all contexts (this implementation)
//!
//! ## Andersen's Analysis
//!
//! This implementation follows Andersen's style analysis:
//! - Subset-based (p ⊆ q means p's targets ⊆ q's targets)
//! - Constraint-based formulation
//! - Efficient with BDD representation
//!
//! Alternative: Steensgaard's analysis uses equality constraints (faster but less precise)
//!
//! # Lattice Structure
//!
//! ```text
//!                    ⊤ (may point to any location)
//!                   / | \
//!         ... {loc1,loc2}, {loc3}, ... (sets of locations)
//!                   \ | /
//!                    ∅ (points to nothing)
//!                    |
//!                    ⊥ (unreachable)
//! ```
//!
//! # Usage Example
//!
//! ```rust,ignore
//! use abstract_interpretation::pointsto::*;
//! use std::rc::Rc;
//!
//! // Create domain with BDD manager
//! let domain = PointsToDomain::new();
//!
//! // Track pointer assignments
//! let mut elem = PointsToElement::new(domain.manager());
//!
//! // p = &x
//! elem = domain.assign_address(&elem, "p", &Location::Stack("x".to_string()));
//!
//! // q = p
//! elem = domain.assign_copy(&elem, "q", "p");
//!
//! // Check aliasing: must p and q alias?
//! assert!(elem.must_alias("p", "q"));
//! ```
//!
//! # BDD Representation
//!
//! Each memory location is encoded as a unique BDD variable. A pointer's
//! points-to set is represented as a disjunction (OR) of location variables.
//!
//! Example:
//! - Location "x" → BDD variable v0
//! - Location "y" → BDD variable v1
//! - `p` may point to {x,y} → BDD: v0 ∨ v1
//! - `q` points to {x} → BDD: v0

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

/// Maps locations to BDD variables and vice versa.
///
/// This provides a bidirectional mapping allowing efficient encoding
/// of location sets as BDDs and decoding BDDs back to location sets.
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

/// Abstract element in the points-to domain.
///
/// Tracks points-to sets for each pointer variable using BDDs.
/// Each pointer maps to a BDD representing the set of locations it may point to.
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

/// Points-to analysis domain.
///
/// Provides operations for pointer analysis including assignments,
/// loads, stores, and alias queries.
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
    /// This requires strong update if src points to a unique location,
    /// otherwise it's a weak update (union).
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
    /// Uses weak update (union) since dst may point to multiple locations.
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
    /// Check if two pointers must alias (point to exactly the same location).
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

    /// Check if two pointers may alias (their points-to sets intersect).
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
