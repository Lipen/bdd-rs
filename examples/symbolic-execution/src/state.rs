//! Symbolic state representation using BDDs.
//!
//! A symbolic state consists of:
//! - Variable mapping: bidirectional mapping between program variables and BDD variable indices
//! - Symbolic store: each program variable has an associated BDD expression
//! - Path condition: a BDD representing constraints on the execution path

use std::collections::HashMap;

use ananke_bdd::bdd::Bdd;
use ananke_bdd::reference::Ref;

use crate::ast::{Expr, Var};

/// Bidirectional mapping between program variables and BDD variable indices (compact 1..n)
#[derive(Debug, Clone)]
pub struct VarMap {
    var_to_index: HashMap<Var, u32>,
    index_to_var: HashMap<u32, Var>,
    next_index: u32,
}

impl VarMap {
    pub fn new() -> Self {
        VarMap {
            var_to_index: HashMap::new(),
            index_to_var: HashMap::new(),
            next_index: 1, // BDD variable indices start at 1
        }
    }

    /// Get or allocate a BDD variable index for a program variable
    pub fn get_or_create(&mut self, var: &Var) -> u32 {
        if let Some(&idx) = self.var_to_index.get(var) {
            idx
        } else {
            let idx = self.next_index;
            self.next_index += 1;
            self.var_to_index.insert(var.clone(), idx);
            self.index_to_var.insert(idx, var.clone());
            idx
        }
    }

    /// Get the BDD variable index for a program variable (if it exists)
    pub fn get_index(&self, var: &Var) -> Option<u32> {
        self.var_to_index.get(var).copied()
    }

    /// Get the program variable for a BDD variable index (if it exists)
    pub fn get_var(&self, index: u32) -> Option<&Var> {
        self.index_to_var.get(&index)
    }
}

impl Default for VarMap {
    fn default() -> Self {
        Self::new()
    }
}

/// Symbolic state: maps program variables to BDD expressions
#[derive(Debug, Clone)]
pub struct SymbolicState {
    bdd: *const Bdd,
    /// Bidirectional mapping between program variables and BDD variable indices
    var_map: VarMap,
    /// Maps program variables to their symbolic values (BDD refs)
    store: HashMap<Var, Ref>,
    /// Path condition: conjunction of all branch conditions taken
    path_condition: Ref,
    /// Exception value thrown (used when jumping to catch block)
    exception_value: Option<Ref>,
    /// Original symbolic values for input variables (before any mutations)
    /// Maps input var -> its BDD variable (not its current value in store)
    input_symbolic_values: HashMap<Var, Ref>,
}

impl SymbolicState {
    pub fn new(bdd: &Bdd) -> Self {
        SymbolicState {
            bdd: bdd as *const Bdd,
            var_map: VarMap::new(),
            store: HashMap::new(),
            path_condition: bdd.one(),
            exception_value: None,
            input_symbolic_values: HashMap::new(),
        }
    }

    /// Get the BDD reference
    pub fn bdd(&self) -> &Bdd {
        unsafe { &*self.bdd }
    }

    /// Get or allocate a BDD variable index for a program variable
    pub fn get_or_create_index(&mut self, var: &Var) -> u32 {
        self.var_map.get_or_create(var)
    }

    /// Get the program variable name for a BDD variable index (if it exists)
    pub fn get_var_for_index(&self, index: u32) -> Option<&Var> {
        self.var_map.get_var(index)
    }

    /// Mark a variable as an input and save its initial symbolic value
    /// This should be called when first creating symbolic variables for inputs
    pub fn mark_as_input(&mut self, var: &Var) {
        if !self.input_symbolic_values.contains_key(var) {
            // Get or create the BDD variable for this input
            let bdd_var = self.get_or_create_index(var);
            let symbolic_value = self.bdd().mk_var(bdd_var);
            self.input_symbolic_values.insert(var.clone(), symbolic_value);
        }
    }

    /// Get the original symbolic value for an input variable (before any mutations)
    pub fn get_input_symbolic_value(&self, var: &Var) -> Option<Ref> {
        self.input_symbolic_values.get(var).copied()
    }

    /// Set the exception value (used when throwing)
    pub fn set_exception_value(&mut self, value: Ref) {
        self.exception_value = Some(value);
    }

    /// Take the exception value (consumes it)
    pub fn take_exception_value(&mut self) -> Option<Ref> {
        self.exception_value.take()
    }

    /// Get symbolic value of a variable
    pub fn get(&self, var: &Var) -> Option<Ref> {
        self.store.get(var).copied()
    }

    /// Set symbolic value of a variable
    pub fn set(&mut self, var: Var, value: Ref) {
        self.store.insert(var, value);
    }

    /// Get the path condition
    pub fn path_condition(&self) -> Ref {
        self.path_condition
    }

    /// Add a constraint to the path condition
    pub fn add_constraint(&mut self, constraint: Ref) {
        self.path_condition = self.bdd().apply_and(self.path_condition, constraint);
    }

    /// Check if the current path is feasible
    pub fn is_feasible(&self) -> bool {
        !self.bdd().is_zero(self.path_condition)
    }

    /// Get the concrete value of a variable under the current path condition
    /// Returns Some(true) if the variable must be true on this path,
    /// Some(false) if it must be false, or None if it's truly symbolic
    pub fn get_concrete_value(&self, var: &Var) -> Option<bool> {
        if let Some(val) = self.get(var) {
            let bdd = self.bdd();
            let pc = self.path_condition;

            // Check if variable is constrained to a specific value under the path condition
            // var is true if: (val & pc) == pc (i.e., whenever pc holds, val holds)
            // var is false if: (val & pc) == 0 (i.e., val is always false when pc holds)
            let val_and_pc = bdd.apply_and(val, pc);
            if val_and_pc == pc {
                Some(true)
            } else if bdd.is_zero(val_and_pc) {
                Some(false)
            } else {
                None
            }
        } else {
            None
        }
    }

    /// Evaluate an expression to a BDD
    pub fn eval_expr(&mut self, expr: &Expr) -> Ref {
        match expr {
            Expr::Lit(true) => self.bdd().one(),
            Expr::Lit(false) => self.bdd().zero(),
            Expr::Var(v) => {
                // Get or create symbolic variable
                if let Some(val) = self.get(v) {
                    val
                } else {
                    // Allocate BDD variable for this program variable
                    let bdd_var = self.get_or_create_index(v);
                    let var_ref = self.bdd().mk_var(bdd_var);
                    self.set(v.clone(), var_ref);
                    var_ref
                }
            }
            Expr::Not(e) => {
                let e_val = self.eval_expr(e);
                self.bdd().apply_not(e_val)
            }
            Expr::And(l, r) => {
                let l_val = self.eval_expr(l);
                let r_val = self.eval_expr(r);
                self.bdd().apply_and(l_val, r_val)
            }
            Expr::Or(l, r) => {
                let l_val = self.eval_expr(l);
                let r_val = self.eval_expr(r);
                self.bdd().apply_or(l_val, r_val)
            }
            Expr::Xor(l, r) => {
                let l_val = self.eval_expr(l);
                let r_val = self.eval_expr(r);
                self.bdd().apply_xor(l_val, r_val)
            }
            Expr::Implies(l, r) => {
                let l_val = self.eval_expr(l);
                let r_val = self.eval_expr(r);
                self.bdd().apply_imply(l_val, r_val)
            }
            Expr::Eq(l, r) => {
                let l_val = self.eval_expr(l);
                let r_val = self.eval_expr(r);
                self.bdd().apply_eq(l_val, r_val)
            }
        }
    }

    /// Clone the state (for branching)
    pub fn clone_state(&self) -> Self {
        SymbolicState {
            bdd: self.bdd,
            var_map: self.var_map.clone(),
            store: self.store.clone(),
            path_condition: self.path_condition,
            exception_value: self.exception_value,
            input_symbolic_values: self.input_symbolic_values.clone(),
        }
    }

    /// Get all program variables
    pub fn vars(&self) -> impl Iterator<Item = &Var> {
        self.store.keys()
    }
}
