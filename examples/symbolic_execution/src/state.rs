//! Symbolic state representation using BDDs.
//!
//! A symbolic state consists of:
//! - Variable mapping: each program variable is mapped to a BDD variable index
//! - Symbolic store: each program variable has an associated BDD expression
//! - Path condition: a BDD representing constraints on the execution path

use std::collections::HashMap;

use bdd_rs::bdd::Bdd;
use bdd_rs::reference::Ref;

use crate::ast::{Expr, Var};

/// Maps program variables to BDD variable indices
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
            next_index: 1, // BDD indices start at 1
        }
    }

    /// Get or create a BDD variable index for a program variable
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

    /// Get BDD variable index for a program variable
    pub fn get(&self, var: &Var) -> Option<u32> {
        self.var_to_index.get(var).copied()
    }

    /// Get program variable name for a BDD index
    pub fn get_var(&self, index: u32) -> Option<&Var> {
        self.index_to_var.get(&index)
    }

    /// Get all variables
    pub fn vars(&self) -> impl Iterator<Item = &Var> {
        self.var_to_index.keys()
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
    var_map: VarMap,
    /// Maps program variables to their symbolic values (BDD refs)
    store: HashMap<Var, Ref>,
    /// Path condition: conjunction of all branch conditions taken
    path_condition: Ref,
}

impl SymbolicState {
    pub fn new(bdd: &Bdd) -> Self {
        SymbolicState {
            bdd: bdd as *const Bdd,
            var_map: VarMap::new(),
            store: HashMap::new(),
            path_condition: bdd.one,
        }
    }

    /// Get the BDD reference
    pub fn bdd(&self) -> &Bdd {
        unsafe { &*self.bdd }
    }

    /// Get the variable map
    pub fn var_map(&self) -> &VarMap {
        &self.var_map
    }

    /// Get mutable variable map
    pub fn var_map_mut(&mut self) -> &mut VarMap {
        &mut self.var_map
    }

    /// Get the path condition
    pub fn path_condition(&self) -> Ref {
        self.path_condition
    }

    /// Get symbolic value of a variable
    pub fn get(&self, var: &Var) -> Option<Ref> {
        self.store.get(var).copied()
    }

    /// Set symbolic value of a variable
    pub fn set(&mut self, var: Var, value: Ref) {
        self.store.insert(var, value);
    }

    /// Add a constraint to the path condition
    pub fn add_constraint(&mut self, constraint: Ref) {
        self.path_condition = self.bdd().apply_and(self.path_condition, constraint);
    }

    /// Check if the current path is feasible
    pub fn is_feasible(&self) -> bool {
        !self.bdd().is_zero(self.path_condition)
    }

    /// Evaluate an expression to a BDD
    pub fn eval_expr(&mut self, expr: &Expr) -> Ref {
        match expr {
            Expr::Lit(true) => self.bdd().one,
            Expr::Lit(false) => self.bdd().zero,
            Expr::Var(v) => {
                // Get or create symbolic variable
                if let Some(val) = self.get(v) {
                    val
                } else {
                    // Create fresh symbolic variable
                    let idx = self.var_map.get_or_create(v);
                    let var_ref = self.bdd().mk_var(idx);
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
        }
    }

    /// Get all program variables
    pub fn vars(&self) -> impl Iterator<Item = &Var> {
        self.var_map.vars()
    }
}
