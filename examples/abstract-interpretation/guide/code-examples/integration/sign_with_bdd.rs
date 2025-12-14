//! Integrating BDDs with Abstract Domains: Path-Sensitive Analysis
//!
//! **Guide Reference:** Part I, Chapter 5 - "Combining BDDs with Abstract Domains"
//!
//! This example demonstrates the **core integration pattern** for path-sensitive
//! abstract interpretation: pairing abstract domains (Sign) with BDD-based
//! path conditions.
//!
//! ## The Integration Pattern
//!
//! Traditional abstract interpretation loses precision at control flow joins.
//! Path-sensitive solution: Track each path separately with BDDs.
//!
//! ## Key Components
//!
//! 1. **Path Condition (BDD)**: Formula characterizing which paths reach this state
//! 2. **Abstract Environment (Map)**: Variable → Abstract value for this path
//! 3. **Path Splitting**: Branch creates multiple states with refined conditions
//! 4. **Feasibility Checking**: Discard paths with contradictory conditions
//!
//! ## Expected Output
//!
//! Run with: `cargo run --example sign_with_bdd`
//!
//! Demonstrates path splitting, path merging, infeasible path detection,
//! and the precision gains from path-sensitive analysis.

use std::collections::HashMap;
use std::rc::Rc;

use ananke_bdd::bdd::Bdd;
use ananke_bdd::reference::Ref;

/// Sign domain from Chapter 1
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
enum Sign {
    #[allow(dead_code)]
    Bot,
    Neg,
    #[allow(dead_code)]
    Zero,
    Pos,
    Top,
}

impl Sign {
    fn join(&self, other: &Self) -> Self {
        use Sign::*;
        match (self, other) {
            (Bot, x) | (x, Bot) => *x,
            (x, y) if x == y => *x,
            _ => Top,
        }
    }
}

/// Path-sensitive analysis state combining BDD control with sign data
struct PathSensitiveState {
    bdd: Rc<Bdd>,
    path: Ref,                  // BDD representing path condition
    env: HashMap<String, Sign>, // Variable → Sign mapping
    next_var: u32,              // Next BDD variable to allocate
}

impl PathSensitiveState {
    fn new(bdd: Rc<Bdd>) -> Self {
        Self {
            bdd: bdd.clone(),
            path: bdd.mk_true(), // Initially: all paths feasible
            env: HashMap::new(),
            next_var: 1,
        }
    }

    /// Check if current path is feasible
    fn is_feasible(&self) -> bool {
        !self.bdd.is_zero(self.path)
    }

    /// Assign a value to a variable
    fn assign(&mut self, var: &str, value: Sign) {
        self.env.insert(var.to_string(), value);
    }

    /// Get the sign of a variable
    fn get(&self, var: &str) -> Sign {
        self.env.get(var).copied().unwrap_or(Sign::Top)
    }

    /// Branch on a condition, splitting into two states
    fn branch(&self) -> (Self, Self) {
        // Allocate fresh BDD variable for this condition
        let cond_var = self.next_var;
        let cond_bdd = self.bdd.mk_var(cond_var);

        // True branch: path ∧ condition
        let true_path = self.bdd.apply_and(self.path, cond_bdd);
        let true_state = Self {
            bdd: self.bdd.clone(),
            path: true_path,
            env: self.env.clone(),
            next_var: self.next_var + 1,
        };

        // False branch: path ∧ ¬condition
        let not_cond = self.bdd.apply_not(cond_bdd);
        let false_path = self.bdd.apply_and(self.path, not_cond);
        let false_state = Self {
            bdd: self.bdd.clone(),
            path: false_path,
            env: self.env.clone(),
            next_var: self.next_var + 1,
        };

        (true_state, false_state)
    }

    /// Join two states (at merge point)
    fn join(&self, other: &Self) -> Self {
        // Merge path conditions: path₁ ∨ path₂
        let merged_path = self.bdd.apply_or(self.path, other.path);

        // Join data environments
        let mut merged_env = HashMap::new();
        let all_vars: std::collections::HashSet<_> = self.env.keys().chain(other.env.keys()).collect();

        for var in all_vars {
            let val1 = self.get(var);
            let val2 = other.get(var);
            merged_env.insert(var.to_string(), val1.join(&val2));
        }

        Self {
            bdd: self.bdd.clone(),
            path: merged_path,
            env: merged_env,
            next_var: self.next_var.max(other.next_var),
        }
    }
}

fn main() {
    println!("=== Path-Sensitive Sign Analysis ===\n");

    let bdd = Rc::new(Bdd::default());

    // Example: if-else with different assignments
    println!("Analyzing:");
    println!("  let mut x;");
    println!("  if condition {{");
    println!("      x = 5;");
    println!("  }} else {{");
    println!("      x = -3;");
    println!("  }}\n");

    let initial = PathSensitiveState::new(bdd.clone());

    // Branch on condition
    let (mut true_branch, mut false_branch) = initial.branch();
    println!("Branched on condition:");
    println!("  True branch feasible: {}", true_branch.is_feasible());
    println!("  False branch feasible: {}\n", false_branch.is_feasible());

    // True branch: x = 5 (Pos)
    true_branch.assign("x", Sign::Pos);
    println!("True branch: x = 5");
    println!("  x = {:?}\n", true_branch.get("x"));

    // False branch: x = -3 (Neg)
    false_branch.assign("x", Sign::Neg);
    println!("False branch: x = -3");
    println!("  x = {:?}\n", false_branch.get("x"));

    // Join at merge point
    let merged = true_branch.join(&false_branch);
    println!("After merge:");
    println!("  x = {:?} (lost precision - could be Pos or Neg)\n", merged.get("x"));

    // Path-sensitive maintains separate invariants
    println!("=== Path-Sensitive Advantage ===");
    println!("Within true branch:");
    println!("  We know x = Pos with certainty");
    println!("  Can prove: x > 0");
    println!("\nWithin false branch:");
    println!("  We know x = Neg with certainty");
    println!("  Can prove: x < 0");
    println!("\nPath-insensitive analysis would only know:");
    println!("  x = Top (unknown)");
    println!("  Cannot prove either property");

    println!("\n=== Summary ===");
    println!("✓ BDD tracks which paths are feasible");
    println!("✓ Sign domain tracks value properties");
    println!("✓ Combined: path-sensitive analysis");
    println!("✓ More precise than path-insensitive");
}
