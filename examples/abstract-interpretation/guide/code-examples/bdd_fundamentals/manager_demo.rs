//! BDD Manager Architecture
//!
//! **Guide Reference:** Part I, Chapter 4 - "BDD Programming Essentials"
//!
//! This example explains why BDD libraries use a manager-centric design
//! and demonstrates the key techniques that make BDDs efficient.
//!
//! ## Why a Manager?
//!
//! BDDs achieve efficiency through three key techniques, all managed centrally:
//!
//! 1. **Hash Consing (Unique Table)**: Ensures structural sharing
//!    - Identical subformulas point to same node in memory
//!    - Enables constant-time equality checking (pointer comparison)
//!
//! 2. **Computed Cache (Memoization)**: Avoids recomputation
//!    - Caches results of apply(op, f1, f2)
//!    - Dramatically speeds up repeated operations
//!
//! 3. **Canonical Forms**: Unique representation per function
//!    - Reduction rules eliminate redundant nodes
//!    - Given fixed variable order, each function has ONE BDD
//!
//! ## Manager Responsibilities
//!
//! - **Variable Allocation**: Assigns unique IDs (1-indexed, 0 reserved)
//! - **Node Creation**: Maintains unique table for hash consing
//! - **Operation Application**: Applies boolean operations with caching
//! - **Memory Management**: Reference counting and garbage collection
//!
//! ## Critical Invariant
//!
//! **All BDD operations MUST go through the manager!**
//!
//! The `Ref` type is just a lightweight handle. The manager owns all nodes
//! and maintains their canonicity.
//!
//! ## Expected Output
//!
//! Run with: `cargo run --example bdd_manager`
//!
//! Demonstrates hash consing, computed cache, variable ordering effects,
//! and the performance benefits of the manager architecture.

use bdd_rs::bdd::Bdd;

fn main() {
    println!("=== BDD Manager Architecture ===\n");

    // Create manager
    let bdd = Bdd::default();
    println!("Created BDD manager");
    println!("  Manager handles:");
    println!("    - Unique table (hash consing)");
    println!("    - Computed cache (memoization)");
    println!("    - Variable allocation");
    println!("    - Garbage collection\n");

    // Variable creation (1-indexed, 0 reserved)
    println!("Variable allocation:");
    let x1 = bdd.mk_var(1);
    let x2 = bdd.mk_var(2);
    let x3 = bdd.mk_var(3);
    println!("  Allocated variables: 1, 2, 3");
    println!("  ⚠ Variables are 1-indexed (0 is reserved)\n");

    // Terminal nodes
    println!("Terminal nodes:");
    let _tru = bdd.mk_true();
    let _fals = bdd.mk_false();
    println!("  Created ⊤ (true) and ⊥ (false)");
    println!("  These are shared across all formulas\n");

    // Demonstrate hash consing (structural sharing)
    println!("Hash Consing (Structural Sharing):");
    let f1 = bdd.apply_and(x1, x2);
    let f2 = bdd.apply_and(x1, x2);
    println!("  f1 = x1 ∧ x2");
    println!("  f2 = x1 ∧ x2");
    println!("  Are f1 and f2 the same reference? {}", f1 == f2);
    println!("  => Hash consing ensures identical formulas share nodes\n");

    // Computed cache demonstration
    println!("Computed Cache (Memoization):");
    let a = bdd.apply_and(x1, x2);
    let b = bdd.apply_and(x2, x3);
    println!("  First time: compute a ∧ b");
    let _r1 = bdd.apply_and(a, b);
    println!("  Second time: lookup cached result");
    let _r2 = bdd.apply_and(a, b);
    println!("  Results identical? {}", _r1 == _r2);
    println!("  => Cache avoids recomputation\n");

    // Manager-centric API
    println!("Manager-Centric Operations:");
    println!("  ✓ Correct: bdd.apply_and(f, g)");
    println!("  ✗ Wrong:   f.and(g) // Ref has no such method");
    println!("  All operations must go through manager!\n");

    // Complement edges (internal representation)
    println!("Canonical Form:");
    println!("  BDDs maintain invariants:");
    println!("    1. High edges never negated");
    println!("    2. Complement edges only on low branches");
    println!("    3. Reduced (no redundant nodes)");
    println!("    4. Ordered (variables respect ordering)\n");

    // Statistics
    println!("Operations performed:");
    println!("  - Variable allocations: 3");
    println!("  - Boolean operations: ~6");
    println!("  - Cache hits enable O(1) for repeated queries");

    // Multiple formulas sharing structure
    println!("\nStructure Sharing Example:");
    let f1 = bdd.apply_and(x1, x2);
    let f2 = bdd.apply_or(x1, x2);
    let _f3 = bdd.apply_and(f1, f2);
    println!("  f1 = x1 ∧ x2");
    println!("  f2 = x1 ∨ x2");
    println!("  f3 = f1 ∧ f2");
    println!("  All three formulas share nodes for x1, x2");
    println!("  Manager tracks reference counts for GC\n");

    // Variable ordering (implicit in allocation)
    println!("Variable Ordering:");
    println!("  Current order: 1 < 2 < 3");
    println!("  Order determined by mk_var() calls");
    println!("  Bad ordering => exponential size blow-up");
    println!("  Good ordering => compact representation");
    println!("  (See variable_ordering example for details)\n");

    println!("=== Summary ===");
    println!("✓ Manager centralizes all BDD operations");
    println!("✓ Hash consing ensures canonicity");
    println!("✓ Computed cache provides speed");
    println!("✓ Reference-based API for safety");
}
