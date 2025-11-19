//! Chapter 4: BDD Manager Architecture Demo
//!
//! This example demonstrates the manager-centric design of BDD libraries.
//! All operations go through the manager to maintain canonicity.

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
    let tru = bdd.mk_true();
    let fals = bdd.mk_false();
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
    let r1 = bdd.apply_and(a, b);
    println!("  Second time: lookup cached result");
    let r2 = bdd.apply_and(a, b);
    println!("  Results identical? {}", r1 == r2);
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
    let f3 = bdd.apply_and(f1, f2);
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
