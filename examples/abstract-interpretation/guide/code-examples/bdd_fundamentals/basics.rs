//! BDD Basics: Introduction to Binary Decision Diagrams
//!
//! **Guide Reference:** Part I, Chapter 3 - "Binary Decision Diagrams"
//!
//! This example introduces the fundamental concepts of Binary Decision Diagrams (BDDs),
//! the data structure that enables path-sensitive abstract interpretation.
//!
//! ## What are BDDs?
//!
//! BDDs are canonical representations of boolean functions. Given a fixed variable
//! ordering, each boolean function has a **unique** reduced BDD representation.
//! This enables constant-time equality checking and efficient boolean operations.
//!
//! ## Key Concepts Demonstrated
//!
//! 1. **Variable Creation**: Variables are 1-indexed (0 is reserved for internal use)
//! 2. **Boolean Operations**: AND, OR, NOT, XOR through the BDD manager
//! 3. **Canonicity**: Same formula always yields same BDD (pointer equality!)
//! 4. **Constants**: Special BDDs for true and false
//! 5. **Formula Construction**: Building complex expressions compositionally
//!
//! ## Critical API Invariant
//!
//! **ALL operations MUST go through the `Bdd` manager!**
//!
//! ```rust
//! let bdd = Bdd::default();
//! let x = bdd.mk_var(1);     // ✓ Correct
//! let f = bdd.apply_and(x, y); // ✓ Through manager
//! let f = x.and(y);          // ✗ Wrong: Ref has no such methods
//! ```
//!
//! The manager maintains hash consing to ensure canonical forms.
//!
//! ## Expected Output
//!
//! Run with: `cargo run --example bdd_basics`
//!
//! Demonstrates variable creation, operations, canonicity property,
//! tautology/satisfiability checking, and formula construction.

use ananke_bdd::bdd::Bdd;

fn main() {
    println!("=== BDD Basics Example ===\n");

    let bdd = Bdd::default();

    // Create variables (1-indexed, 0 is reserved)
    println!("Creating variables...");
    let x = bdd.mk_var(1);
    let y = bdd.mk_var(2);
    let z = bdd.mk_var(3);
    println!("  x = var(1), y = var(2), z = var(3)\n");

    // Boolean operations
    println!("Boolean operations:");
    let _and_xy = bdd.apply_and(x, y);
    println!("  x ∧ y created");

    let _or_xy = bdd.apply_or(x, y);
    println!("  x ∨ y created");

    let not_x = bdd.apply_not(x);
    println!("  ¬x created\n");

    // Canonicity: same formula yields same BDD
    println!("Canonicity property:");
    let f1 = bdd.apply_and(x, y);
    let f2 = bdd.apply_and(x, y);
    println!("  f1 = x ∧ y");
    println!("  f2 = x ∧ y");
    println!("  f1 == f2: {} (pointer equality!)\n", f1 == f2);

    // Constants
    println!("Constants:");
    let tru = bdd.mk_true();
    let fals = bdd.mk_false();
    println!("  Created true and false");

    let x_or_true = bdd.apply_or(x, tru);
    println!("  x ∨ true = true: {}", x_or_true == tru);

    let x_and_false = bdd.apply_and(x, fals);
    println!("  x ∧ false = false: {}\n", x_and_false == fals);

    // Building complex formulas
    println!("Complex formula: (x ∧ y) ∨ (¬x ∧ z)");
    let left = bdd.apply_and(x, y);
    let right = bdd.apply_and(not_x, z);
    let formula = bdd.apply_or(left, right);
    println!("  Formula created");
    println!("  Is satisfiable: {}", formula != fals);
    println!("  Is tautology: {}\n", formula == tru);

    // Tautology checking
    println!("Tautology: x ∨ ¬x (Law of Excluded Middle)");
    let lem = bdd.apply_or(x, not_x);
    println!("  Is tautology: {}\n", lem == tru);

    // Unsatisfiable formula
    println!("Unsatisfiable: x ∧ ¬x");
    let unsat = bdd.apply_and(x, not_x);
    println!("  Is unsatisfiable: {}\n", unsat == fals);

    // XOR operation
    println!("XOR: x ⊕ y = (x ∧ ¬y) ∨ (¬x ∧ y)");
    let _xor = bdd.apply_xor(x, y);
    println!("  Created XOR");
    println!("  x ⊕ x = false: {}", bdd.apply_xor(x, x) == fals);
    println!("  x ⊕ false = x: {}", bdd.apply_xor(x, fals) == x);

    println!("\n=== Summary ===");
    println!("✓ Variables created (1-indexed)");
    println!("✓ Boolean operations work");
    println!("✓ Canonicity ensures uniqueness");
    println!("✓ Tautologies and contradictions detected");
}
