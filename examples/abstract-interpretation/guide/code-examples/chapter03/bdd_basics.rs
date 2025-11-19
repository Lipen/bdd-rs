//! Chapter 3: BDD Basics
//!
//! This example demonstrates fundamental BDD operations from Chapter 3.
//! Shows variable creation, boolean operations, and canonicity.

use bdd_rs::bdd::Bdd;

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
    let and_xy = bdd.apply_and(x, y);
    println!("  x ∧ y created");

    let or_xy = bdd.apply_or(x, y);
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
    let xor = bdd.apply_xor(x, y);
    println!("  Created XOR");
    println!("  x ⊕ x = false: {}", bdd.apply_xor(x, x) == fals);
    println!("  x ⊕ false = x: {}", bdd.apply_xor(x, fals) == x);

    println!("\n=== Summary ===");
    println!("✓ Variables created (1-indexed)");
    println!("✓ Boolean operations work");
    println!("✓ Canonicity ensures uniqueness");
    println!("✓ Tautologies and contradictions detected");
}
