//! Chapter 3: Boolean Operations with BDDs
//!
//! This example demonstrates various boolean operations and their properties.

use ananke_bdd::bdd::Bdd;

fn main() {
    println!("=== Boolean Operations Example ===\n");

    let bdd = Bdd::default();
    let x = bdd.mk_var(1);
    let y = bdd.mk_var(2);
    let z = bdd.mk_var(3);

    // De Morgan's Laws
    println!("De Morgan's Laws:");
    println!("  ¬(x ∧ y) = ¬x ∨ ¬y");
    let left = bdd.apply_not(bdd.apply_and(x, y));
    let right = bdd.apply_or(bdd.apply_not(x), bdd.apply_not(y));
    println!("  Verified: {}\n", left == right);

    println!("  ¬(x ∨ y) = ¬x ∧ ¬y");
    let left = bdd.apply_not(bdd.apply_or(x, y));
    let right = bdd.apply_and(bdd.apply_not(x), bdd.apply_not(y));
    println!("  Verified: {}\n", left == right);

    // Distributive laws
    println!("Distributive Laws:");
    println!("  x ∧ (y ∨ z) = (x ∧ y) ∨ (x ∧ z)");
    let left = bdd.apply_and(x, bdd.apply_or(y, z));
    let right = bdd.apply_or(bdd.apply_and(x, y), bdd.apply_and(x, z));
    println!("  Verified: {}\n", left == right);

    // Absorption laws
    println!("Absorption Laws:");
    println!("  x ∧ (x ∨ y) = x");
    let result = bdd.apply_and(x, bdd.apply_or(x, y));
    println!("  Verified: {}\n", result == x);

    println!("  x ∨ (x ∧ y) = x");
    let result = bdd.apply_or(x, bdd.apply_and(x, y));
    println!("  Verified: {}\n", result == x);

    // XOR properties
    println!("XOR Properties:");
    println!("  x ⊕ x = false");
    println!("  Verified: {}\n", bdd.apply_xor(x, x) == bdd.mk_false());

    println!("  x ⊕ false = x");
    println!("  Verified: {}\n", bdd.apply_xor(x, bdd.mk_false()) == x);

    println!("  x ⊕ y = y ⊕ x (commutative)");
    println!("  Verified: {}\n", bdd.apply_xor(x, y) == bdd.apply_xor(y, x));

    // Implication
    println!("Implication:");
    println!("  (x → y) = ¬x ∨ y");
    let impl1 = bdd.apply_or(bdd.apply_not(x), y);
    println!("  Created x → y\n");

    println!("  (x → y) ∧ x => y (Modus Ponens)");
    let antecedent = bdd.apply_and(impl1, x);
    let implies_y = bdd.apply_or(bdd.apply_not(antecedent), y);
    println!("  Verified: {}\n", implies_y == bdd.mk_true());

    // Satisfiability examples
    println!("Satisfiability:");
    let tru = bdd.mk_true();
    let fals = bdd.mk_false();

    let sat1 = bdd.apply_or(x, y); // Satisfiable
    let sat2 = bdd.apply_and(x, bdd.apply_not(x)); // Unsatisfiable
    let sat3 = bdd.apply_or(bdd.apply_and(x, y), bdd.apply_and(bdd.apply_not(x), z)); // Satisfiable

    println!("  x ∨ y: {}", if sat1 != fals { "SAT" } else { "UNSAT" });
    println!("  x ∧ ¬x: {}", if sat2 != fals { "SAT" } else { "UNSAT" });
    println!("  (x ∧ y) ∨ (¬x ∧ z): {}", if sat3 != fals { "SAT" } else { "UNSAT" });
    println!();

    // Equivalence
    println!("Equivalence (IFF):");
    println!("  x ↔ y = (x → y) ∧ (y → x)");
    let iff1 = bdd.apply_eq(x, y);
    let impl_xy = bdd.apply_or(bdd.apply_not(x), y);
    let impl_yx = bdd.apply_or(bdd.apply_not(y), x);
    let iff2 = bdd.apply_and(impl_xy, impl_yx);
    println!("  Verified: {}\n", iff1 == iff2);

    // Complex formula
    println!("Complex Formula:");
    println!("  f = (x ∧ y) ∨ (¬x ∧ ¬y) ∨ z");
    let f = bdd.apply_or(
        bdd.apply_or(bdd.apply_and(x, y), bdd.apply_and(bdd.apply_not(x), bdd.apply_not(y))),
        z,
    );
    println!("  Created formula");
    println!("  Is tautology: {}", f == tru);
    println!("  Is unsatisfiable: {}", f == fals);
    println!("  Is satisfiable: {}", f != fals);

    println!("\n=== Summary ===");
    println!("✓ Boolean algebra laws verified");
    println!("✓ BDD canonicity enables fast equality checks");
    println!("✓ Complex formulas handled efficiently");
}
