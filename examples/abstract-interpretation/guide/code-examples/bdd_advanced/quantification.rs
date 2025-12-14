//! Chapter 4: BDD Quantification
//!
//! This example demonstrates existential and universal quantification from Chapter 4.
//! Shows how quantifiers eliminate variables while preserving logical relationships.

use ananke_bdd::bdd::Bdd;

fn main() {
    println!("=== BDD Quantification Example ===\n");

    let bdd = Bdd::default();
    let x = bdd.mk_var(1);
    let y = bdd.mk_var(2);
    let z = bdd.mk_var(3);

    // Existential quantification: ∃x. (x ∧ y)
    println!("Existential quantification:");
    println!("  f = x ∧ y");
    let f = bdd.apply_and(x, y);

    println!("  ∃x. (x ∧ y) = y");
    let exists_x = bdd.exists(f, &[1]); // Quantify out variable 1 (x)
    println!("  Result equals y: {}\n", exists_x == y);

    // Explanation: ∃x. (x ∧ y) = (false ∧ y) ∨ (true ∧ y) = false ∨ y = y

    // Universal quantification: ∀x. (x ∨ y)
    println!("Universal quantification:");
    println!("  f = x ∨ y");
    let f = bdd.apply_or(x, y);

    println!("  ∀x. (x ∨ y) = y");
    let forall_x = bdd.forall(f, &[1]);
    println!("  Result equals y: {}\n", forall_x == y);

    // Explanation: ∀x. (x ∨ y) = (false ∨ y) ∧ (true ∨ y) = y ∧ true = y

    // More complex example
    println!("Complex example: f(x,y,z) = (x ∧ y) ∨ z");
    let f = bdd.apply_or(bdd.apply_and(x, y), z);

    println!("  ∃x. f = (false ∧ y) ∨ z ∨ (true ∧ y) ∨ z");
    println!("        = z ∨ y ∨ z = y ∨ z");
    let exists_x_f = bdd.exists(f, &[1]);
    let expected = bdd.apply_or(y, z);
    println!("  Result equals y ∨ z: {}\n", exists_x_f == expected);

    println!("  ∀y. f = (x ∧ false) ∨ z ∧ (x ∧ true) ∨ z");
    println!("        = z ∧ (x ∨ z) = z");
    let forall_y_f = bdd.forall(f, &[2]);
    println!("  Result equals z: {}\n", forall_y_f == z);

    // Quantifier duality: ∀x. φ = ¬∃x. ¬φ
    println!("Quantifier duality:");
    println!("  ∀x. φ = ¬∃x. ¬φ");
    let phi = bdd.apply_or(x, y);
    let forall_version = bdd.forall(phi, &[1]);
    let exists_version = bdd.apply_not(bdd.exists(bdd.apply_not(phi), &[1]));
    println!("  Both versions equal: {}\n", forall_version == exists_version);

    // Eliminating multiple variables
    println!("Eliminating multiple variables:");
    println!("  f = (x ∧ y) ∨ (y ∧ z)");
    let f = bdd.apply_or(bdd.apply_and(x, y), bdd.apply_and(y, z));

    println!("  ∃x. ∃y. f");
    let elim = bdd.exists(f, &[1, 2]); // Eliminate x and y
    println!(
        "  After eliminating x and y: result = {}",
        if elim == z {
            "z"
        } else if bdd.is_one(elim) {
            "true"
        } else {
            "complex"
        }
    );

    println!("\n=== Summary ===");
    println!("✓ Existential quantification: ∃x. f = f[x←0] ∨ f[x←1]");
    println!("✓ Universal quantification: ∀x. f = f[x←0] ∧ f[x←1]");
    println!("✓ Quantifiers eliminate variables");
    println!("✓ Duality: ∀x. φ = ¬∃x. ¬φ");
}
