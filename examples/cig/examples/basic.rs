//! Basic CIG usage example.
//!
//! This example demonstrates:
//! - Building CIGs from truth tables
//! - Checking functional equivalence
//! - Displaying CIG structure
//!
//! Run with: cargo run --example basic

use cig::{CigBuilder, TruthTable, Var};

fn main() {
    println!("═══════════════════════════════════════════════════════════════");
    println!("     Canonical Interaction Graph (CIG) - Basic Example");
    println!("═══════════════════════════════════════════════════════════════\n");

    let mut builder = CigBuilder::new();

    // Example 1: Simple AND function
    println!("Example 1: AND function (x₁ ∧ x₂)");
    println!("─────────────────────────────────");
    let f_and = TruthTable::from_expr(2, |x| x[0] && x[1]);
    let cig_and = builder.build(&f_and);
    println!("{}", cig_and);
    println!("Size: {} nodes", cig_and.size());
    println!("Depth: {}", cig_and.depth());
    println!();

    // Example 2: XOR function (separable)
    println!("Example 2: XOR function (x₁ ⊕ x₂)");
    println!("──────────────────────────────────");
    let f_xor = TruthTable::from_expr(2, |x| x[0] ^ x[1]);
    let cig_xor = builder.build(&f_xor);
    println!("{}", cig_xor);
    println!("Size: {} nodes", cig_xor.size());
    println!();

    // Example 3: Equivalence checking
    println!("Example 3: Equivalence Checking");
    println!("───────────────────────────────");

    // De Morgan's law: ¬(x ∧ y) = ¬x ∨ ¬y
    let f1 = TruthTable::from_expr(2, |x| !(x[0] && x[1]));
    let f2 = TruthTable::from_expr(2, |x| !x[0] || !x[1]);

    let cig1 = builder.build(&f1);
    let cig2 = builder.build(&f2);

    println!("f₁ = ¬(x₁ ∧ x₂)");
    println!("f₂ = ¬x₁ ∨ ¬x₂");
    println!();
    println!("f₁ ≡ f₂ (De Morgan): {}", cig1.equivalent(&cig2));
    assert!(cig1.equivalent(&cig2), "De Morgan's law should hold");
    println!();

    // Example 4: Three-variable function
    println!("Example 4: Three-variable function");
    println!("───────────────────────────────────");
    let f = TruthTable::from_expr(3, |x| (x[0] && x[1]) || x[2]);
    let cig = builder.build(&f);
    println!("f = (x₁ ∧ x₂) ∨ x₃");
    println!();
    println!("{}", cig);
    println!("Size: {} nodes", cig.size());
    println!("Depth: {}", cig.depth());
    println!("Interaction width: {}", cig.interaction_width());
    println!();

    // Example 5: Variable projection
    println!("Example 5: Variable Projections");
    println!("────────────────────────────────");
    for i in 1..=3 {
        let proj = TruthTable::var(3, Var(i as u32));
        let cig = builder.build(&proj);
        println!("x{} → {:?}", i, cig.root());
    }
    println!();

    // Example 6: Constants
    println!("Example 6: Constants");
    println!("────────────────────");
    let zero = TruthTable::zero(2);
    let one = TruthTable::one(2);
    let cig_zero = builder.build(&zero);
    let cig_one = builder.build(&one);
    println!("0 → {:?}", cig_zero.root());
    println!("1 → {:?}", cig_one.root());
    println!();

    println!("═══════════════════════════════════════════════════════════════");
    println!("                    All assertions passed!");
    println!("═══════════════════════════════════════════════════════════════");
}
