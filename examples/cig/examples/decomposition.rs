//! Decomposition example - Understanding the interaction partition.
//!
//! This example shows how CIG decomposes functions into their
//! irreducible interaction components.
//!
//! Run with: cargo run --example decomposition

use cig::{CigBuilder, TruthTable};
use cig::display::{display_tree, compact_notation};
use cig::truth_table::named;

fn main() {
    println!("═══════════════════════════════════════════════════════════════");
    println!("     CIG Decomposition - Interaction Structure Analysis");
    println!("═══════════════════════════════════════════════════════════════\n");

    let mut builder = CigBuilder::new();

    // Example 1: Fully separable (parity)
    println!("┌─────────────────────────────────────────────────────────────┐");
    println!("│              Example 1: Parity (Fully Separable)           │");
    println!("└─────────────────────────────────────────────────────────────┘\n");
    println!("f = x₁ ⊕ x₂ ⊕ x₃ ⊕ x₄\n");
    println!("Each variable is in its own interaction block.");
    println!("Interaction partition: {{x₁}}, {{x₂}}, {{x₃}}, {{x₄}}\n");

    let parity = named::xor_all(4);
    let cig = builder.build(&parity);
    println!("{}", display_tree(&cig));
    println!("Compact: {}\n", compact_notation(&cig));

    // Example 2: Fully irreducible (majority)
    println!("┌─────────────────────────────────────────────────────────────┐");
    println!("│            Example 2: Majority (Fully Irreducible)         │");
    println!("└─────────────────────────────────────────────────────────────┘\n");
    println!("f = MAJ₃(x₁, x₂, x₃) = (x₁∧x₂) ∨ (x₂∧x₃) ∨ (x₁∧x₃)\n");
    println!("All three variables interact irreducibly.");
    println!("Interaction partition: {{x₁, x₂, x₃}}\n");

    let maj = named::majority3();
    let cig = builder.build(&maj);
    println!("{}", display_tree(&cig));
    println!("Compact: {}\n", compact_notation(&cig));

    // Example 3: Hierarchical decomposition
    println!("┌─────────────────────────────────────────────────────────────┐");
    println!("│         Example 3: Hierarchical Decomposition              │");
    println!("└─────────────────────────────────────────────────────────────┘\n");
    println!("f = (x₁ ⊕ x₂) ∧ (x₃ ⊕ x₄)\n");
    println!("Top level: AND separates {{x₁,x₂}} from {{x₃,x₄}}");
    println!("Second level: XOR separates within each block");
    println!("Interaction partition: {{x₁}}, {{x₂}}, {{x₃}}, {{x₄}}\n");

    let composed = TruthTable::from_expr(4, |x| (x[0] ^ x[1]) && (x[2] ^ x[3]));
    let cig = builder.build(&composed);
    println!("{}", display_tree(&cig));
    println!("Compact: {}\n", compact_notation(&cig));

    // Example 4: Multiplexer (irreducible)
    println!("┌─────────────────────────────────────────────────────────────┐");
    println!("│            Example 4: Multiplexer (Irreducible)            │");
    println!("└─────────────────────────────────────────────────────────────┘\n");
    println!("f = MUX(s, a, b) = (¬s ∧ a) ∨ (s ∧ b)\n");
    println!("The selector 's' interacts with both data inputs.");
    println!("No partition allows separation → all in one block.\n");

    let mux = named::mux();
    let cig = builder.build(&mux);
    println!("{}", display_tree(&cig));
    println!("Compact: {}\n", compact_notation(&cig));

    // Example 5: Mixed structure
    println!("┌─────────────────────────────────────────────────────────────┐");
    println!("│              Example 5: Mixed Structure                    │");
    println!("└─────────────────────────────────────────────────────────────┘\n");
    println!("f = (x₁ ∧ x₂) ⊕ x₃\n");
    println!("The AND of x₁,x₂ is irreducible, but XOR with x₃ is separable.\n");

    let mixed = TruthTable::from_expr(3, |x| (x[0] && x[1]) ^ x[2]);
    let cig = builder.build(&mixed);
    println!("{}", display_tree(&cig));
    println!("Compact: {}\n", compact_notation(&cig));

    // Example 6: Verify decomposition preserves semantics
    println!("┌─────────────────────────────────────────────────────────────┐");
    println!("│          Example 6: Semantic Preservation Check            │");
    println!("└─────────────────────────────────────────────────────────────┘\n");

    let test_functions = [
        ("x₁ ∧ x₂", TruthTable::from_expr(2, |x| x[0] && x[1])),
        ("x₁ ∨ x₂", TruthTable::from_expr(2, |x| x[0] || x[1])),
        ("x₁ ⊕ x₂", TruthTable::from_expr(2, |x| x[0] ^ x[1])),
        ("¬x₁", TruthTable::from_expr(1, |x| !x[0])),
    ];

    for (name, f) in &test_functions {
        let cig = builder.build(f);

        // Verify all truth table entries
        let n = f.num_vars();
        let mut all_match = true;
        for i in 0..(1 << n) {
            let assignment: Vec<bool> = (0..n)
                .map(|j| (i >> j) & 1 == 1)
                .collect();
            let tt_result = f.eval(&assignment);
            let cig_result = cig::operations::evaluate(&cig, &assignment);
            if tt_result != cig_result {
                all_match = false;
                break;
            }
        }

        let status = if all_match { "✓" } else { "✗" };
        println!("{} {} - CIG matches truth table", status, name);
        assert!(all_match, "Semantic mismatch for {}", name);
    }

    println!("\n═══════════════════════════════════════════════════════════════");
    println!("                 All decompositions verified!");
    println!("═══════════════════════════════════════════════════════════════");
}
