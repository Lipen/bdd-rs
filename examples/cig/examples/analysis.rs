//! CIG structural analysis example.
//!
//! This example demonstrates how CIG reveals the intrinsic complexity
//! of Boolean functions through interaction analysis.
//!
//! Run with: cargo run --example analysis

use cig::{CigBuilder, TruthTable, Var};
use cig::analysis::{CigAnalysis, ComplexityClass};
use cig::truth_table::named;

fn main() {
    println!("═══════════════════════════════════════════════════════════════");
    println!("     CIG Structural Analysis - Understanding Boolean Functions");
    println!("═══════════════════════════════════════════════════════════════\n");

    let mut builder = CigBuilder::new();

    // Analyze a variety of functions
    analyze_function(&mut builder, "Constant 0", TruthTable::zero(4));
    analyze_function(&mut builder, "Constant 1", TruthTable::one(4));
    analyze_function(&mut builder, "Projection x₁", TruthTable::var(4, Var(1)));
    analyze_function(&mut builder, "AND₄", named::and_all(4));
    analyze_function(&mut builder, "OR₄", named::or_all(4));
    analyze_function(&mut builder, "XOR₄ (Parity)", named::xor_all(4));
    analyze_function(&mut builder, "MAJ₃", named::majority3());
    analyze_function(&mut builder, "MUX", named::mux());
    analyze_function(&mut builder, "Full Adder Sum", named::full_adder_sum());
    analyze_function(&mut builder, "Full Adder Carry", named::full_adder_carry());

    // Composed functions
    println!("\n═══════════════════════════════════════════════════════════════");
    println!("                    Composed Functions");
    println!("═══════════════════════════════════════════════════════════════\n");

    let composed1 = TruthTable::from_expr(4, |x| (x[0] ^ x[1]) && (x[2] ^ x[3]));
    analyze_function(&mut builder, "(x₁ ⊕ x₂) ∧ (x₃ ⊕ x₄)", composed1);

    let composed2 = TruthTable::from_expr(4, |x| (x[0] || x[1]) && (x[2] || x[3]));
    analyze_function(&mut builder, "(x₁ ∨ x₂) ∧ (x₃ ∨ x₄)", composed2);

    let composed3 = TruthTable::from_expr(4, |x| (x[0] && x[1]) ^ (x[2] && x[3]));
    analyze_function(&mut builder, "(x₁ ∧ x₂) ⊕ (x₃ ∧ x₄)", composed3);

    // Demonstrate complexity classification
    println!("\n═══════════════════════════════════════════════════════════════");
    println!("                  Complexity Classification");
    println!("═══════════════════════════════════════════════════════════════\n");

    demonstrate_classification(&mut builder);

    println!("\n═══════════════════════════════════════════════════════════════");
    println!("                        Analysis Complete");
    println!("═══════════════════════════════════════════════════════════════");
}

fn analyze_function(builder: &mut CigBuilder, name: &str, f: TruthTable) {
    let cig = builder.build(&f);
    let analysis = CigAnalysis::analyze(&cig);

    println!("┌─────────────────────────────────────────────────────────────┐");
    println!("│ {:<59} │", name);
    println!("├─────────────────────────────────────────────────────────────┤");
    println!("│ Variables:         {:<40} │", analysis.num_variables);
    println!("│ CIG Size:          {:<40} │", analysis.size);
    println!("│ CIG Depth:         {:<40} │", analysis.depth);
    println!("│ Interaction Width: {:<40} │", analysis.interaction_width);
    println!("│ Table Size:        {:<40} │", analysis.table_size);
    println!("│ Complexity:        {:<40} │", format!("{}", analysis.complexity_class));
    println!("│ BDD Width LB:      {:<40} │", format!("≥ {}", analysis.bdd_width_lower_bound()));
    println!("└─────────────────────────────────────────────────────────────┘\n");
}

fn demonstrate_classification(builder: &mut CigBuilder) {
    let examples: Vec<(&str, TruthTable, ComplexityClass)> = vec![
        ("0 (constant)", TruthTable::zero(2), ComplexityClass::Constant),
        ("x₁ (projection)", TruthTable::var(2, Var(1)), ComplexityClass::Projection),
        ("x₁ ⊕ x₂ ⊕ x₃ (linear)", named::xor_all(3), ComplexityClass::Linear),
        ("x₁ ∧ x₂ (monotone)", TruthTable::from_expr(2, |x| x[0] && x[1]), ComplexityClass::Monotone),
        ("MAJ₃ (irreducible)", named::majority3(), ComplexityClass::Irreducible),
    ];

    for (name, f, expected) in examples {
        let cig = builder.build(&f);
        let analysis = CigAnalysis::analyze(&cig);

        let status = if analysis.complexity_class == expected {
            "✓"
        } else {
            "✗"
        };

        println!("{} {} → {}", status, name, analysis.complexity_class);
        assert_eq!(analysis.complexity_class, expected, "Classification mismatch for {}", name);
    }
}
