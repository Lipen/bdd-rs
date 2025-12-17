//! Comparison with BDD - demonstrating CIG's advantages.
//!
//! This example shows how CIG can guide BDD variable ordering
//! and provide complexity certificates.
//!
//! Run with: cargo run --example comparison

use cig::{CigBuilder, TruthTable};
use cig::analysis::{CigAnalysis, suggest_variable_order};
use ananke_bdd::bdd::Bdd;

fn main() {
    println!("═══════════════════════════════════════════════════════════════");
    println!("     CIG vs BDD Comparison - Complexity Certificates");
    println!("═══════════════════════════════════════════════════════════════\n");

    let mut cig_builder = CigBuilder::new();
    let bdd = Bdd::default();

    // Example 1: Parity function (BDD-friendly)
    println!("┌─────────────────────────────────────────────────────────────┐");
    println!("│        Example 1: Parity Function (4 variables)            │");
    println!("└─────────────────────────────────────────────────────────────┘\n");

    let parity = TruthTable::from_expr(4, |x| x[0] ^ x[1] ^ x[2] ^ x[3]);
    compare_representations(&mut cig_builder, &bdd, "Parity₄", &parity);

    // Example 2: Hidden weighted bit (challenging for BDD)
    println!("┌─────────────────────────────────────────────────────────────┐");
    println!("│      Example 2: Threshold Function (3 of 5)                │");
    println!("└─────────────────────────────────────────────────────────────┘\n");

    let threshold = TruthTable::from_expr(5, |x| {
        let count: usize = x.iter().filter(|&&b| b).count();
        count >= 3
    });
    compare_representations(&mut cig_builder, &bdd, "Threshold₃₅", &threshold);

    // Example 3: Majority-3 (irreducible)
    println!("┌─────────────────────────────────────────────────────────────┐");
    println!("│         Example 3: Majority Function (3 variables)         │");
    println!("└─────────────────────────────────────────────────────────────┘\n");

    let maj = TruthTable::from_expr(3, |x| {
        (x[0] && x[1]) || (x[1] && x[2]) || (x[0] && x[2])
    });
    compare_representations(&mut cig_builder, &bdd, "MAJ₃", &maj);

    // Example 4: Composed function with structure
    println!("┌─────────────────────────────────────────────────────────────┐");
    println!("│      Example 4: Composed Function with Structure           │");
    println!("└─────────────────────────────────────────────────────────────┘\n");

    let composed = TruthTable::from_expr(6, |x| {
        // ((x1 XOR x2) AND (x3 XOR x4)) OR (x5 AND x6)
        ((x[0] ^ x[1]) && (x[2] ^ x[3])) || (x[4] && x[5])
    });
    compare_representations(&mut cig_builder, &bdd, "Composed₆", &composed);

    // Example 5: Demonstrate variable ordering guidance
    println!("┌─────────────────────────────────────────────────────────────┐");
    println!("│        Example 5: Variable Ordering Guidance               │");
    println!("└─────────────────────────────────────────────────────────────┘\n");

    demonstrate_ordering_guidance(&mut cig_builder, &bdd);

    // Example 6: Lower bound certificate
    println!("┌─────────────────────────────────────────────────────────────┐");
    println!("│           Example 6: Lower Bound Certificates              │");
    println!("└─────────────────────────────────────────────────────────────┘\n");

    demonstrate_lower_bounds(&mut cig_builder);

    println!("\n═══════════════════════════════════════════════════════════════");
    println!("                     Comparison Complete");
    println!("═══════════════════════════════════════════════════════════════");
}

fn compare_representations(
    cig_builder: &mut CigBuilder,
    bdd: &Bdd,
    name: &str,
    f: &TruthTable,
) {
    // Build CIG
    let cig = cig_builder.build(f);
    let analysis = CigAnalysis::analyze(&cig);

    // Build BDD
    let bdd_ref = build_bdd_from_truth_table(bdd, f);
    let bdd_size = bdd.size(bdd_ref);

    println!("Function: {}", name);
    println!("Variables: {}\n", f.num_vars());

    println!("CIG Analysis:");
    println!("  Size:          {} nodes", analysis.size);
    println!("  Depth:         {}", analysis.depth);
    println!("  Interaction ω: {}", analysis.interaction_width);
    println!("  Complexity:    {}", analysis.complexity_class);
    println!();

    println!("BDD Analysis:");
    println!("  Size:          {} nodes", bdd_size);
    println!();

    println!("CIG-based bounds:");
    println!("  BDD width ≥ {}", analysis.bdd_width_lower_bound());
    println!();
}

fn build_bdd_from_truth_table(bdd: &Bdd, f: &TruthTable) -> ananke_bdd::reference::Ref {
    let n = f.num_vars() as usize;

    // Build BDD bottom-up using Shannon expansion
    let mut current = vec![bdd.zero(); 1 << n];
    for i in 0..(1 << n) {
        current[i] = if f.eval_index(i) { bdd.one() } else { bdd.zero() };
    }

    for var in (1..=n).rev() {
        let half = 1 << (var - 1);
        let mut next = vec![bdd.zero(); half];

        for i in 0..half {
            let low = current[i * 2];
            let high = current[i * 2 + 1];
            next[i] = bdd.apply_ite(bdd.mk_var(var as u32), high, low);
        }

        current = next;
    }

    current[0]
}

fn demonstrate_ordering_guidance(cig_builder: &mut CigBuilder, bdd: &Bdd) {
    // Function where variable ordering matters
    let f = TruthTable::from_expr(4, |x| (x[0] && x[2]) || (x[1] && x[3]));

    let cig = cig_builder.build(&f);
    let suggested_order = suggest_variable_order(&cig);

    println!("Function: (x₁ ∧ x₃) ∨ (x₂ ∧ x₄)");
    println!();
    println!("CIG-suggested variable order:");
    print!("  ");
    for (i, var) in suggested_order.iter().enumerate() {
        if i > 0 {
            print!(" < ");
        }
        print!("{}", var);
    }
    println!();
    println!();

    // Build BDD with default ordering
    let bdd_ref = build_bdd_from_truth_table(bdd, &f);
    println!("BDD size (default order): {} nodes", bdd.size(bdd_ref));
    println!();

    println!("The CIG structure reveals that {{x₁, x₃}} and {{x₂, x₄}} interact,");
    println!("suggesting these pairs should be adjacent in the BDD ordering.");
    println!();
}

fn demonstrate_lower_bounds(cig_builder: &mut CigBuilder) {
    let functions = [
        ("Parity₄", TruthTable::from_expr(4, |x| x[0] ^ x[1] ^ x[2] ^ x[3])),
        ("AND₄", TruthTable::from_expr(4, |x| x[0] && x[1] && x[2] && x[3])),
        ("MAJ₃", TruthTable::from_expr(3, |x| {
            (x[0] && x[1]) || (x[1] && x[2]) || (x[0] && x[2])
        })),
        ("MUX", TruthTable::from_expr(3, |x| {
            (!x[0] && x[1]) || (x[0] && x[2])
        })),
    ];

    println!("CIG provides lower bounds on BDD width based on interaction structure:\n");

    println!("┌───────────────┬───────┬────────────────────┐");
    println!("│ Function      │   ω   │  BDD Width ≥       │");
    println!("├───────────────┼───────┼────────────────────┤");

    for (name, f) in &functions {
        let cig = cig_builder.build(f);
        let analysis = CigAnalysis::analyze(&cig);
        let lb = analysis.bdd_width_lower_bound();

        println!("│ {:<13} │ {:>5} │ {:>18} │", name, analysis.interaction_width, lb);
    }

    println!("└───────────────┴───────┴────────────────────┘");
    println!();
    println!("ω = interaction width (max arity of irreducible interactions)");
    println!("Lower bound = 2^(ω-1)");
    println!();
}
