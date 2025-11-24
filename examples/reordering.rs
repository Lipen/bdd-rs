//! Variable ordering and reordering example.
//!
//! This example demonstrates how variable ordering affects BDD size and shows
//! the effectiveness of Rudell's sifting algorithm for dynamic reordering.
//!
//! Run with:
//! ```bash
//! cargo run --example reordering
//! ```

use bdd_rs::bdd::Bdd;

fn main() {
    println!("=== BDD Variable Ordering and Reordering Example ===\n");

    example_1_ordering_matters();
    println!();

    example_2_bad_to_good_ordering();
    println!();

    example_3_sifting_optimization();
    println!();

    example_4_complex_formula();
}

/// Example 1: Show how ordering affects BDD size
fn example_1_ordering_matters() {
    println!("Example 1: Variable Ordering Impact");
    println!("-------------------------------------");

    let bdd = Bdd::default();

    // Create two functions with the same semantics but different variable orderings
    // Function: (x1 ∧ y1) ∨ (x2 ∧ y2) ∨ (x3 ∧ y3)

    // Good ordering: x1, y1, x2, y2, x3, y3 (variables in pairs)
    let x1 = bdd.mk_var(1);
    let y1 = bdd.mk_var(2);
    let x2 = bdd.mk_var(3);
    let y2 = bdd.mk_var(4);
    let x3 = bdd.mk_var(5);
    let y3 = bdd.mk_var(6);

    let term1 = bdd.apply_and(x1, y1);
    let term2 = bdd.apply_and(x2, y2);
    let term3 = bdd.apply_and(x3, y3);
    let f_good = bdd.apply_or(bdd.apply_or(term1, term2), term3);

    println!("Good ordering (x1,y1,x2,y2,x3,y3): {} nodes", bdd.size(f_good));

    // Bad ordering: x1, x2, x3, y1, y2, y3 (all x's, then all y's)
    let x1 = bdd.mk_var(11);
    let x2 = bdd.mk_var(12);
    let x3 = bdd.mk_var(13);
    let y1 = bdd.mk_var(14);
    let y2 = bdd.mk_var(15);
    let y3 = bdd.mk_var(16);

    let term1 = bdd.apply_and(x1, y1);
    let term2 = bdd.apply_and(x2, y2);
    let term3 = bdd.apply_and(x3, y3);
    let f_bad = bdd.apply_or(bdd.apply_or(term1, term2), term3);

    println!("Bad ordering  (x1,x2,x3,y1,y2,y3): {} nodes", bdd.size(f_bad));
    println!("Size ratio: {:.2}x", bdd.size(f_bad) as f64 / bdd.size(f_good) as f64);
}

/// Example 2: Use sifting to improve a bad ordering
fn example_2_bad_to_good_ordering() {
    println!("Example 2: Improving Bad Ordering with Sifting");
    println!("------------------------------------------------");

    let bdd = Bdd::default();

    // Start with a suboptimal ordering
    // Function: (a ∧ b ∧ c) ∨ (d ∧ e ∧ f)
    // With ordering a,d,b,e,c,f this is suboptimal
    let a = bdd.mk_var(1);
    let d = bdd.mk_var(2);
    let b = bdd.mk_var(3);
    let e = bdd.mk_var(4);
    let c = bdd.mk_var(5);
    let f = bdd.mk_var(6);

    let term1 = bdd.apply_and(bdd.apply_and(a, b), c);
    let term2 = bdd.apply_and(bdd.apply_and(d, e), f);
    let formula = bdd.apply_or(term1, term2);

    let mut roots = vec![formula];
    let size_before = bdd.count_nodes(&roots);

    println!("Initial size: {} nodes", size_before);
    println!(
        "Variables: a={}, d={}, b={}, e={}, c={}, f={} (interleaved)\n",
        bdd.variable(a.index()),
        bdd.variable(d.index()),
        bdd.variable(b.index()),
        bdd.variable(e.index()),
        bdd.variable(c.index()),
        bdd.variable(f.index()),
    );

    // Perform sifting
    let stats = bdd.sift_all_variables(&mut roots);

    println!("After sifting:");
    println!("  Final size: {} nodes", stats.final_size);
    println!(
        "  Reduction: {:.1}%",
        100.0 * (1.0 - (stats.final_size as f64 / stats.initial_size as f64))
    );
    println!("  Total swaps: {}", stats.swaps);
    println!("  Variables processed: {}", stats.variables_processed);
}

/// Example 3: Detailed sifting process
fn example_3_sifting_optimization() {
    println!("Example 3: Sifting a Single Variable");
    println!("---------------------------------------");

    let bdd = Bdd::default();

    // Create a function where one variable is out of place
    // f = (x1 ∧ x2) ∨ (x3 ∧ x4) with x2 initially at the wrong position
    let x1 = bdd.mk_var(1);
    let x3 = bdd.mk_var(2); // x3 comes before x2 (suboptimal)
    let x2 = bdd.mk_var(3);
    let x4 = bdd.mk_var(4);

    let f = bdd.apply_or(bdd.apply_and(x1, x2), bdd.apply_and(x3, x4));

    let mut roots = vec![f];
    let size_before = bdd.count_nodes(&roots);

    println!(
        "Initial ordering: x1={}, x3={}, x2={}, x4={}",
        bdd.variable(x1.index()),
        bdd.variable(x3.index()),
        bdd.variable(x2.index()),
        bdd.variable(x4.index()),
    );
    println!("Initial size: {} nodes", size_before);
    println!("\nSifting variable 3 (x2)...");

    let (swaps, reduction) = bdd.sift_variable(&mut roots, 3, 4);

    println!("  Swaps performed: {}", swaps);
    println!("  Size reduction: {} nodes", reduction);
    println!("  Final size: {} nodes", bdd.count_nodes(&roots));
}

/// Example 4: Complex formula with significant improvement
fn example_4_complex_formula() {
    println!("Example 4: Complex Formula Optimization");
    println!("-----------------------------------------");

    let bdd = Bdd::default();

    // Build a more complex formula with poor initial ordering
    // Formula: majority function on sets of variables
    // (a1 ∧ b1) ∨ (a2 ∧ b2) ∨ (a3 ∧ b3) with interleaved ordering

    let mut vars = Vec::new();
    for i in 1..=6 {
        vars.push(bdd.mk_var(i));
    }

    // Initial ordering: a1, a2, a3, b1, b2, b3
    let a1 = vars[0];
    let a2 = vars[1];
    let a3 = vars[2];
    let b1 = vars[3];
    let b2 = vars[4];
    let b3 = vars[5];

    let term1 = bdd.apply_and(a1, b1);
    let term2 = bdd.apply_and(a2, b2);
    let term3 = bdd.apply_and(a3, b3);

    let f = bdd.apply_or(bdd.apply_or(term1, term2), term3);

    let mut roots = vec![f];
    let initial_size = bdd.count_nodes(&roots);

    println!("Complex formula: (a1∧b1) ∨ (a2∧b2) ∨ (a3∧b3)");
    println!("Initial ordering: a1,a2,a3,b1,b2,b3 (all a's, then all b's)");
    println!("Initial size: {} nodes\n", initial_size);

    println!("Running sifting algorithm...");
    let stats = bdd.sift_all_variables(&mut roots);

    println!("\nResults:");
    println!("  Initial size:  {} nodes", stats.initial_size);
    println!("  Final size:    {} nodes", stats.final_size);
    println!("  Best size:     {} nodes", stats.best_size);
    println!("  Reduction:     {:.1}%", stats.reduction_percent());
    println!("  Total swaps:   {}", stats.swaps);
    println!("  Variables:     {}", stats.variables_processed);

    if stats.final_size < stats.initial_size {
        println!("\n✓ Sifting improved the BDD size!");
    } else {
        println!("\n→ BDD size stayed the same (already optimal)");
    }
}
