//! Variable Reordering Example
//!
//! This example demonstrates the explicit variable ordering features and
//! Rudell's sifting algorithm for dynamic BDD reordering.
//!
//! Key features demonstrated:
//! - Explicit variable ordering (var_order, level_map)
//! - Type-safe Var and Level abstractions
//! - In-place adjacent variable swaps (O(k) using forwarding pointers)
//! - Non-adjacent variable swaps (via adjacent swap sequences)
//! - Sifting individual variables to find optimal positions
//! - Full sifting algorithm for all variables
//!
//! Run with:
//! ```bash
//! cargo run --example reordering
//! ```

use bdd_rs::bdd::Bdd;
use bdd_rs::types::{Level, Var};

fn main() {
    println!("=== BDD Variable Reordering Example ===\n");

    example_1_ordering_impact();
    println!();

    example_2_query_ordering();
    println!();

    example_3_manual_swaps();
    println!();

    example_4_sifting_single_variable();
    println!();

    example_5_full_sifting();
}

/// Example 1: Demonstrate how variable ordering affects BDD size
fn example_1_ordering_impact() {
    println!("Example 1: Variable Ordering Impact");
    println!("=====================================");

    let bdd = Bdd::default();

    // Create a function: (x1 ∧ y1) ∨ (x2 ∧ y2) ∨ (x3 ∧ y3)
    // The ordering matters significantly for this function!

    println!("Building function: (x1∧y1) ∨ (x2∧y2) ∨ (x3∧y3)\n");

    // Good ordering: pairs together (x1, y1, x2, y2, x3, y3)
    println!("Good ordering (pairs together):");
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

    println!("  Size: {} nodes", bdd.size(f_good));

    // Bad ordering: all x's, then all y's (x1, x2, x3, y1, y2, y3)
    println!("\nBad ordering (separated):");
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

    println!("  Size: {} nodes", bdd.size(f_bad));
    println!(
        "\nSize ratio: {:.2}x (bad ordering is {} times larger)",
        bdd.size(f_bad) as f64 / bdd.size(f_good) as f64,
        bdd.size(f_bad) / bdd.size(f_good)
    );
}

/// Example 2: Query the explicit variable ordering
fn example_2_query_ordering() {
    println!("Example 2: Querying Explicit Variable Ordering");
    println!("================================================");

    let bdd = Bdd::default();

    // Create variables
    let x = bdd.mk_var(1);
    let y = bdd.mk_var(2);
    let z = bdd.mk_var(3);

    println!("Created variables: x (id=1), y (id=2), z (id=3)\n");

    // Query the variable ordering
    let var_order = bdd.get_variable_order();
    println!("Variable order (level → var):");
    for (level_idx, var) in var_order.iter().enumerate() {
        println!("  Level {}: Var({})", level_idx, var.id());
    }

    // Query individual variable levels
    println!("\nVariable → Level mapping:");
    for var_id in [1, 2, 3] {
        let var = Var::new(var_id);
        if let Some(level) = bdd.get_level(var) {
            println!("  Var({}) → Level {}", var_id, level.index());
        }
    }

    // Query variables at specific levels
    println!("\nLevel → Variable mapping:");
    for level_idx in 0..bdd.num_levels() {
        let level = Level::new(level_idx);
        if let Some(var) = bdd.get_variable_at_level(level) {
            println!("  Level {} → Var({})", level_idx, var.id());
        }
    }

    let f = bdd.apply_and(bdd.apply_and(x, y), z);
    println!("\nCreated function f = x ∧ y ∧ z");
    println!("f = {} of size {}", bdd.to_bracket_string(f), bdd.size(f));

    // Check nodes at each level
    println!("\nNodes at each level:");
    for level_idx in 0..bdd.num_levels() {
        let level = Level::new(level_idx);
        let nodes = bdd.get_nodes_at_level(level);
        println!("  Level {}: {} node(s)", level_idx, nodes.len());
    }
}

/// Example 3: Manual adjacent and non-adjacent variable swaps
fn example_3_manual_swaps() {
    println!("Example 3: Manual Variable Swaps");
    println!("==================================");

    let bdd = Bdd::default();

    let x1 = bdd.mk_var(1);
    let x2 = bdd.mk_var(2);
    let x3 = bdd.mk_var(3);
    let x4 = bdd.mk_var(4);

    let f = bdd.apply_or(bdd.apply_and(x1, x2), bdd.apply_and(x3, x4));

    println!("Function: (x1∧x2) ∨ (x3∧x4)");
    println!("Initial ordering: x1, x2, x3, x4");
    println!("Initial size: {} nodes\n", bdd.size(f));

    // Adjacent swap
    println!("Performing adjacent swap: levels 1 and 2 (x2 ↔ x3)");
    let mut roots = vec![f];
    bdd.swap_adjacent_variables(&mut roots, 1);

    let f = roots[0];
    println!("  New ordering: x1, x3, x2, x4");
    println!("  Size after swap: {} nodes\n", bdd.size(f));

    // Non-adjacent swap (uses multiple adjacent swaps internally)
    println!("Performing non-adjacent swap: vars 1 and 4 (x1 ↔ x4)");
    bdd.swap_any_variables(&mut roots, 1, 4);

    let f = roots[0];
    println!("  Final ordering: x4, x3, x2, x1");
    println!("  Size after swap: {} nodes", bdd.size(f));

    // Verify function is preserved
    let test_val = bdd.cofactor_cube(f, &[1, 2, 3, 4]);
    println!("\nFunction semantics preserved: {} (should be true)", bdd.is_one(test_val));
}

/// Example 4: Sift a single variable to find its optimal position
fn example_4_sifting_single_variable() {
    println!("Example 4: Sifting a Single Variable");
    println!("======================================");

    let bdd = Bdd::default();

    // Create a function where variable 3 is suboptimally placed
    // f = (x1 ∧ x2) ∨ (x3 ∧ x4) with x3 initially at wrong position
    let x1 = bdd.mk_var(1);
    let x3 = bdd.mk_var(2); // x3 comes early (suboptimal)
    let x2 = bdd.mk_var(3);
    let x4 = bdd.mk_var(4);

    let f = bdd.apply_or(bdd.apply_and(x1, x2), bdd.apply_and(x3, x4));

    println!("Function: (x1∧x2) ∨ (x3∧x4)");
    println!("Initial ordering has x3 out of place\n");

    let mut roots = vec![f];
    let size_before = bdd.count_nodes(&roots);

    println!("Before sifting:");
    println!("  Size: {} nodes", size_before);

    // Sift variable 2 (which has var_id=2, which is x3 in our labeling)
    println!("\nSifting variable 2 (x3)...");
    let (swaps, reduction) = bdd.sift_variable(&mut roots, 2);

    println!("  Swaps performed: {}", swaps);
    println!("  Size reduction: {} nodes", reduction);
    println!("\nAfter sifting:");
    println!("  Size: {} nodes", bdd.count_nodes(&roots));

    if reduction > 0 {
        println!("  ✓ Sifting improved the BDD!");
    } else if reduction == 0 {
        println!("  → BDD size unchanged (already at local optimum)");
    }
}

/// Example 5: Full sifting algorithm on all variables
fn example_5_full_sifting() {
    println!("Example 5: Full Sifting Algorithm");
    println!("===================================");

    let bdd = Bdd::default();

    // Build a complex formula with suboptimal ordering
    // Function: (a1∧b1) ∨ (a2∧b2) ∨ (a3∧b3)
    // Initial ordering: a1, a2, a3, b1, b2, b3 (all a's, then all b's - BAD!)

    println!("Building complex formula: (a1∧b1) ∨ (a2∧b2) ∨ (a3∧b3)");
    println!("Initial ordering: all a's, then all b's (suboptimal)\n");

    let a1 = bdd.mk_var(1);
    let a2 = bdd.mk_var(2);
    let a3 = bdd.mk_var(3);
    let b1 = bdd.mk_var(4);
    let b2 = bdd.mk_var(5);
    let b3 = bdd.mk_var(6);

    let term1 = bdd.apply_and(a1, b1);
    let term2 = bdd.apply_and(a2, b2);
    let term3 = bdd.apply_and(a3, b3);
    let f = bdd.apply_or(bdd.apply_or(term1, term2), term3);

    let mut roots = vec![f];

    println!("Before sifting:");
    println!("  Size: {} nodes", bdd.count_nodes(&roots));

    // Show initial ordering
    let var_order = bdd.get_variable_order();
    print!("  Ordering: ");
    for (i, var) in var_order.iter().enumerate() {
        print!("var{}", var.id());
        if i < var_order.len() - 1 {
            print!(", ");
        }
    }
    println!("\n");

    // Run full sifting algorithm
    println!("Running sifting algorithm...");
    let stats = bdd.sift_all_variables(&mut roots);

    println!("\nResults:");
    println!("  Initial size:      {} nodes", stats.initial_size);
    println!("  Final size:        {} nodes", stats.final_size);
    println!("  Best size seen:    {} nodes", stats.best_size);
    println!("  Reduction:         {:.1}%", stats.reduction_percent());
    println!("  Total swaps:       {}", stats.swaps);
    println!("  Variables sifted:  {}", stats.variables_processed);

    // Show final ordering
    let var_order = bdd.get_variable_order();
    print!("\nFinal ordering: ");
    for (i, var) in var_order.iter().enumerate() {
        print!("var{}", var.id());
        if i < var_order.len() - 1 {
            print!(", ");
        }
    }
    println!();

    if stats.final_size < stats.initial_size {
        println!("\n✓ Sifting successfully improved the BDD size!");
        println!("  The algorithm found a better variable ordering.");
    } else {
        println!("\n→ BDD size stayed the same");
        println!("  The initial ordering was already locally optimal.");
    }
}
