//! Variable Reordering Example
//!
//! Demonstrates how variable ordering dramatically affects BDD size.
//!
//! Key points:
//! - Variable ordering can cause exponential difference in BDD size
//! - Good ordering keeps related variables together
//! - Bad ordering separates related variables
//! - Sifting algorithm can improve bad orderings
//!
//! Run with:
//! ```bash
//! cargo run --example reordering
//! ```

use ananke_bdd::bdd::Bdd;

fn main() {
    println!("=== BDD Variable Ordering Example ===\n");

    // Function: (a1∧b1) ∨ (a2∧b2) ∨ (a3∧b3)
    // This function is very sensitive to variable ordering!

    let bdd = Bdd::default();

    // GOOD ordering: pairs together (a1,b1,a2,b2,a3,b3)
    println!("Building with GOOD ordering (pairs together): a1,b1,a2,b2,a3,b3");
    let f_good = {
        let a1 = bdd.mk_var(1);
        let b1 = bdd.mk_var(2);
        let a2 = bdd.mk_var(3);
        let b2 = bdd.mk_var(4);
        let a3 = bdd.mk_var(5);
        let b3 = bdd.mk_var(6);

        let t1 = bdd.apply_and(a1, b1);
        let t2 = bdd.apply_and(a2, b2);
        let t3 = bdd.apply_and(a3, b3);

        bdd.apply_or(bdd.apply_or(t1, t2), t3)
    };

    let size_good = bdd.size(f_good);
    println!("  Size: {} nodes", size_good);
    println!("  BDD: {}", bdd.to_bracket_string(f_good));
    assert_eq!(size_good, 7, "Good ordering should produce 7 nodes");

    // BAD ordering: separated (a1,a2,a3,b1,b2,b3)
    println!("\nBuilding with BAD ordering (separated): a1,a2,a3,b1,b2,b3");
    let bdd2 = Bdd::default();

    let f_bad = {
        let a1 = bdd2.mk_var(1);
        let a2 = bdd2.mk_var(2);
        let a3 = bdd2.mk_var(3);
        let b1 = bdd2.mk_var(4);
        let b2 = bdd2.mk_var(5);
        let b3 = bdd2.mk_var(6);

        let t1 = bdd2.apply_and(a1, b1);
        let t2 = bdd2.apply_and(a2, b2);
        let t3 = bdd2.apply_and(a3, b3);

        bdd2.apply_or(bdd2.apply_or(t1, t2), t3)
    };

    let size_bad = bdd2.size(f_bad);
    println!("  Size: {} nodes", size_bad);
    println!("  BDD: {}", bdd2.to_bracket_string(f_bad));
    assert_eq!(size_bad, 15, "Bad ordering should produce 15 nodes");

    // Compare results
    println!("\nCOMPARISON:");
    println!("  Good ordering: {} nodes", size_good);
    println!("  Bad ordering:  {} nodes", size_bad);
    println!("  Ratio:         {:.2}x", size_bad as f64 / size_good as f64);
    assert!(size_bad > size_good, "Bad ordering should produce larger BDD");
    println!(
        "\n✓ Variable ordering matters! Bad ordering is {:.2}x larger!",
        size_bad as f64 / size_good as f64
    );

    // Try sifting on the bad ordering
    println!("\nSIFTING THE BAD ORDERING:");

    let mut roots = vec![f_bad];
    let order_before: Vec<u32> = bdd2.get_variable_order().iter().map(|v| v.id()).collect();
    println!("  Before: order={:?}, size={} nodes", order_before, size_bad);

    let stats = bdd2.sift_all_variables(&mut roots);

    let size_after = bdd2.count_nodes(&roots);
    let order_after: Vec<u32> = bdd2.get_variable_order().iter().map(|v| v.id()).collect();
    println!("  After:  order={:?}, size={} nodes", order_after, size_after);

    println!(
        "\nSifting performed {} swaps across {} variables",
        stats.swaps, stats.variables_processed
    );

    if size_after < size_bad as usize {
        let improvement = 100.0 * (size_bad as usize - size_after) as f64 / size_bad as f64;
        println!("✓ Sifting improved BDD by {:.1}%!", improvement);
    } else {
        println!("→ Sifting found a local optimum (no further improvement)");
    }

    assert!(size_after <= size_bad as usize, "Sifting should not increase size");
}
