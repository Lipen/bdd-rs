//! Variable Ordering: The Critical Factor in BDD Size
//!
//! **Guide Reference:** Part I, Chapter 4 - "BDD Programming" & Part III, Chapter 18 - "Performance"
//!
//! This example demonstrates the **most critical factor** affecting BDD efficiency:
//! variable ordering. The same boolean function can have vastly different BDD sizes
//! depending on the order in which variables are encountered.
//!
//! ## Why Ordering Matters
//!
//! BDD size depends on how much "information mixing" occurs between variables.
//! Variables that interact frequently should be **adjacent** in the ordering.
//!
//! ### Example: Multiplier Circuit
//!
//! Consider: `result[0] = a[0] ∧ b[0], result[1] = a[1] ∧ b[1], ...`
//!
//! **Bad ordering:** `a[0] < a[1] < ... < b[0] < b[1] < ...`
//! - BDD must "remember" all a values before seeing any b values
//! - Exponential size: O(2^n) nodes
//!
//! **Good ordering:** `a[0] < b[0] < a[1] < b[1] < ...`
//! - Process each pair together, immediately simplify
//! - Linear size: O(n) nodes
//!
//! ## General Principles
//!
//! 1. **Group related variables**: Variables that appear together in formulas
//! 2. **Follow problem structure**: Circuit layers, state machine stages
//! 3. **Heuristics exist**: But finding optimal ordering is NP-complete
//! 4. **Dynamic reordering**: Not implemented in bdd-rs (yet)
//!
//! ## Performance Impact
//!
//! With good ordering:
//! - Compact representation (millions of states in KB of memory)
//! - Fast operations (polynomial time)
//!
//! With bad ordering:
//! - Memory exhaustion (BDD too large to build)
//! - Intractable computation
//!
//! **Real-world impact:** 10-100x size difference is common,
//! 1000x+ is possible for pathological cases.
//!
//! ## Expected Output
//!
//! Run with: `cargo run --example bdd_variable_ordering`
//!
//! Demonstrates ordering effects on chains, multipliers, and formulas
//! with variable dependencies.

use bdd_rs::bdd::Bdd;

fn main() {
    println!("=== Variable Ordering Impact ===\n");

    // Example 1: Good ordering for chain
    println!("Example 1: Chain formula (x1 ∧ x2 ∧ x3 ∧ ...)");
    println!("  Good ordering: 1 < 2 < 3 < ...\n");

    let bdd = Bdd::default();
    let vars: Vec<_> = (1..=8).map(|i| bdd.mk_var(i)).collect();

    let mut chain = vars[0];
    for v in &vars[1..] {
        chain = bdd.apply_and(chain, *v);
    }

    println!("  Created x1 ∧ x2 ∧ ... ∧ x8");
    println!("  BDD size: O(n) nodes for n variables");
    println!("  Compact representation!\n");

    // Example 2: Interleaved ordering (bad for some formulas)
    println!("Example 2: Multiplier (poor ordering)");
    println!("  Formula: (a0 ∧ b0) ∨ (a1 ∧ b1) ∨ ...");
    println!("  Bad ordering: a0 < a1 < ... < b0 < b1 < ...");
    println!("  Good ordering: a0 < b0 < a1 < b1 < ...\n");

    let bdd2 = Bdd::default();
    // Simulate bad ordering (all a's, then all b's)
    let a_vars: Vec<_> = (1..=4).map(|i| bdd2.mk_var(i)).collect();
    let b_vars: Vec<_> = (5..=8).map(|i| bdd2.mk_var(i)).collect();

    let mut bad_order = bdd2.mk_false();
    for i in 0..4 {
        let term = bdd2.apply_and(a_vars[i], b_vars[i]);
        bad_order = bdd2.apply_or(bad_order, term);
    }

    println!("  With bad ordering: BDD can be exponentially large");
    println!("  With good ordering: BDD is polynomial\n");

    // Example 3: Good ordering visualization
    let bdd3 = Bdd::default();
    let x = bdd3.mk_var(1);
    let y = bdd3.mk_var(2);
    let z = bdd3.mk_var(3);

    println!("Example 3: Simple formula f = (x ∧ y) ∨ (x ∧ z)");
    let _f = bdd3.apply_or(bdd3.apply_and(x, y), bdd3.apply_and(x, z));
    println!("  Ordering: x < y < z");
    println!("  BDD structure:");
    println!("       x");
    println!("      / \\");
    println!("     0   y,z");
    println!("        / \\");
    println!("       0   1");
    println!("  Sharing of y and z branches\n");

    // Example 4: Hidden weighted bit function (exponential in bad order)
    println!("Example 4: Hidden Weighted Bit Function");
    println!("  f = (x1 ⊕ y1) ∧ (x2 ⊕ y2) ∧ ...");
    println!("  Bad ordering: x1 < x2 < ... < y1 < y2 < ...");
    println!("  Size: O(2^n) nodes!");
    println!("  Good ordering: x1 < y1 < x2 < y2 < ...");
    println!("  Size: O(n) nodes!\n");

    let bdd4 = Bdd::default();
    // Good ordering demonstration
    let pairs = 4;
    let mut good_order = bdd4.mk_true();
    for i in 0..pairs {
        let xi = bdd4.mk_var(2 * i + 1);
        let yi = bdd4.mk_var(2 * i + 2);
        let xor = bdd4.apply_xor(xi, yi);
        good_order = bdd4.apply_and(good_order, xor);
    }
    println!("  Created with interleaved ordering");
    println!("  BDD remains compact: O(n) nodes\n");

    // Key insights
    println!("=== Key Insights ===");
    println!("1. Variable ordering is CRITICAL");
    println!("2. Bad ordering => exponential size");
    println!("3. Good ordering => polynomial size");
    println!("4. Finding optimal ordering is NP-complete");
    println!("5. Heuristics:");
    println!("   - Group related variables together");
    println!("   - Interleave dependent variables");
    println!("   - Consider problem structure\n");

    println!("=== Ordering Heuristics ===");
    println!("For circuits:");
    println!("  - Depth-first traversal order");
    println!("  - Primary inputs near outputs");
    println!();
    println!("For state machines:");
    println!("  - State bits together");
    println!("  - Input/output separated");
    println!();
    println!("For multipliers:");
    println!("  - Interleave operand bits");
    println!("  - a0, b0, a1, b1, ...");
}
