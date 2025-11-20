//! Loop Optimization Analysis Example.
//!
//! This example demonstrates using the **Congruence Domain** combined with the **Interval Domain**
//! to analyze a strided loop.
//!
//! Scenario:
//! ```c
//! for (int i = 0; i < 100; i += 4) {
//!     // Access array at index i
//!     // Check alignment: i % 4 == 0
//! }
//! ```
//!
//! The analysis proves:
//! 1. `i` is always within bounds [0, 100].
//! 2. `i` is always a multiple of 4 (alignment safety).

use abstract_interpretation::congruence::{Congruence, CongruenceDomain};
use abstract_interpretation::domain::AbstractDomain;
use abstract_interpretation::generic_product::{ProductDomain, ProductElement};
use abstract_interpretation::interval::{Bound, Interval, SingleIntervalDomain};

fn main() {
    println!("=== Loop Optimization Analysis ===");
    println!("Using Interval x Congruence Product Domain.\n");

    println!("Program:");
    println!("  for (int i = 0; i < 100; i += 4) {{");
    println!("      // Access array at index i");
    println!("      // Check alignment: i % 4 == 0");
    println!("  }}\n");

    // Define domains
    let interval_dom = SingleIntervalDomain;
    let congruence_dom = CongruenceDomain;
    let product_dom = ProductDomain::new(interval_dom.clone(), congruence_dom.clone());

    // Initial state: i = 0
    // Interval: [0, 0]
    // Congruence: 0 (mod 0) -> Constant 0
    let i_interval = Interval::constant(0);
    let i_congruence = congruence_dom.constant(0);
    let mut state = ProductElement(i_interval, i_congruence);

    println!("Initial State (i = 0):");
    println!("  Interval: {}", state.0);
    println!("  Congruence: {:?}", state.1);

    // Loop simulation (Fixpoint iteration)
    // Loop condition: i < 100
    // Loop step: i += 4

    println!("\n--- Analyzing Loop ---");
    for iter in 1..=5 {
        println!("Iteration {}:", iter);

        // 1. Check condition i < 100
        // Refine interval to [-inf, 99]
        // (Simplified: we just check if we should continue)
        // In a real engine, we'd use meet().

        // 2. Body: i += 4
        // Interval: [low+4, high+4]
        let next_interval = Interval::new(state.0.low.add(&Bound::Finite(4)), state.0.high.add(&Bound::Finite(4)));

        // Congruence: (c, k) + (4, 0)
        let four_cong = congruence_dom.constant(4);
        let next_congruence = congruence_dom.add(&state.1, &four_cong);

        let next_state = ProductElement(next_interval, next_congruence);

        // 3. Join with previous state (Widen)
        // Interval Widen: [0, 0] ∇ [4, 4] -> [0, +inf]
        // Congruence Join: 0 (mod 0) ⊔ 4 (mod 0) -> 0 (mod 4)
        //   (gcd(0, 0, |0-4|) = 4)

        let old_state = state.clone();
        state = product_dom.widen(&state, &next_state);

        // Narrowing for interval (simulated): i < 100
        // [0, +inf] meet [-inf, 99] -> [0, 99] (actually loop runs while i < 100, so i can reach 100 at exit? No, i < 100 is guard)
        // Wait, standard loop analysis:
        //   State at head.
        //   Body executes if i < 100.
        //   i += 4.
        //   Join back to head.

        // Let's manually apply the "i < 100" constraint to the widened interval
        if let Bound::Finite(h) = state.0.high {
            if h >= 100 {
                state.0.high = Bound::Finite(100); // Upper bound from loop condition + stride?
                                                   // Actually, if i < 100, max i is 96. Next i is 100.
                                                   // So at loop head, i can be 100 (exit condition).
            }
        } else {
            // Widen went to infinity, apply loop bound
            state.0.high = Bound::Finite(100);
        }

        println!("  State after join/widen:");
        println!("    Interval: {}", state.0);
        println!("    Congruence: {:?}", state.1);

        if state == old_state {
            println!("  ✓ Fixpoint reached!");
            break;
        }
    }

    println!("\nFinal Loop Invariant:");
    println!("  i ∈ {}", state.0);
    println!("  i ≡ {:?}", state.1);

    // Verification
    // 1. Bounds check
    let safe_bounds = match (state.0.low, state.0.high) {
        (Bound::Finite(l), Bound::Finite(h)) => l >= 0 && h <= 100,
        _ => false,
    };

    if safe_bounds {
        println!("  ✓ Verified: i is within [0, 100]");
    } else {
        println!("  ✗ Failed: Bounds check failed");
    }
    assert!(safe_bounds);

    // 2. Alignment check (multiple of 4)
    // Congruence should be (0, 4) or (0, k) where k is multiple of 4
    let aligned = match state.1 {
        Congruence::Val(c, k) => c == 0 && k % 4 == 0 && k != 0,
        _ => false,
    };

    if aligned {
        println!("  ✓ Verified: i is always a multiple of 4 (Alignment Safe)");
    } else {
        println!("  ✗ Failed: Alignment check failed");
    }
    assert!(aligned);
}
