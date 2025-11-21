//! Loop Optimization Analysis Example.
//!
//! This example demonstrates using the **Congruence Domain** combined with the **Interval Domain**
//! to analyze a strided loop.
//!
//! # Scenario
//!
//! ```c
//! for (int i = 0; i < 100; i += 4) {
//!     // Access array at index i
//!     // Check alignment: i % 4 == 0
//! }
//! ```
//!
//! # Analysis Goals
//!
//! 1. **Bounds Check**: Prove `i` is always within `[0, 100]`.
//! 2. **Alignment Check**: Prove `i` is always a multiple of 4.
//!
//! # Technical Details
//!
//! - **Interval Domain**: Tracks range `[min, max]`.
//! - **Congruence Domain**: Tracks `x ≡ c (mod k)`.
//! - **Product Domain**: Combines both for precise analysis.

use abstract_interpretation::congruence::{Congruence, CongruenceDomain};
use abstract_interpretation::domain::AbstractDomain;
use abstract_interpretation::generic_product::{ProductDomain, ProductElement};
use abstract_interpretation::interval::{Bound, Interval, SingleIntervalDomain};

fn main() {
    println!("\n=======================================================");
    println!("   Loop Optimization Analysis");
    println!("=======================================================\n");

    analyze_strided_loop();
    println!("=======================================================");
    analyze_countdown_loop();

    println!("=======================================================");
    println!("   Analysis Complete");
    println!("=======================================================");
}

/// Example 1: Strided Loop Analysis
/// Analyzes a loop with a stride of 4: `for (i = 0; i < 100; i += 4)`
fn analyze_strided_loop() {
    println!("--- Example 1: Strided Loop Analysis ---");
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

    // Assert initial state
    assert_eq!(state.0, Interval::constant(0));
    assert_eq!(state.1, Congruence::Val(0, 0));

    // Loop simulation (Fixpoint iteration)
    // Loop condition: i < 100
    // Loop step: i += 4

    println!("\n--- Analyzing Loop Fixpoint ---");
    for iter in 1..=5 {
        println!("Iteration {}:", iter);

        // 1. Check condition i < 100
        // Refine interval to [-inf, 99]
        // (Simplified: we just check if we should continue)

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
        // Let's manually apply the "i < 100" constraint to the widened interval
        if let Bound::Finite(h) = state.0.high {
            if h >= 100 {
                state.0.high = Bound::Finite(100);
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
    println!("\n--- Verification ---");

    // 1. Bounds check
    let safe_bounds = match (state.0.low, state.0.high) {
        (Bound::Finite(l), Bound::Finite(h)) => l >= 0 && h <= 100,
        _ => false,
    };

    assert!(safe_bounds, "Bounds check failed: i should be in [0, 100]");
    println!("  ✓ Verified: i is within [0, 100]");

    // 2. Alignment check (multiple of 4)
    // Congruence should be (0, 4) or (0, k) where k is multiple of 4
    let aligned = match state.1 {
        Congruence::Val(c, k) => c == 0 && k % 4 == 0 && k != 0,
        _ => false,
    };

    assert!(aligned, "Alignment check failed: i should be a multiple of 4");
    println!("  ✓ Verified: i is always a multiple of 4 (Alignment Safe)");
    println!();
}

/// Example 2: Countdown Loop Analysis
/// Analyzes a loop counting down: `for (i = 10; i >= 0; i -= 2)`
fn analyze_countdown_loop() {
    println!("--- Example 2: Countdown Loop Analysis ---");
    println!("Program:");
    println!("  for (int i = 10; i >= 0; i -= 2) {{");
    println!("      // Access array at index i");
    println!("  }}\n");

    // Define domains
    let interval_dom = SingleIntervalDomain;
    let congruence_dom = CongruenceDomain;
    let product_dom = ProductDomain::new(interval_dom.clone(), congruence_dom.clone());

    // Initial state: i = 10
    // Interval: [10, 10]
    // Congruence: 10 (mod 0) -> Constant 10
    let i_interval = Interval::constant(10);
    let i_congruence = congruence_dom.constant(10);
    let mut state = ProductElement(i_interval, i_congruence);

    println!("Initial State (i = 10):");
    println!("  Interval: {}", state.0);
    println!("  Congruence: {:?}", state.1);

    // Assert initial state
    assert_eq!(state.0, Interval::constant(10));
    assert_eq!(state.1, Congruence::Val(10, 0));

    println!("\n--- Analyzing Loop Fixpoint ---");

    for iter in 1..=5 {
        println!("Iteration {}:", iter);

        // 1. Body: i -= 2
        // Interval: [low-2, high-2]
        let next_interval = Interval::new(state.0.low.add(&Bound::Finite(-2)), state.0.high.add(&Bound::Finite(-2)));

        // Congruence: (c, k) + (-2, 0)
        let minus_two_cong = congruence_dom.constant(-2);
        let next_congruence = congruence_dom.add(&state.1, &minus_two_cong);

        let next_state = ProductElement(next_interval, next_congruence);

        // 2. Join with previous state (Widen)
        // Interval Widen: [10, 10] ∇ [8, 8] -> [-inf, 10]

        let old_state = state.clone();
        state = product_dom.widen(&state, &next_state);

        // 3. Narrowing: i >= 0
        // Apply loop bound
        if let Bound::Finite(l) = state.0.low {
            if l < 0 {
                state.0.low = Bound::Finite(0);
            }
        } else {
            // Widen went to -infinity, apply loop bound
            state.0.low = Bound::Finite(0);
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
    println!("\n--- Verification ---");

    // 1. Bounds check
    let safe_bounds = match (state.0.low, state.0.high) {
        (Bound::Finite(l), Bound::Finite(h)) => l >= 0 && h <= 10,
        _ => false,
    };
    assert!(safe_bounds, "Bounds check failed: i should be in [0, 10]");
    println!("  ✓ Verified: i is within [0, 10]");

    // 2. Parity check (even numbers)
    let is_even = match state.1 {
        Congruence::Val(c, k) => c % 2 == 0 && k % 2 == 0,
        _ => false,
    };
    assert!(is_even, "Parity check failed: i should be even");
    println!("  ✓ Verified: i is always even");
    println!();
}
