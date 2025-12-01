//! Abstract Domains Example
//!
//! Demonstrates the use of abstract domains for constraint solving.
//!
//! Run with: `cargo run -p tbdd-pbt --example abstract_domains`

use tbdd_pbt::domain::{
    AbstractDomain, Concretizable, Congruence, DomainState, Interval, PredicateTransfer, ReducedProduct, Sign,
};
use tbdd_pbt::predicate::CompareOp;

fn main() {
    println!("══════════════════════════════════════════════════════════════");
    println!("  T-BDD: Abstract Domains for Constraint Solving");
    println!("══════════════════════════════════════════════════════════════\n");

    // ─────────────────────────────────────────────────────────────────────────
    // Interval Domain
    // ─────────────────────────────────────────────────────────────────────────

    println!("── INTERVAL DOMAIN ──────────────────────────────────────────────");
    println!();

    let i1 = Interval::from_bounds(0, 100);
    let i2 = Interval::from_bounds(50, 150);

    println!("  i1 = {:?}", i1);
    println!("  i2 = {:?}", i2);
    println!();
    println!("  i1 ⊔ i2 (join)  = {:?}", i1.join(&i2));
    println!("  i1 ⊓ i2 (meet)  = {:?}", i1.meet(&i2));
    println!("  i1 ⊑ i2 (leq)   = {}", i1.leq(&i2));
    println!();

    // Predicate transfer
    let top = Interval::top();
    println!("  Predicate transfer from ⊤:");
    println!("    x < 10   → {:?}", top.transfer(CompareOp::Lt, 10, true));
    println!("    x >= 50  → {:?}", top.transfer(CompareOp::Ge, 50, true));
    println!("    x == 42  → {:?}", top.transfer(CompareOp::Eq, 42, true));
    println!();

    // Chained constraints
    let mut x = Interval::top();
    println!("  Chained constraints:");
    println!("    Start:   {:?}", x);
    x = x.transfer(CompareOp::Ge, 0, true);
    println!("    x >= 0:  {:?}", x);
    x = x.transfer(CompareOp::Lt, 100, true);
    println!("    x < 100: {:?}", x);
    x = x.transfer(CompareOp::Ne, 50, true); // != is imprecise
    println!("    x != 50: {:?} (imprecise)", x);
    println!();

    // Widening
    println!("  Widening (loop iteration):");
    let mut loop_var = Interval::constant(0);
    println!("    Iter 0: {:?}", loop_var);
    loop_var = loop_var.join(&Interval::constant(1));
    println!("    Iter 1: {:?}", loop_var);
    loop_var = loop_var.widen(&Interval::from_bounds(0, 2));
    println!("    Widen:  {:?}", loop_var);
    println!();

    // Concretization
    println!("  Concretization:");
    let interval = Interval::from_bounds(-10, 10);
    println!("    {:?} → concrete: {:?}", interval, interval.concretize());
    println!("    samples: {:?}", interval.sample(5));
    println!();

    // ─────────────────────────────────────────────────────────────────────────
    // Sign Domain
    // ─────────────────────────────────────────────────────────────────────────

    println!("── SIGN DOMAIN ──────────────────────────────────────────────────");
    println!();

    use Sign::*;

    println!("  Lattice structure:");
    println!("                 Top");
    println!("              /   |   \\");
    println!("         NonNeg NonZero NonPos");
    println!("          / \\     |    / \\");
    println!("        Pos Zero     Zero Neg");
    println!("          \\   |     |   /");
    println!("              Bottom");
    println!();

    println!("  Join operations:");
    println!("    Neg ⊔ Pos  = {:?}", Negative.join(&Positive));
    println!("    Neg ⊔ Zero = {:?}", Negative.join(&Zero));
    println!("    Pos ⊔ Zero = {:?}", Positive.join(&Zero));
    println!();

    println!("  Meet operations:");
    println!("    NonNeg ⊓ NonPos = {:?}", NonNegative.meet(&NonPositive));
    println!("    NonNeg ⊓ NonZero = {:?}", NonNegative.meet(&NonZero));
    println!();

    println!("  Predicate transfer:");
    println!("    ⊤ with x < 0  → {:?}", Top.transfer(CompareOp::Lt, 0, true));
    println!("    ⊤ with x >= 0 → {:?}", Top.transfer(CompareOp::Ge, 0, true));
    println!("    ⊤ with x == 0 → {:?}", Top.transfer(CompareOp::Eq, 0, true));
    println!("    ⊤ with x != 0 → {:?}", Top.transfer(CompareOp::Ne, 0, true));
    println!();

    println!("  Concretization:");
    println!("    Negative → {:?}", Negative.concretize());
    println!("    Positive → {:?}", Positive.concretize());
    println!("    NonZero samples → {:?}", NonZero.sample(4));
    println!();

    // ─────────────────────────────────────────────────────────────────────────
    // Congruence Domain
    // ─────────────────────────────────────────────────────────────────────────

    println!("── CONGRUENCE DOMAIN ────────────────────────────────────────────");
    println!();

    let even = Congruence::new(2, 0);
    let odd = Congruence::new(2, 1);
    let div4 = Congruence::new(4, 0);
    let aligned8 = Congruence::aligned(8);

    println!("  even = x ≡ 0 (mod 2)");
    println!("  odd  = x ≡ 1 (mod 2)");
    println!("  div4 = x ≡ 0 (mod 4)");
    println!("  aligned8 = x ≡ 0 (mod 8)");
    println!();

    println!("  Membership:");
    println!("    even.contains(0)  = {}", even.contains(0));
    println!("    even.contains(1)  = {}", even.contains(1));
    println!("    even.contains(42) = {}", even.contains(42));
    println!();

    println!("  Operations:");
    println!("    even ⊔ odd  = {:?}", even.join(&odd));
    println!("    even ⊓ odd  = {:?}", even.meet(&odd));
    println!(
        "    even ⊓ div4 = mod {}, rem {}",
        even.meet(&div4).modulus(),
        even.meet(&div4).remainder()
    );
    println!();

    println!("  Samples from aligned8: {:?}", aligned8.sample(5));
    println!();

    // ─────────────────────────────────────────────────────────────────────────
    // Reduced Product
    // ─────────────────────────────────────────────────────────────────────────

    println!("── REDUCED PRODUCT ──────────────────────────────────────────────");
    println!();

    let interval = Interval::from_bounds(-10, 10);
    let sign = Sign::NonNegative;
    let product = ReducedProduct::new(interval.clone(), sign);

    println!("  Product of:");
    println!("    Interval: {:?}", interval);
    println!("    Sign:     {:?}", sign);
    println!();
    println!("  is_bottom: {}", product.is_bottom());
    println!("  concrete:  {:?}", product.concretize());
    println!();

    // Example: combined analysis would refine interval to [0, 10]
    println!("  Combined analysis insight:");
    println!("    Interval [-10, 10] ∧ NonNegative → should refine to [0, 10]");
    println!("    (Full reduction not yet implemented)");
    println!();

    // ─────────────────────────────────────────────────────────────────────────
    // Domain State
    // ─────────────────────────────────────────────────────────────────────────

    println!("── DOMAIN STATE (Multi-Variable) ────────────────────────────────");
    println!();

    let mut state: DomainState<Interval> = DomainState::new();

    println!("  Initial state: all variables are ⊤");
    println!();

    // Apply constraints
    state.set("x", Interval::from_bounds(0, 100));
    state.set("y", Interval::from_bounds(-50, 50));

    println!("  After x ∈ [0, 100], y ∈ [-50, 50]:");
    println!("    x = {:?}", state.get("x"));
    println!("    y = {:?}", state.get("y"));
    println!("    z = {:?} (not constrained)", state.get("z"));
    println!();

    // Generate witness
    let witness = state.to_witness();
    println!("  Generated witness:");
    if let Some(w) = witness {
        for (var, val) in &w.values {
            println!("    {} = {}", var, val);
        }
    }
    println!();

    // ─────────────────────────────────────────────────────────────────────────
    // Precision Comparison
    // ─────────────────────────────────────────────────────────────────────────

    println!("── PRECISION COMPARISON ─────────────────────────────────────────");
    println!();

    println!("  Testing constraint: x >= 0 ∧ x < 10 ∧ x % 2 == 0");
    println!();

    // Interval only
    let mut interval_only = Interval::top();
    interval_only = interval_only.transfer(CompareOp::Ge, 0, true);
    interval_only = interval_only.transfer(CompareOp::Lt, 10, true);
    println!("  Interval alone: {:?}", interval_only);
    println!("    Possible values: any in [0, 9]");

    // Congruence only
    let _congruence_only = Congruence::new(2, 0);
    println!("  Congruence alone: x ≡ 0 (mod 2)");
    println!("    Possible values: ..., -2, 0, 2, 4, ...");

    // Ideally combined
    println!();
    println!("  Combined (ideal): [0, 9] ∩ (even)");
    println!("    Possible values: 0, 2, 4, 6, 8");
    println!("    (5 values vs 10 from interval alone)");
    println!();

    println!("══════════════════════════════════════════════════════════════");
    println!("  Abstract domains demonstration complete!");
    println!("══════════════════════════════════════════════════════════════");
}
