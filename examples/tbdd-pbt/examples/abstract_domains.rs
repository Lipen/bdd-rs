//! Abstract Domains Example
//!
//! Demonstrates the use of abstract domains for constraint solving.
//!
//! Run with: `cargo run -p tbdd-pbt --example abstract_domains`

use tbdd_pbt::domain::{
    AbstractDomain, Concretizable, Congruence, DomainState, Interval, Parity, PredicateTransfer, ReducedProduct, Reducible, Sign,
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
    println!("    ⊤ with x < 0  → {:?}", Sign::Top.transfer(CompareOp::Lt, 0, true));
    println!("    ⊤ with x >= 0 → {:?}", Sign::Top.transfer(CompareOp::Ge, 0, true));
    println!("    ⊤ with x == 0 → {:?}", Sign::Top.transfer(CompareOp::Eq, 0, true));
    println!("    ⊤ with x != 0 → {:?}", Sign::Top.transfer(CompareOp::Ne, 0, true));
    println!();

    println!("  Concretization:");
    println!("    Negative → {:?}", Negative.concretize());
    println!("    Positive → {:?}", Positive.concretize());
    println!("    NonZero samples → {:?}", NonZero.sample(4));
    println!();

    // ─────────────────────────────────────────────────────────────────────────
    // Parity Domain
    // ─────────────────────────────────────────────────────────────────────────

    println!("── PARITY DOMAIN ────────────────────────────────────────────────");
    println!();

    println!("  Lattice structure:");
    println!("         ⊤ (any)");
    println!("        / \\");
    println!("     Even  Odd");
    println!("        \\ /");
    println!("         ⊥");
    println!();

    println!("  Membership:");
    println!("    Even.contains(0)  = {}", Parity::Even.contains(0));
    println!("    Even.contains(1)  = {}", Parity::Even.contains(1));
    println!("    Even.contains(42) = {}", Parity::Even.contains(42));
    println!("    Odd.contains(0)   = {}", Parity::Odd.contains(0));
    println!("    Odd.contains(7)   = {}", Parity::Odd.contains(7));
    println!();

    println!("  Join operations:");
    println!("    Even ⊔ Odd    = {:?}", Parity::Even.join(&Parity::Odd));
    println!("    Even ⊔ Even   = {:?}", Parity::Even.join(&Parity::Even));
    println!("    Even ⊔ Bottom = {:?}", Parity::Even.join(&Parity::Bottom));
    println!();

    println!("  Meet operations:");
    println!("    Even ⊓ Odd = {:?}", Parity::Even.meet(&Parity::Odd));
    println!("    Even ⊓ Top = {:?}", Parity::Even.meet(&Parity::Top));
    println!();

    println!("  Predicate transfer:");
    println!("    ⊤ with x == 0  → {:?}", Parity::Top.transfer(CompareOp::Eq, 0, true));
    println!("    ⊤ with x == 7  → {:?}", Parity::Top.transfer(CompareOp::Eq, 7, true));
    println!("    ⊤ with x != 0  → {:?}", Parity::Top.transfer(CompareOp::Ne, 0, true));
    println!();

    println!("  Concretization:");
    println!("    Even samples → {:?}", Parity::Even.sample(5));
    println!("    Odd samples  → {:?}", Parity::Odd.sample(5));
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

    println!("  The Reducible trait enables cross-domain constraint propagation.");
    println!();

    // Interval × Sign reduction
    println!("  Interval.reduce(Sign):");
    let interval = Interval::from_bounds(-10, 10);
    println!("    [-10, 10].reduce(Positive) → {:?}", interval.reduce(&Sign::Positive));
    println!("    [-10, 10].reduce(Negative) → {:?}", interval.reduce(&Sign::Negative));
    println!("    [-10, 10].reduce(Zero)     → {:?}", interval.reduce(&Sign::Zero));
    println!("    [-10, 10].reduce(NonNeg)   → {:?}", interval.reduce(&Sign::NonNegative));
    println!();

    // Sign × Interval reduction
    println!("  Sign.reduce(Interval):");
    println!("    Top.reduce([1, 10])   → {:?}", Sign::Top.reduce(&Interval::from_bounds(1, 10)));
    println!(
        "    Top.reduce([-10, -1]) → {:?}",
        Sign::Top.reduce(&Interval::from_bounds(-10, -1))
    );
    println!("    Top.reduce([0, 0])    → {:?}", Sign::Top.reduce(&Interval::from_bounds(0, 0)));
    println!("    Top.reduce([-5, 5])   → {:?}", Sign::Top.reduce(&Interval::from_bounds(-5, 5)));
    println!();

    // Parity × Sign reduction (zero is even!)
    println!("  Parity.reduce(Sign) — Zero is even!");
    println!("    Top.reduce(Zero)    → {:?}", Parity::Top.reduce(&Sign::Zero));
    println!("    Odd.reduce(Zero)    → {:?}", Parity::Odd.reduce(&Sign::Zero));
    println!("    Even.reduce(NonZero) → {:?}", Parity::Even.reduce(&Sign::NonZero));
    println!();

    // Sign × Parity reduction
    println!("  Sign.reduce(Parity):");
    println!("    Zero.reduce(Odd)    → {:?}", Sign::Zero.reduce(&Parity::Odd));
    println!("    NonZero.reduce(Even) → {:?}", Sign::NonZero.reduce(&Parity::Even));
    println!("    Top.reduce(Odd)     → {:?}", Sign::Top.reduce(&Parity::Odd));
    println!();

    // ReducedProduct combines domains
    println!("  ReducedProduct combines and reduces:");
    let product = ReducedProduct::new_reduced(Interval::from_bounds(-10, 10), Sign::Positive);
    println!("    new_reduced([-10, 10], Positive):");
    println!("      interval → {:?}", product.d1);
    println!("      sign     → {:?}", product.d2);
    println!();

    // Detecting infeasibility
    let infeasible = ReducedProduct::new_reduced(Interval::from_bounds(1, 10), Sign::Negative);
    println!("    new_reduced([1, 10], Negative):");
    println!("      interval → {:?}", infeasible.d1);
    println!("      sign     → {:?}", infeasible.d2);
    println!("      is_bottom: {}", infeasible.is_bottom());
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

    println!("  Testing constraint: x >= 0 ∧ x < 10 ∧ x is even");
    println!();

    // Interval only
    let mut interval_only = Interval::top();
    interval_only = interval_only.transfer(CompareOp::Ge, 0, true);
    interval_only = interval_only.transfer(CompareOp::Lt, 10, true);
    println!("  Interval alone: {:?}", interval_only);
    println!("    Possible values: any in [0, 9] (10 values)");
    println!();

    // Parity only
    let parity_only = Parity::Even;
    println!("  Parity alone: {:?}", parity_only);
    println!("    Possible values: ..., -2, 0, 2, 4, ... (infinite)");
    println!();

    // Combined with reduction
    let reduced = ReducedProduct::new_reduced(interval_only.clone(), parity_only);
    println!("  Reduced product: Interval × Parity");
    println!("    interval: {:?}", reduced.d1);
    println!("    parity:   {:?}", reduced.d2);
    println!("    Combined: [0, 9] ∧ Even → 0, 2, 4, 6, 8 (5 values)");
    println!();

    // Three-way combination example
    println!("  Three-domain example: Interval × Sign × Parity");
    let i = Interval::from_bounds(-10, 10);
    let s = Sign::Positive;
    let p = Parity::Even;
    println!("    Original:");
    println!("      Interval: {:?}", i);
    println!("      Sign:     {:?}", s);
    println!("      Parity:   {:?}", p);
    // Reduce step by step
    let i_reduced = i.reduce(&s);
    let s_reduced = s.reduce(&i_reduced);
    println!("    After Interval×Sign reduction:");
    println!("      Interval: {:?}", i_reduced);
    println!("      Sign:     {:?}", s_reduced);
    println!("    Combined: [1, 10] ∧ Positive ∧ Even → 2, 4, 6, 8, 10");
    println!();

    println!("══════════════════════════════════════════════════════════════");
    println!("  Abstract domains demonstration complete!");
    println!("══════════════════════════════════════════════════════════════");
}
