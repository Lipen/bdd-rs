//! Core tests for the SDD library.
//!
//! Tests cover literals, SDDs, vtrees, and manager operations.

use ananke_sdd::{Literal, SddManager};
use num_bigint::BigUint;

// ─── Literal Tests ─────────────────────────────────────────────────────────────

#[test]
fn literal_creation() {
    let pos = Literal::positive(1);
    assert!(pos.is_positive());
    assert!(!pos.is_negative());
    assert_eq!(pos.var(), 1);

    let neg = Literal::negative(1);
    assert!(!neg.is_positive());
    assert!(neg.is_negative());
    assert_eq!(neg.var(), 1);
}

#[test]
fn literal_negation() {
    let pos = Literal::positive(2);
    let neg = -pos;

    assert!(!neg.is_positive());
    assert_eq!(neg.var(), 2);
    assert_eq!(-neg, pos);
}

#[test]
fn literal_evaluation() {
    let pos = Literal::positive(1);
    assert!(pos.polarity()); // positive = true polarity
    assert!(!(-pos).polarity()); // negative = false polarity
}

// ─── Basic SDD Tests ───────────────────────────────────────────────────────────

#[test]
fn constants() {
    let mgr = SddManager::new(2);

    let t = mgr.true_sdd();
    let f = mgr.false_sdd();

    assert!(mgr.is_true(t));
    assert!(mgr.is_false(f));
    assert!(!mgr.is_true(f));
    assert!(!mgr.is_false(t));
}

#[test]
fn variables() {
    let mgr = SddManager::new(3);

    let x1 = mgr.var(1);
    let x2 = mgr.var(2);

    // Variables are not constants
    assert!(!mgr.is_true(x1));
    assert!(!mgr.is_false(x1));

    // Different variables produce different results
    // (Check they're both satisfiable but not tautologies)
    assert!(mgr.is_satisfiable(x1));
    assert!(mgr.is_satisfiable(x2));
}

#[test]
fn negation() {
    let mgr = SddManager::new(2);

    let x = mgr.var(1);
    let nx = mgr.neg(x);
    let nnx = mgr.neg(nx);

    // Double negation is identity (check via satisfiability properties)
    assert!(mgr.is_satisfiable(x));
    assert!(mgr.is_satisfiable(nx));

    // x ∧ ¬x = false
    assert!(mgr.is_false(mgr.and(x, nx)));

    // x ∨ ¬x = true
    assert!(mgr.is_true(mgr.or(x, nx)));

    // ¬¬x has same model count as x
    assert_eq!(mgr.model_count(x), mgr.model_count(nnx));

    // Negation of constants
    assert!(mgr.is_true(mgr.neg(mgr.false_sdd())));
    assert!(mgr.is_false(mgr.neg(mgr.true_sdd())));
}

// ─── Boolean Operations ────────────────────────────────────────────────────────

#[test]
fn and_operation() {
    let mgr = SddManager::new(3);

    let x = mgr.var(1);
    let y = mgr.var(2);

    // x ∧ true = x (same model count)
    assert_eq!(mgr.model_count(mgr.and(x, mgr.true_sdd())), mgr.model_count(x));

    // x ∧ false = false
    assert!(mgr.is_false(mgr.and(x, mgr.false_sdd())));

    // x ∧ x = x (same model count)
    assert_eq!(mgr.model_count(mgr.and(x, x)), mgr.model_count(x));

    // x ∧ ¬x = false
    assert!(mgr.is_false(mgr.and(x, mgr.neg(x))));

    // Commutativity: x ∧ y = y ∧ x (same model count)
    assert_eq!(mgr.model_count(mgr.and(x, y)), mgr.model_count(mgr.and(y, x)));
}

#[test]
fn or_operation() {
    let mgr = SddManager::new(3);

    let x = mgr.var(1);
    let y = mgr.var(2);

    // x ∨ false = x (same model count)
    assert_eq!(mgr.model_count(mgr.or(x, mgr.false_sdd())), mgr.model_count(x));

    // x ∨ true = true
    assert!(mgr.is_true(mgr.or(x, mgr.true_sdd())));

    // x ∨ x = x (same model count)
    assert_eq!(mgr.model_count(mgr.or(x, x)), mgr.model_count(x));

    // x ∨ ¬x = true
    assert!(mgr.is_true(mgr.or(x, mgr.neg(x))));

    // Commutativity: x ∨ y = y ∨ x (same model count)
    assert_eq!(mgr.model_count(mgr.or(x, y)), mgr.model_count(mgr.or(y, x)));
}

#[test]
fn xor_operation() {
    let mgr = SddManager::new(3);

    let x = mgr.var(1);
    let y = mgr.var(2);

    // x ⊕ false = x (same model count)
    assert_eq!(mgr.model_count(mgr.xor(x, mgr.false_sdd())), mgr.model_count(x));

    // x ⊕ true = ¬x (same model count as ¬x)
    assert_eq!(mgr.model_count(mgr.xor(x, mgr.true_sdd())), mgr.model_count(mgr.neg(x)));

    // x ⊕ x = false
    assert!(mgr.is_false(mgr.xor(x, x)));

    // x ⊕ ¬x = true
    assert!(mgr.is_true(mgr.xor(x, mgr.neg(x))));

    // Commutativity: x ⊕ y = y ⊕ x (same model count)
    assert_eq!(mgr.model_count(mgr.xor(x, y)), mgr.model_count(mgr.xor(y, x)));
}

#[test]
fn ite_operation() {
    let mgr = SddManager::new(3);

    let x = mgr.var(1);
    let y = mgr.var(2);
    let z = mgr.var(3);

    // ITE(true, y, z) = y
    assert_eq!(mgr.model_count(mgr.ite(mgr.true_sdd(), y, z)), mgr.model_count(y));

    // ITE(false, y, z) = z
    assert_eq!(mgr.model_count(mgr.ite(mgr.false_sdd(), y, z)), mgr.model_count(z));

    // ITE(x, y, y) = y
    assert_eq!(mgr.model_count(mgr.ite(x, y, y)), mgr.model_count(y));

    // ITE(x, true, false) = x
    assert_eq!(mgr.model_count(mgr.ite(x, mgr.true_sdd(), mgr.false_sdd())), mgr.model_count(x));

    // ITE(x, false, true) = ¬x
    assert_eq!(
        mgr.model_count(mgr.ite(x, mgr.false_sdd(), mgr.true_sdd())),
        mgr.model_count(mgr.neg(x))
    );
}

#[test]
fn implies_operation() {
    let mgr = SddManager::new(3);

    let x = mgr.var(1);
    let y = mgr.var(2);

    // false → x = true
    assert!(mgr.is_true(mgr.implies(mgr.false_sdd(), x)));

    // true → x = x
    assert_eq!(mgr.model_count(mgr.implies(mgr.true_sdd(), x)), mgr.model_count(x));

    // x → true = true
    assert!(mgr.is_true(mgr.implies(x, mgr.true_sdd())));

    // x → false = ¬x
    assert_eq!(mgr.model_count(mgr.implies(x, mgr.false_sdd())), mgr.model_count(mgr.neg(x)));

    // x → x = true
    assert!(mgr.is_true(mgr.implies(x, x)));

    // x → y = ¬x ∨ y (same model count)
    assert_eq!(mgr.model_count(mgr.implies(x, y)), mgr.model_count(mgr.or(mgr.neg(x), y)));
}

#[test]
fn equiv_operation() {
    let mgr = SddManager::new(3);

    let x = mgr.var(1);
    let y = mgr.var(2);

    // x ↔ x = true
    assert!(mgr.is_true(mgr.equiv(x, x)));

    // x ↔ ¬x = false
    assert!(mgr.is_false(mgr.equiv(x, mgr.neg(x))));

    // x ↔ true = x
    assert_eq!(mgr.model_count(mgr.equiv(x, mgr.true_sdd())), mgr.model_count(x));

    // x ↔ false = ¬x
    assert_eq!(mgr.model_count(mgr.equiv(x, mgr.false_sdd())), mgr.model_count(mgr.neg(x)));

    // Commutativity: x ↔ y = y ↔ x
    assert_eq!(mgr.model_count(mgr.equiv(x, y)), mgr.model_count(mgr.equiv(y, x)));

    // x ↔ y = ¬(x ⊕ y) (same model count)
    assert_eq!(mgr.model_count(mgr.equiv(x, y)), mgr.model_count(mgr.neg(mgr.xor(x, y))));
}

// ─── Model Counting ────────────────────────────────────────────────────────────

#[test]
fn model_count_constants() {
    let mgr = SddManager::new(3);

    // false has 0 models
    assert_eq!(mgr.model_count(mgr.false_sdd()), BigUint::from(0u32));

    // true has 2^n models
    assert_eq!(mgr.model_count(mgr.true_sdd()), BigUint::from(8u32));
}

#[test]
fn model_count_single_var() {
    let mgr = SddManager::new(3);

    let x = mgr.var(1);

    // x has 2^(n-1) models (half of all assignments)
    assert_eq!(mgr.model_count(x), BigUint::from(4u32));

    // ¬x also has 2^(n-1) models
    assert_eq!(mgr.model_count(mgr.neg(x)), BigUint::from(4u32));
}

#[test]
fn model_count_conjunction() {
    let mgr = SddManager::new(4);

    let x1 = mgr.var(1);
    let x2 = mgr.var(2);

    // x₁ ∧ x₂ has 2^(n-2) models
    let conj = mgr.and(x1, x2);
    assert_eq!(mgr.model_count(conj), BigUint::from(4u32));

    // x₁ ∧ x₂ ∧ x₃ has 2^(n-3) models
    let conj3 = mgr.and(conj, mgr.var(3));
    assert_eq!(mgr.model_count(conj3), BigUint::from(2u32));
}

#[test]
fn model_count_disjunction() {
    let mgr = SddManager::new(4);

    let x1 = mgr.var(1);
    let x2 = mgr.var(2);

    // x₁ ∨ x₂ has 2^n - 2^(n-2) models = 16 - 4 = 12
    let disj = mgr.or(x1, x2);
    assert_eq!(mgr.model_count(disj), BigUint::from(12u32));
}

#[test]
fn model_count_xor() {
    let mgr = SddManager::new(4);

    // XOR chain has exactly 2^(n-1) models (half true, half false)
    let mut xor = mgr.var(1);
    for i in 2..=4 {
        xor = mgr.xor(xor, mgr.var(i));
    }
    assert_eq!(mgr.model_count(xor), BigUint::from(8u32));
}

// ─── Satisfiability ────────────────────────────────────────────────────────────

#[test]
fn any_sat_constants() {
    let mgr = SddManager::new(3);

    assert!(mgr.any_sat(mgr.false_sdd()).is_none());
    assert!(mgr.any_sat(mgr.true_sdd()).is_some());
}

#[test]
fn any_sat_conjunction() {
    let mgr = SddManager::new(3);

    let x1 = mgr.var(1);
    let x2 = mgr.var(2);
    let conj = mgr.and(x1, x2);

    let sat = mgr.any_sat(conj).expect("Should have a model");

    // Both x1 and x2 must be true (positive in the assignment)
    // The result is a Vec<i32> where positive means true
    assert!(sat.iter().any(|&lit| lit == 1)); // x1 = true
    assert!(sat.iter().any(|&lit| lit == 2)); // x2 = true
}

// ─── Quantification ────────────────────────────────────────────────────────────

#[test]
fn existential_quantification() {
    let mgr = SddManager::new(3);

    let x = mgr.var(1);
    let y = mgr.var(2);

    // ∃x.(x ∧ y) = y (same model count)
    let conj = mgr.and(x, y);
    let exists_x = mgr.exists(conj, 1);
    assert_eq!(mgr.model_count(exists_x), mgr.model_count(y));

    // ∃x.x = true
    let exists_self = mgr.exists(x, 1);
    assert!(mgr.is_true(exists_self));

    // ∃x.¬x = true
    let exists_neg = mgr.exists(mgr.neg(x), 1);
    assert!(mgr.is_true(exists_neg));
}

#[test]
fn universal_quantification() {
    let mgr = SddManager::new(3);

    let x = mgr.var(1);
    let y = mgr.var(2);

    // ∀x.(x ∨ y) = y (same model count)
    let disj = mgr.or(x, y);
    let forall_x = mgr.forall(disj, 1);
    assert_eq!(mgr.model_count(forall_x), mgr.model_count(y));

    // ∀x.x = false
    let forall_self = mgr.forall(x, 1);
    assert!(mgr.is_false(forall_self));

    // ∀x.true = true
    let forall_true = mgr.forall(mgr.true_sdd(), 1);
    assert!(mgr.is_true(forall_true));
}

// ─── Vtree Types ───────────────────────────────────────────────────────────────

#[test]
fn balanced_vtree() {
    let mgr = SddManager::new(4);

    // Should create valid SDDs
    let x1 = mgr.var(1);
    let x4 = mgr.var(4);
    let conj = mgr.and(x1, x4);

    assert!(!mgr.is_false(conj));
    assert_eq!(mgr.model_count(conj), BigUint::from(4u32));
}

#[test]
fn right_linear_vtree() {
    let mgr = SddManager::with_right_linear_vtree(4);

    let x1 = mgr.var(1);
    let x4 = mgr.var(4);
    let conj = mgr.and(x1, x4);

    assert!(!mgr.is_false(conj));
    assert_eq!(mgr.model_count(conj), BigUint::from(4u32));
}

#[test]
fn left_linear_vtree() {
    let mgr = SddManager::with_left_linear_vtree(4);

    let x1 = mgr.var(1);
    let x4 = mgr.var(4);
    let conj = mgr.and(x1, x4);

    assert!(!mgr.is_false(conj));
    assert_eq!(mgr.model_count(conj), BigUint::from(4u32));
}

// ─── Complex Formulas ──────────────────────────────────────────────────────────

#[test]
fn at_most_one() {
    let mgr = SddManager::new(3);

    let x1 = mgr.var(1);
    let x2 = mgr.var(2);
    let x3 = mgr.var(3);

    // At most one of x1, x2, x3 is true
    // = ¬(x1 ∧ x2) ∧ ¬(x1 ∧ x3) ∧ ¬(x2 ∧ x3)
    let c1 = mgr.neg(mgr.and(x1, x2));
    let c2 = mgr.neg(mgr.and(x1, x3));
    let c3 = mgr.neg(mgr.and(x2, x3));
    let amo = mgr.and(mgr.and(c1, c2), c3);

    // Models: 000, 001, 010, 100 = 4 models
    assert_eq!(mgr.model_count(amo), BigUint::from(4u32));
}

#[test]
fn exactly_one() {
    let mgr = SddManager::new(3);

    let x1 = mgr.var(1);
    let x2 = mgr.var(2);
    let x3 = mgr.var(3);

    // At least one
    let alo = mgr.or(mgr.or(x1, x2), x3);

    // At most one
    let c1 = mgr.neg(mgr.and(x1, x2));
    let c2 = mgr.neg(mgr.and(x1, x3));
    let c3 = mgr.neg(mgr.and(x2, x3));
    let amo = mgr.and(mgr.and(c1, c2), c3);

    // Exactly one = at least one ∧ at most one
    let exo = mgr.and(alo, amo);

    // Models: 001, 010, 100 = 3 models
    assert_eq!(mgr.model_count(exo), BigUint::from(3u32));
}

#[test]
fn de_morgan() {
    let mgr = SddManager::new(3);

    let x = mgr.var(1);
    let y = mgr.var(2);

    // ¬(x ∧ y) = ¬x ∨ ¬y (same model count)
    let lhs = mgr.neg(mgr.and(x, y));
    let rhs = mgr.or(mgr.neg(x), mgr.neg(y));
    assert_eq!(mgr.model_count(lhs), mgr.model_count(rhs));

    // ¬(x ∨ y) = ¬x ∧ ¬y (same model count)
    let lhs2 = mgr.neg(mgr.or(x, y));
    let rhs2 = mgr.and(mgr.neg(x), mgr.neg(y));
    assert_eq!(mgr.model_count(lhs2), mgr.model_count(rhs2));
}

#[test]
fn distributivity() {
    let mgr = SddManager::new(4);

    let x = mgr.var(1);
    let y = mgr.var(2);
    let z = mgr.var(3);

    // x ∧ (y ∨ z) = (x ∧ y) ∨ (x ∧ z) (same model count)
    let lhs = mgr.and(x, mgr.or(y, z));
    let rhs = mgr.or(mgr.and(x, y), mgr.and(x, z));
    assert_eq!(mgr.model_count(lhs), mgr.model_count(rhs));

    // x ∨ (y ∧ z) = (x ∨ y) ∧ (x ∨ z) (same model count)
    let lhs2 = mgr.or(x, mgr.and(y, z));
    let rhs2 = mgr.and(mgr.or(x, y), mgr.or(x, z));
    assert_eq!(mgr.model_count(lhs2), mgr.model_count(rhs2));
}

#[test]
fn associativity() {
    let mgr = SddManager::new(4);

    let x = mgr.var(1);
    let y = mgr.var(2);
    let z = mgr.var(3);

    // (x ∧ y) ∧ z = x ∧ (y ∧ z) (same model count)
    let lhs = mgr.and(mgr.and(x, y), z);
    let rhs = mgr.and(x, mgr.and(y, z));
    assert_eq!(mgr.model_count(lhs), mgr.model_count(rhs));

    // (x ∨ y) ∨ z = x ∨ (y ∨ z) (same model count)
    let lhs2 = mgr.or(mgr.or(x, y), z);
    let rhs2 = mgr.or(x, mgr.or(y, z));
    assert_eq!(mgr.model_count(lhs2), mgr.model_count(rhs2));
}

// ─── Weighted Model Count ──────────────────────────────────────────────────────

#[test]
fn wmc_uniform_weights() {
    let mgr = SddManager::new(3);

    // With uniform weights (all 1.0), WMC equals model count
    let pos = vec![0.0, 1.0, 1.0, 1.0];
    let neg = vec![0.0, 1.0, 1.0, 1.0];

    // TRUE has 2^3 = 8 models
    assert!((mgr.wmc(mgr.true_sdd(), &pos, &neg) - 8.0).abs() < 1e-10);

    // FALSE has 0 models
    assert!((mgr.wmc(mgr.false_sdd(), &pos, &neg) - 0.0).abs() < 1e-10);

    // x1 has 4 models
    let x1 = mgr.var(1);
    assert!((mgr.wmc(x1, &pos, &neg) - 4.0).abs() < 1e-10);

    // x1 ∧ x2 has 2 models
    let x1_and_x2 = mgr.and(mgr.var(1), mgr.var(2));
    assert!((mgr.wmc(x1_and_x2, &pos, &neg) - 2.0).abs() < 1e-10);
}

#[test]
fn wmc_probability_weights() {
    let mgr = SddManager::new(2);

    // Weights as probabilities: pos[i] = P(x_i = true), neg[i] = P(x_i = false)
    let pos = vec![0.0, 0.3, 0.6];
    let neg = vec![0.0, 0.7, 0.4];

    // TRUE: (0.3 + 0.7) * (0.6 + 0.4) = 1.0
    assert!((mgr.wmc(mgr.true_sdd(), &pos, &neg) - 1.0).abs() < 1e-10);

    // x1: 0.3 * (0.6 + 0.4) = 0.3
    let x1 = mgr.var(1);
    assert!((mgr.wmc(x1, &pos, &neg) - 0.3).abs() < 1e-10);

    // ¬x1: 0.7 * 1.0 = 0.7
    assert!((mgr.wmc(mgr.neg(x1), &pos, &neg) - 0.7).abs() < 1e-10);

    // x1 ∧ x2: 0.3 * 0.6 = 0.18
    let x1_and_x2 = mgr.and(mgr.var(1), mgr.var(2));
    assert!((mgr.wmc(x1_and_x2, &pos, &neg) - 0.18).abs() < 1e-10);

    // x1 ∨ x2: 0.3 * 0.6 + 0.3 * 0.4 + 0.7 * 0.6 = 0.18 + 0.12 + 0.42 = 0.72
    let x1_or_x2 = mgr.or(mgr.var(1), mgr.var(2));
    assert!((mgr.wmc(x1_or_x2, &pos, &neg) - 0.72).abs() < 1e-10);
}

#[test]
fn wmc_xor() {
    let mgr = SddManager::new(2);

    // With uniform weights
    let pos = vec![0.0, 1.0, 1.0];
    let neg = vec![0.0, 1.0, 1.0];

    // x1 XOR x2 has 2 models: (T,F) and (F,T)
    let xor = mgr.xor(mgr.var(1), mgr.var(2));
    assert!((mgr.wmc(xor, &pos, &neg) - 2.0).abs() < 1e-10);

    // With probability weights
    let pos = vec![0.0, 0.5, 0.5];
    let neg = vec![0.0, 0.5, 0.5];

    // XOR: 0.5 * 0.5 + 0.5 * 0.5 = 0.5
    assert!((mgr.wmc(xor, &pos, &neg) - 0.5).abs() < 1e-10);
}

// ─── SDD Size ──────────────────────────────────────────────────────────────────

#[test]
fn size_constants() {
    let mgr = SddManager::new(3);

    // Constants have size 1
    assert_eq!(mgr.size(mgr.true_sdd()), 1);
    assert_eq!(mgr.size(mgr.false_sdd()), 1);
}

#[test]
fn size_variables() {
    let mgr = SddManager::new(3);

    // Literals have size 1
    let x = mgr.var(1);
    assert_eq!(mgr.size(x), 1);

    // Negated literals also have size 1
    assert_eq!(mgr.size(mgr.neg(x)), 1);
}

#[test]
fn size_monotonicity() {
    let mgr = SddManager::new(4);

    let x = mgr.var(1);
    let y = mgr.var(2);
    let z = mgr.var(3);

    let xy = mgr.and(x, y);
    let xyz = mgr.and(xy, z);

    // More complex formula should have >= size
    assert!(mgr.size(xyz) >= mgr.size(xy));
    assert!(mgr.size(xy) >= mgr.size(x));
}
