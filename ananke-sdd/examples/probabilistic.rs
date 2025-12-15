//! Probabilistic Inference Example.
//!
//! Demonstrates using SDDs for probabilistic reasoning via Weighted Model Counting (WMC).
//! SDDs enable tractable WMC, the foundation for efficient probabilistic inference
//! in Bayesian networks and probabilistic programs.
//!
//! Scenario: Simple Medical Diagnosis Network with actual probability weights.
//!
//! Run with: `cargo run --example probabilistic`

use ananke_sdd::SddManager;

fn main() {
    println!("─── Probabilistic Inference with SDDs ───\n");
    println!("Scenario: Medical Diagnosis Network\n");

    // ────────────────────────────────────────────────────────────────────────
    // PROBLEM SETUP
    // ────────────────────────────────────────────────────────────────────────

    println!("── Problem Setup ──\n");

    println!("Variables:");
    println!("  x₁ = Disease (flu)");
    println!("  x₂ = Fever (symptom)");
    println!("  x₃ = Cough (symptom)");
    println!();

    println!("Causal structure: D → F, D → C");
    println!("  Disease can cause both fever and cough.\n");

    println!("Prior and conditional probabilities:");
    println!("  P(D)    = 0.3       (30% chance of having flu)");
    println!("  P(F|D)  = 0.9       (90% fever if sick)");
    println!("  P(F|¬D) = 0.1       (10% fever otherwise)");
    println!("  P(C|D)  = 0.8       (80% cough if sick)");
    println!("  P(C|¬D) = 0.2       (20% cough otherwise)");
    println!();

    let mgr = SddManager::new(3);

    // Variables: 1=Disease, 2=Fever, 3=Cough
    let d = mgr.var(1);
    let f = mgr.var(2);
    let c = mgr.var(3);
    let not_d = mgr.neg(d);

    // ────────────────────────────────────────────────────────────────────────
    // WEIGHTED MODEL COUNTING BASICS
    // ────────────────────────────────────────────────────────────────────────

    println!("── 1. Weighted Model Counting (WMC) ──\n");

    println!("WMC assigns weights to literals:");
    println!("  WMC(f) = Σ over models m |= f of Π over literals l in m of w(l)\n");

    println!("Weight arrays (index = variable, 0 is unused):");
    println!("  pos_weights[i] = weight of positive literal xᵢ");
    println!("  neg_weights[i] = weight of negative literal ¬xᵢ");
    println!();

    // ────────────────────────────────────────────────────────────────────────
    // SIMPLE PRIOR COMPUTATION
    // ────────────────────────────────────────────────────────────────────────

    println!("── 2. Computing Prior Probabilities ──\n");

    // Weight arrays: index 0 unused, indices 1-3 for variables
    // For Disease (var 1): prior probability
    // For Fever and Cough, use 0.5/0.5 (uniform for now)
    let pos = vec![0.0, 0.3, 0.5, 0.5]; // [unused, P(D), P(F), P(C)]
    let neg = vec![0.0, 0.7, 0.5, 0.5]; // [unused, P(¬D), P(¬F), P(¬C)]

    println!("Weights:");
    println!("  pos = {:?}", pos);
    println!("  neg = {:?}", neg);
    println!();

    let wmc_true = mgr.wmc(mgr.true_sdd(), &pos, &neg);
    println!("WMC(⊤) = {:.4} (normalization: product of all weight sums)", wmc_true);

    let wmc_d = mgr.wmc(d, &pos, &neg);
    println!("WMC(D) = {:.4} = P(D) × P(F or ¬F) × P(C or ¬C)", wmc_d);

    let wmc_not_d = mgr.wmc(not_d, &pos, &neg);
    println!("WMC(¬D) = {:.4} = P(¬D) × ...", wmc_not_d);
    println!();

    let p_d = wmc_d / wmc_true;
    let p_not_d = wmc_not_d / wmc_true;
    println!("Normalized probabilities:");
    println!("  P(D)  = WMC(D) / WMC(⊤)  = {:.4} / {:.4} = {:.4}", wmc_d, wmc_true, p_d);
    println!("  P(¬D) = WMC(¬D) / WMC(⊤) = {:.4} / {:.4} = {:.4}", wmc_not_d, wmc_true, p_not_d);
    println!("  Sum: {:.4}", p_d + p_not_d);
    println!();

    // ────────────────────────────────────────────────────────────────────────
    // JOINT PROBABILITY
    // ────────────────────────────────────────────────────────────────────────

    println!("── 3. Joint Probability ──\n");

    let d_and_f = mgr.and(d, f);
    let d_and_not_f = mgr.and(d, mgr.neg(f));

    let wmc_df = mgr.wmc(d_and_f, &pos, &neg);
    let wmc_d_nf = mgr.wmc(d_and_not_f, &pos, &neg);

    println!("Joint probabilities with uniform F weights:");
    println!("  WMC(D ∧ F) = {:.4}", wmc_df);
    println!("  WMC(D ∧ ¬F) = {:.4}", wmc_d_nf);
    println!();

    // ────────────────────────────────────────────────────────────────────────
    // BAYESIAN NETWORK ENCODING
    // ────────────────────────────────────────────────────────────────────────

    println!("── 4. Encoding Bayesian Network ──\n");

    println!("For a Bayesian network, we compute joint probability directly:");
    println!("  P(D,F,C) = P(D) × P(F|D) × P(C|D)\n");

    let pd = 0.3;
    let p_f_given_d = 0.9;
    let p_f_given_not_d = 0.1;
    let p_c_given_d = 0.8;
    let p_c_given_not_d = 0.2;

    println!("Computing P(D,F,C) for all configurations:\n");

    println!("  D  F  C   P(D,F,C)");
    println!("  ─  ─  ─   ────────");

    let configs = [
        (true, true, true),
        (true, true, false),
        (true, false, true),
        (true, false, false),
        (false, true, true),
        (false, true, false),
        (false, false, true),
        (false, false, false),
    ];

    let mut joint_probs = vec![];

    for (d_val, f_val, c_val) in configs {
        let p_d_term = if d_val { pd } else { 1.0 - pd };
        let p_f_term = if d_val {
            if f_val {
                p_f_given_d
            } else {
                1.0 - p_f_given_d
            }
        } else if f_val {
            p_f_given_not_d
        } else {
            1.0 - p_f_given_not_d
        };
        let p_c_term = if d_val {
            if c_val {
                p_c_given_d
            } else {
                1.0 - p_c_given_d
            }
        } else if c_val {
            p_c_given_not_d
        } else {
            1.0 - p_c_given_not_d
        };

        let joint = p_d_term * p_f_term * p_c_term;
        joint_probs.push(((d_val, f_val, c_val), joint));

        println!("  {}  {}  {}   {:.4}", b(d_val), b(f_val), b(c_val), joint);
    }

    let total: f64 = joint_probs.iter().map(|(_, p)| p).sum();
    println!();
    println!("  Total: {:.4} (should be 1.0)", total);
    println!();

    // ────────────────────────────────────────────────────────────────────────
    // MARGINAL PROBABILITY
    // ────────────────────────────────────────────────────────────────────────

    println!("── 5. Marginal Probabilities ──\n");

    let p_fever: f64 = joint_probs.iter().filter(|((_, f, _), _)| *f).map(|(_, p)| p).sum();

    let p_cough: f64 = joint_probs.iter().filter(|((_, _, c), _)| *c).map(|(_, p)| p).sum();

    println!("Marginal probabilities:");
    println!("  P(Fever) = {:.4}", p_fever);
    println!("  P(Cough) = {:.4}", p_cough);
    println!();

    // ────────────────────────────────────────────────────────────────────────
    // CONDITIONAL PROBABILITY (INFERENCE)
    // ────────────────────────────────────────────────────────────────────────

    println!("── 6. Conditional Probability (Inference) ──\n");

    println!("Key inference: P(D | F, C) = P(D, F, C) / P(F, C)\n");

    // P(F, C)
    let p_fc: f64 = joint_probs.iter().filter(|((_, f, c), _)| *f && *c).map(|(_, p)| p).sum();

    // P(D, F, C)
    let p_dfc = joint_probs.iter().find(|((d, f, c), _)| *d && *f && *c).map(|(_, p)| *p).unwrap();

    let p_d_given_fc = p_dfc / p_fc;

    println!("Given: Patient has Fever AND Cough\n");
    println!("  P(F, C) = {:.4}", p_fc);
    println!("  P(D, F, C) = {:.4}", p_dfc);
    println!("  P(D | F, C) = {:.4} / {:.4} = {:.4}", p_dfc, p_fc, p_d_given_fc);
    println!();
    println!("Interpretation: {:.1}% chance of flu given both symptoms", p_d_given_fc * 100.0);
    println!();

    // ────────────────────────────────────────────────────────────────────────
    // SDD WMC FOR INFERENCE
    // ────────────────────────────────────────────────────────────────────────

    println!("── 7. SDD WMC for Inference ──\n");

    println!("SDDs compute conditional probabilities via WMC.\n");

    // Using uniform weights (for comparison)
    let uniform_pos = vec![0.0, 0.5, 0.5, 0.5];
    let uniform_neg = vec![0.0, 0.5, 0.5, 0.5];

    let evidence = mgr.and(f, c); // F ∧ C

    let wmc_evidence_u = mgr.wmc(evidence, &uniform_pos, &uniform_neg);
    let wmc_joint_u = mgr.wmc(mgr.and(d, evidence), &uniform_pos, &uniform_neg);

    println!("With uniform weights (0.5/0.5):");
    println!("  WMC(F ∧ C) = {:.4}", wmc_evidence_u);
    println!("  WMC(D ∧ F ∧ C) = {:.4}", wmc_joint_u);
    println!("  P(D | F, C) = {:.4}", wmc_joint_u / wmc_evidence_u);
    println!();

    // Using biased weights
    let biased_pos = vec![0.0, 0.3, 0.8, 0.7]; // favor D, F, C being true
    let biased_neg = vec![0.0, 0.7, 0.2, 0.3];

    let wmc_evidence_b = mgr.wmc(evidence, &biased_pos, &biased_neg);
    let wmc_joint_b = mgr.wmc(mgr.and(d, evidence), &biased_pos, &biased_neg);

    println!("With biased weights (higher prob for symptoms):");
    println!("  WMC(F ∧ C) = {:.4}", wmc_evidence_b);
    println!("  WMC(D ∧ F ∧ C) = {:.4}", wmc_joint_b);
    println!("  P(D | F, C) = {:.4}", wmc_joint_b / wmc_evidence_b);
    println!();

    // ────────────────────────────────────────────────────────────────────────
    // LARGER NETWORK
    // ────────────────────────────────────────────────────────────────────────

    println!("── 8. Scaling: Constraint Network ──\n");

    let mgr6 = SddManager::new(6);
    let vars: Vec<_> = (1..=6).map(|i| mgr6.var(i)).collect();

    // Network structure
    let c1 = mgr6.implies(vars[0], vars[1]); // A → B
    let c2 = mgr6.implies(vars[0], vars[2]); // A → C
    let c3 = mgr6.implies(vars[1], vars[3]); // B → D
    let c4 = mgr6.implies(vars[2], vars[4]); // C → E
    let c5 = mgr6.implies(mgr6.or(vars[3], vars[4]), vars[5]); // D∨E → F

    let network = mgr6.and_all([c1, c2, c3, c4, c5]);

    println!("Network: (A→B) ∧ (A→C) ∧ (B→D) ∧ (C→E) ∧ ((D∨E)→F)\n");
    println!("  SDD size: {} nodes", mgr6.size(network));
    println!("  Valid configurations: {}", mgr6.model_count(network));
    println!();

    // Weights for 6 variables
    let pos6 = vec![0.0, 0.4, 0.5, 0.5, 0.6, 0.6, 0.7];
    let neg6 = vec![0.0, 0.6, 0.5, 0.5, 0.4, 0.4, 0.3];

    let wmc_network = mgr6.wmc(network, &pos6, &neg6);
    println!("WMC(network) = {:.4}", wmc_network);

    // P(F | A) under network
    let with_a = mgr6.and(network, vars[0]);
    let with_a_and_f = mgr6.and(with_a, vars[5]);

    let wmc_a = mgr6.wmc(with_a, &pos6, &neg6);
    let wmc_af = mgr6.wmc(with_a_and_f, &pos6, &neg6);

    println!();
    println!("Conditional query: P(F | A, network)");
    println!("  WMC(A ∧ network) = {:.4}", wmc_a);
    println!("  WMC(A ∧ F ∧ network) = {:.4}", wmc_af);
    println!("  P(F | A) = {:.4}", wmc_af / wmc_a);
    println!();

    // ────────────────────────────────────────────────────────────────────────
    // SUMMARY
    // ────────────────────────────────────────────────────────────────────────

    println!("─── Summary ───\n");

    println!("SDDs enable efficient probabilistic inference via WMC:");
    println!("  • Compile network structure once");
    println!("  • Answer probability queries in O(|SDD|) time");
    println!("  • Support evidence incorporation via conditioning");
    println!("  • Foundation for probabilistic circuits and ML");
    println!();
    println!("Key formula: P(Q | E) = WMC(Q ∧ E ∧ KB) / WMC(E ∧ KB)");
    println!();

    println!("Done.");
}

/// Helper: boolean to 0/1.
fn b(v: bool) -> char {
    if v {
        '1'
    } else {
        '0'
    }
}
