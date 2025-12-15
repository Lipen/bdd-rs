//! Explainable Counterexamples via SDD in Bounded Model Checking
//!
//! This example demonstrates how SDDs can provide **structured, decomposed
//! counterexamples** for model checking, going beyond the single linear trace
//! produced by traditional model checkers.
//!
//! # The Problem with Classical Counterexamples
//!
//! Traditional model checking tools (e.g., SPIN, NuSMV) produce:
//! - A **single** linear execution trace
//! - Often **very long** (thousands of steps)
//! - No insight into **which factors** independently cause the violation
//! - No view of the **space** of all counterexamples
//!
//! # SDD-Based Approach
//!
//! SDDs can represent the **entire set** of counterexamples compactly:
//! 1. Encode bounded reachability as a Boolean formula
//! 2. Compile the "bad states" formula into an SDD
//! 3. Analyze the SDD structure to find:
//!    - Independent factors (prime decomposition)
//!    - Invariant variables (always 0 or 1 in all counterexamples)
//!    - Variable groupings that move together
//!
//! # Case Study: Token Ring Protocol
//!
//! A simple mutual exclusion protocol where N processes pass a token:
//! - Only the token holder can enter the critical section
//! - Safety property: at most one process in critical section
//! - We look for bounded paths that violate this property.

use ananke_sdd::{Sdd, SddId, SddManager};
use num_bigint::BigUint;

/// Token Ring Protocol model.
///
/// State encoding for N processes:
/// - `has_token[i]` : process i holds the token
/// - `in_cs[i]`     : process i is in critical section
/// - `waiting[i]`   : process i is waiting to enter CS
///
/// Transitions:
/// - Process with token can enter CS if not already in CS
/// - Process in CS can exit and pass token to next process
/// - Process without token can request entry (set waiting)
struct TokenRingModel {
    num_processes: u32,
    num_steps: u32,
    vars_per_step: u32,
}

impl TokenRingModel {
    fn new(num_processes: u32, num_steps: u32) -> Self {
        // Variables per process per timestep: has_token, in_cs, waiting
        let vars_per_process = 3;
        Self {
            num_processes,
            num_steps,
            vars_per_step: num_processes * vars_per_process,
        }
    }

    fn total_vars(&self) -> u32 {
        self.vars_per_step * (self.num_steps + 1)
    }

    /// Variable index for `has_token[proc]` at time `t`.
    fn has_token(&self, proc: u32, t: u32) -> u32 {
        t * self.vars_per_step + proc * 3 + 1
    }

    /// Variable index for `in_cs[proc]` at time `t`.
    fn in_cs(&self, proc: u32, t: u32) -> u32 {
        t * self.vars_per_step + proc * 3 + 2
    }

    /// Variable index for `waiting[proc]` at time `t`.
    fn waiting(&self, proc: u32, t: u32) -> u32 {
        t * self.vars_per_step + proc * 3 + 3
    }
}

/// Encode initial state: process 0 has token, nobody in CS.
fn initial_state(mgr: &SddManager, model: &TokenRingModel) -> SddId {
    let mut init = mgr.true_sdd();

    for p in 0..model.num_processes {
        // Process 0 has token initially
        let has_tok = mgr.var(model.has_token(p, 0));
        if p == 0 {
            init = mgr.and(init, has_tok);
        } else {
            init = mgr.and(init, mgr.neg(has_tok));
        }

        // Nobody in critical section initially
        let in_critical = mgr.var(model.in_cs(p, 0));
        init = mgr.and(init, mgr.neg(in_critical));

        // Nobody waiting initially
        let wait = mgr.var(model.waiting(p, 0));
        init = mgr.and(init, mgr.neg(wait));
    }

    init
}

/// Encode transition relation from time t to t+1.
fn transition(mgr: &SddManager, model: &TokenRingModel, t: u32) -> SddId {
    let mut trans = mgr.false_sdd();

    for actor in 0..model.num_processes {
        // Action 1: Process with token enters CS (if not already in CS)
        let enter_cs = {
            let has_tok = mgr.var(model.has_token(actor, t));
            let not_in_cs = mgr.neg(mgr.var(model.in_cs(actor, t)));
            let precond = mgr.and(has_tok, not_in_cs);

            // Effect: enter CS, keep token
            let mut effect = mgr.var(model.in_cs(actor, t + 1));
            effect = mgr.and(effect, mgr.var(model.has_token(actor, t + 1)));
            effect = mgr.and(effect, mgr.neg(mgr.var(model.waiting(actor, t + 1))));

            mgr.and(precond, effect)
        };

        // Action 2: Process in CS exits and passes token
        let exit_cs = {
            let in_critical = mgr.var(model.in_cs(actor, t));
            let has_tok = mgr.var(model.has_token(actor, t));
            let precond = mgr.and(in_critical, has_tok);

            // Effect: exit CS, pass token to next process
            let next = (actor + 1) % model.num_processes;
            let mut effect = mgr.neg(mgr.var(model.in_cs(actor, t + 1)));
            effect = mgr.and(effect, mgr.neg(mgr.var(model.has_token(actor, t + 1))));
            effect = mgr.and(effect, mgr.var(model.has_token(next, t + 1)));

            mgr.and(precond, effect)
        };

        // Action 3: Process without token sets waiting flag
        let set_waiting = {
            let no_tok = mgr.neg(mgr.var(model.has_token(actor, t)));
            let not_waiting = mgr.neg(mgr.var(model.waiting(actor, t)));
            let precond = mgr.and(no_tok, not_waiting);

            // Effect: set waiting, preserve other state
            let mut effect = mgr.var(model.waiting(actor, t + 1));
            effect = mgr.and(effect, mgr.neg(mgr.var(model.in_cs(actor, t + 1))));

            mgr.and(precond, effect)
        };

        // Combine all actions for this actor
        let actor_trans = mgr.or(enter_cs, mgr.or(exit_cs, set_waiting));
        trans = mgr.or(trans, actor_trans);
    }

    // Frame axiom: variables not changed by action stay the same
    // (simplified: allow any consistent transition)
    trans
}

/// Bad state: more than one process in critical section.
fn bad_state(mgr: &SddManager, model: &TokenRingModel, t: u32) -> SddId {
    let mut bad = mgr.false_sdd();

    // For each pair of processes, check if both are in CS
    for p1 in 0..model.num_processes {
        for p2 in (p1 + 1)..model.num_processes {
            let p1_in_cs = mgr.var(model.in_cs(p1, t));
            let p2_in_cs = mgr.var(model.in_cs(p2, t));
            let both_in_cs = mgr.and(p1_in_cs, p2_in_cs);
            bad = mgr.or(bad, both_in_cs);
        }
    }

    bad
}

/// Analyze SDD structure to extract explainable counterexample information.
fn analyze_counterexamples(mgr: &SddManager, counterexamples: SddId, model: &TokenRingModel) {
    println!("\n╔══════════════════════════════════════════════════════════════════╗");
    println!("║              SDD COUNTEREXAMPLE ANALYSIS                         ║");
    println!("╚══════════════════════════════════════════════════════════════════╝\n");

    // Basic statistics
    let size = mgr.size(counterexamples);
    let count = mgr.model_count(counterexamples);

    println!("📊 Basic Statistics:");
    println!("   • SDD size: {} nodes", size);
    println!("   • Number of counterexamples: {}", count);
    println!();

    // Analyze which variables are fixed vs free
    println!("🔍 Variable Analysis (invariants in counterexamples):");
    let mut always_true = Vec::new();
    let mut always_false = Vec::new();
    let mut varying = Vec::new();

    for var in 1..=model.total_vars() {
        // Condition on positive and negative literals
        let with_pos = mgr.condition(counterexamples, var as i32);
        let with_neg = mgr.condition(counterexamples, -(var as i32));

        let pos_sat = !mgr.is_false(with_pos);
        let neg_sat = !mgr.is_false(with_neg);

        if pos_sat && !neg_sat {
            always_true.push(var);
        } else if !pos_sat && neg_sat {
            always_false.push(var);
        } else if pos_sat && neg_sat {
            varying.push(var);
        }
    }

    println!("   • Variables always TRUE in counterexamples: {} vars", always_true.len());
    println!("   • Variables always FALSE in counterexamples: {} vars", always_false.len());
    println!("   • Variables that vary across counterexamples: {} vars", varying.len());
    println!();

    // Interpret the fixed variables (only show if non-trivial)
    if !always_true.is_empty() || !always_false.is_empty() {
        println!("📋 Essential Invariants Across Counterexamples:");
        for &var in &always_true {
            let (name, time) = decode_variable(var, model);
            println!("   ✓ {} at t={}", name, time);
        }
        for &var in &always_false {
            let (name, time) = decode_variable(var, model);
            println!("   ✗ {} at t={}", name, time);
        }
        println!();
    }

    // Show one sample counterexample
    println!("📝 Sample Counterexample (one of {}):", count);
    if let Some(assignment) = mgr.any_sat(counterexamples) {
        print_trace(&assignment, model);
    }

    // Analyze prime decomposition at top level
    println!("\n🧩 SDD Prime Decomposition (Independent Factors):");
    analyze_decomposition(mgr, counterexamples, 0);
}

/// Decode a variable number back to semantic meaning.
fn decode_variable(var: u32, model: &TokenRingModel) -> (String, u32) {
    let adjusted = var - 1;
    let time = adjusted / model.vars_per_step;
    let within_step = adjusted % model.vars_per_step;
    let proc = within_step / 3;
    let var_type = within_step % 3;

    let name = match var_type {
        0 => format!("has_token[P{}]", proc),
        1 => format!("in_cs[P{}]", proc),
        2 => format!("waiting[P{}]", proc),
        _ => format!("unknown[{}]", var),
    };

    (name, time)
}

/// Print execution trace from assignment.
fn print_trace(assignment: &[i32], model: &TokenRingModel) {
    for t in 0..=model.num_steps {
        print!("   t={}: ", t);
        for p in 0..model.num_processes {
            let tok_var = model.has_token(p, t);
            let cs_var = model.in_cs(p, t);
            let wait_var = model.waiting(p, t);

            let has_tok = assignment.get(tok_var as usize - 1).copied().unwrap_or(0) > 0;
            let in_critical = assignment.get(cs_var as usize - 1).copied().unwrap_or(0) > 0;
            let waiting = assignment.get(wait_var as usize - 1).copied().unwrap_or(0) > 0;

            let state = match (has_tok, in_critical, waiting) {
                (true, true, _) => "T+CS",
                (true, false, _) => "T",
                (false, true, _) => "CS!", // Bug: in CS without token
                (false, false, true) => "W",
                (false, false, false) => "-",
            };
            print!("P{}[{}] ", p, state);
        }
        println!();
    }
}

/// Analyze decomposition structure of the SDD.
fn analyze_decomposition(mgr: &SddManager, f: SddId, _depth: usize) {
    use ananke_sdd::Sdd;

    let node = mgr.node(f);

    match node {
        Sdd::Decision { elements, .. } => {
            // Only show summary, not all details
            println!("   {} prime-sub decompositions found", elements.len());
            println!("   (Each represents an independent region of variable space)");
        }
        _ => {
            // For terminal nodes, nothing to analyze
        }
    }
}

/// Demonstrate comparison with single counterexample.
fn compare_with_single_counterexample(mgr: &SddManager, counterexamples: SddId, _model: &TokenRingModel) {
    println!("\n╔══════════════════════════════════════════════════════════════════╗");
    println!("║     STRUCTURED COUNTEREXAMPLE ANALYSIS                           ║");
    println!("╚══════════════════════════════════════════════════════════════════╝\n");

    let count = mgr.model_count(counterexamples);

    // Factor analysis - key insight
    println!("📊 Independent Failure Factors:");
    let node = mgr.node(counterexamples);
    if let Sdd::Decision { elements, .. } = node {
        println!("   SDD reveals {} independent ways to violate mutex:\n", elements.len());

        let mut valid_factors = 0;
        for elem in elements.iter() {
            let prime_count = mgr.model_count(elem.prime);
            let sub_count = mgr.model_count(elem.sub);

            if sub_count > BigUint::from(0u32) {
                valid_factors += 1;
                println!("   Factor {}: {} × {} variable assignments", valid_factors, prime_count, sub_count);
            }
        }
    }

    println!("\n💡 What This Reveals:");
    println!("   Traditional model checker → 1 trace");
    println!("   SDD-based analysis → {} distinct counterexamples", count);
    println!("   Structured into factors → independent failure modes");
}

/// Demonstrate with an intentionally buggy protocol.
fn demonstrate_with_buggy_model() {
    // Simpler model where bugs can occur: processes can enter CS without proper token check

    let num_vars = 12; // 4 vars per process × 3 processes
    let mgr = SddManager::new(num_vars);

    // Simple encoding: in_cs[0], in_cs[1], in_cs[2] at two time points
    // Vars 1-3: in_cs at t=0
    // Vars 4-6: in_cs at t=1
    // Vars 7-9: has_token at t=0
    // Vars 10-12: has_token at t=1

    // Initial: nobody in CS
    let init = {
        let not_cs0 = mgr.neg(mgr.var(1));
        let not_cs1 = mgr.neg(mgr.var(2));
        let not_cs2 = mgr.neg(mgr.var(3));
        mgr.and(not_cs0, mgr.and(not_cs1, not_cs2))
    };

    // Buggy transition: any process CAN enter CS (no token check!)
    let buggy_trans = {
        // Process 0 can enter CS
        let p0_enters = mgr.var(4);
        // Process 1 can enter CS
        let p1_enters = mgr.var(5);
        // Process 2 can enter CS
        let p2_enters = mgr.var(6);
        // Any combination is allowed (bug!)
        mgr.and(
            mgr.or(p0_enters, mgr.neg(p0_enters)),
            mgr.and(mgr.or(p1_enters, mgr.neg(p1_enters)), mgr.or(p2_enters, mgr.neg(p2_enters))),
        )
    };

    let reachable = mgr.and(init, buggy_trans);

    // Bad: two or more processes in CS at t=1
    let bad = {
        let both_01 = mgr.and(mgr.var(4), mgr.var(5));
        let both_02 = mgr.and(mgr.var(4), mgr.var(6));
        let both_12 = mgr.and(mgr.var(5), mgr.var(6));
        mgr.or(both_01, mgr.or(both_02, both_12))
    };

    let counterexamples = mgr.and(reachable, bad);

    println!("Buggy Model Results:");
    println!("   SDD size: {} nodes", mgr.size(counterexamples));
    println!("   Counterexample count: {}\n", mgr.model_count(counterexamples));

    // Simplified analysis
    println!("🔍 Analysis of Buggy Protocol Counterexamples:");

    if let Some(sat) = mgr.any_sat(counterexamples) {
        println!("\n   Sample counterexample:");
        println!("   t=0: All processes NOT in CS (initial state)");
        print!("   t=1: ");

        let in_cs: Vec<_> = (4..=6)
            .filter(|&v| sat.get(v - 1).copied().unwrap_or(0) > 0)
            .map(|v| format!("P{}", v - 4))
            .collect();
        println!("{} in CS simultaneously!", in_cs.join(" and "));
    }

    // Show decomposition
    println!("\n   SDD Structure (prime decomposition):");
    let node = mgr.node(counterexamples);
    if let Sdd::Decision { elements, .. } = node {
        println!("   {} independent factors:", elements.len());
        for (i, _elem) in elements.iter().enumerate() {
            println!("   Factor {}: represents one way multiple processes enter CS", i + 1);
        }
    }

    println!("\n   Key Insight:");
    println!("   The SDD reveals that counterexamples decompose into");
    println!("   independent choices of WHICH pair of processes violate mutex.");
    println!("   This structural insight is not available from a single trace!");
}

fn main() {
    println!("═══════════════════════════════════════════════════════════════════");
    println!("     EXPLAINABLE COUNTEREXAMPLES VIA SDD");
    println!("     Bounded Model Checking with Structured Analysis");
    println!("═══════════════════════════════════════════════════════════════════\n");

    // Create a small token ring with 3 processes, 2 steps
    // (Intentionally buggy to produce counterexamples)
    let num_processes = 3;
    let num_steps = 2;
    let model = TokenRingModel::new(num_processes, num_steps);

    println!("📋 Model: Token Ring Protocol");
    println!("   • {} processes", num_processes);
    println!("   • {} time steps (bounded)", num_steps);
    println!("   • {} total Boolean variables\n", model.total_vars());

    let mgr = SddManager::new(model.total_vars());

    println!("Step 1: Encoding initial state...");
    let init = initial_state(&mgr, &model);
    println!("   Initial state SDD size: {} nodes\n", mgr.size(init));

    println!("Step 2: Encoding transition relations...");
    let mut reachable = init;
    for t in 0..num_steps {
        let trans = transition(&mgr, &model, t);
        println!("   Transition t={} SDD size: {} nodes", t, mgr.size(trans));
        reachable = mgr.and(reachable, trans);
    }
    println!("   Reachable states SDD size: {} nodes\n", mgr.size(reachable));

    println!("Step 3: Encoding bad states (mutual exclusion violation)...");
    let mut any_bad = mgr.false_sdd();
    for t in 0..=num_steps {
        let bad_at_t = bad_state(&mgr, &model, t);
        println!("   Bad states at t={} SDD size: {} nodes", t, mgr.size(bad_at_t));
        any_bad = mgr.or(any_bad, bad_at_t);
    }
    println!("   Bad states SDD size: {} nodes\n", mgr.size(any_bad));

    println!("Step 4: Computing counterexamples (reachable ∧ bad)...");
    let counterexamples = mgr.and(reachable, any_bad);
    let ce_size = mgr.size(counterexamples);
    let ce_count = mgr.model_count(counterexamples);

    if mgr.is_false(counterexamples) {
        println!("   ✓ No counterexamples found - property holds!");
        println!("   The protocol correctly maintains mutual exclusion.\n");

        // For demonstration, let's inject a bug
        println!("═══════════════════════════════════════════════════════════════════");
        println!("   Injecting a BUG for demonstration purposes...");
        println!("═══════════════════════════════════════════════════════════════════\n");

        demonstrate_with_buggy_model();
    } else {
        println!("   ✗ Found counterexamples!");
        println!("   SDD size: {} nodes", ce_size);
        println!("   Number of distinct counterexamples: {}\n", ce_count);

        analyze_counterexamples(&mgr, counterexamples, &model);
        compare_with_single_counterexample(&mgr, counterexamples, &model);
    }
}
