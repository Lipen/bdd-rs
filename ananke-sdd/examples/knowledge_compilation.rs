//! Knowledge Compilation Example.
//!
//! Demonstrates using SDDs for knowledge compilation: compiling a propositional
//! knowledge base into a tractable form for efficient query answering.
//!
//! Scenario: Laptop Configuration
//! - Components have constraints (e.g., GPU requires large battery)
//! - Compile constraints once, answer queries efficiently
//!
//! Run with: `cargo run --example knowledge_compilation`

use ananke_sdd::SddManager;

fn main() {
    println!("─── Knowledge Compilation with SDDs ───\n");
    println!("Scenario: Laptop Configurator\n");

    // ────────────────────────────────────────────────────────────────────────
    // PROBLEM DESCRIPTION
    // ────────────────────────────────────────────────────────────────────────

    println!("── Problem Setup ──\n");

    println!("Variables (components):");
    println!("  x₁ = High-end GPU");
    println!("  x₂ = Large battery");
    println!("  x₃ = Slim design");
    println!("  x₄ = Powerful CPU");
    println!("  x₅ = 4K display");
    println!("  x₆ = Extended warranty");
    println!();

    println!("Constraints (business rules):");
    println!("  C1: GPU → Battery      (GPU needs power)");
    println!("  C2: Slim → ¬Battery    (slim excludes big battery)");
    println!("  C3: 4K → CPU           (4K needs processing)");
    println!("  C4: GPU ∨ CPU          (at least one performance component)");
    println!("  C5: Warranty → GPU∨4K  (warranty for premium items)");
    println!();

    // ────────────────────────────────────────────────────────────────────────
    // CREATE SDD MANAGER AND VARIABLES
    // ────────────────────────────────────────────────────────────────────────

    let mgr = SddManager::new(6);

    let gpu = mgr.var(1);
    let battery = mgr.var(2);
    let slim = mgr.var(3);
    let cpu = mgr.var(4);
    let display_4k = mgr.var(5);
    let warranty = mgr.var(6);

    // ────────────────────────────────────────────────────────────────────────
    // COMPILE KNOWLEDGE BASE
    // ────────────────────────────────────────────────────────────────────────

    println!("── 1. Compiling Knowledge Base ──\n");

    let c1 = mgr.implies(gpu, battery); // GPU → Battery
    let c2 = mgr.implies(slim, mgr.neg(battery)); // Slim → ¬Battery
    let c3 = mgr.implies(display_4k, cpu); // 4K → CPU
    let c4 = mgr.or(gpu, cpu); // GPU ∨ CPU
    let c5 = mgr.implies(warranty, mgr.or(gpu, display_4k)); // Warranty → GPU∨4K

    let kb = mgr.and_all([c1, c2, c3, c4, c5]);

    println!("Knowledge base compiled!");
    println!("  SDD size:            {} nodes", mgr.size(kb));
    println!("  Valid configurations: {}", mgr.model_count(kb));
    println!();

    // ────────────────────────────────────────────────────────────────────────
    // CONSISTENCY CHECK
    // ────────────────────────────────────────────────────────────────────────

    println!("── 2. Consistency Check ──\n");

    println!("Q: Is the knowledge base consistent?");
    let consistent = mgr.is_satisfiable(kb);
    println!("A: {} — valid configurations exist\n", yn(consistent));

    // ────────────────────────────────────────────────────────────────────────
    // ENTAILMENT QUERIES
    // ────────────────────────────────────────────────────────────────────────

    println!("── 3. Entailment Queries ──\n");

    println!("Entailment: KB ⊨ φ iff KB ∧ ¬φ is unsatisfiable\n");

    // Does KB entail (GPU → Battery)?
    let query1 = mgr.implies(gpu, battery);
    let entails1 = !mgr.is_satisfiable(mgr.and(kb, mgr.neg(query1)));
    println!("  KB ⊨ (GPU → Battery)?     {}", yn(entails1));

    // Does KB entail (Slim → ¬GPU)?
    let query2 = mgr.implies(slim, mgr.neg(gpu));
    let entails2 = !mgr.is_satisfiable(mgr.and(kb, mgr.neg(query2)));
    println!("  KB ⊨ (Slim → ¬GPU)?       {}", yn(entails2));

    // Does KB entail GPU?
    let entails_gpu = !mgr.is_satisfiable(mgr.and(kb, mgr.neg(gpu)));
    println!("  KB ⊨ GPU?                 {}", yn(entails_gpu));

    // Does KB entail (GPU ∨ CPU)?
    let entails_perf = !mgr.is_satisfiable(mgr.and(kb, mgr.neg(mgr.or(gpu, cpu))));
    println!("  KB ⊨ (GPU ∨ CPU)?         {}", yn(entails_perf));

    println!();
    println!("Note: Slim → ¬GPU follows from C1 (GPU→Battery) and C2 (Slim→¬Battery).");
    println!();

    // ────────────────────────────────────────────────────────────────────────
    // EQUIVALENCE CHECKING
    // ────────────────────────────────────────────────────────────────────────

    println!("── 4. Equivalence Checking ──\n");

    println!("Check if two formulas are equivalent under the knowledge base.\n");

    // Under KB, is (Slim) equivalent to (Slim ∧ CPU)?
    // Since Slim → ¬GPU → CPU (from C4: GPU ∨ CPU)
    let slim_alone = mgr.and(kb, slim);
    let slim_cpu = mgr.and(kb, mgr.and(slim, cpu));

    // Two ways to check equivalence:
    // 1. Model counts match AND (a ∧ ¬b) ∨ (¬a ∧ b) is unsat under KB
    let xor_check = mgr.xor(slim, mgr.and(slim, cpu));
    let equiv1 = !mgr.is_satisfiable(mgr.and(kb, xor_check));

    println!("  Under KB: Slim ≡ (Slim ∧ CPU)?");
    println!("    Via XOR test: {}", yn(equiv1));
    println!("    Model counts: {} vs {}", mgr.model_count(slim_alone), mgr.model_count(slim_cpu));
    println!();
    println!("  Explanation: Slim forces ¬GPU (via Battery), so C4 forces CPU.");
    println!();

    // ────────────────────────────────────────────────────────────────────────
    // CONFLICT DETECTION
    // ────────────────────────────────────────────────────────────────────────

    println!("── 5. Conflict Detection ──\n");

    println!("Identify impossible combinations:\n");

    let conflicts = [
        ("GPU ∧ Slim", mgr.and(gpu, slim)),
        ("4K ∧ ¬CPU", mgr.and(display_4k, mgr.neg(cpu))),
        ("Warranty ∧ ¬GPU ∧ ¬4K", mgr.and_all([warranty, mgr.neg(gpu), mgr.neg(display_4k)])),
        ("GPU ∧ ¬Battery", mgr.and(gpu, mgr.neg(battery))),
    ];

    println!("  Combination              Possible?  Why");
    println!("  ───────────────────────  ─────────  ────────────────────────");

    for (name, formula) in conflicts {
        let possible = mgr.is_satisfiable(mgr.and(kb, formula));
        let reason = if possible { "" } else { get_conflict_reason(name) };
        println!("  {:23}  {:9}  {}", name, yn(possible), reason);
    }
    println!();

    // ────────────────────────────────────────────────────────────────────────
    // INCREMENTAL COMPILATION
    // ────────────────────────────────────────────────────────────────────────

    println!("── 6. Incremental Compilation ──\n");

    println!("Add new constraints incrementally:\n");

    // Original KB size
    println!("  Original KB: {} nodes, {} configs", mgr.size(kb), mgr.model_count(kb));

    // Add: Premium = GPU ∧ 4K
    let premium = mgr.and(gpu, display_4k);
    let c6 = mgr.implies(warranty, premium); // Stronger warranty requirement
    let kb2 = mgr.and(kb, c6);

    println!(
        "  + Warranty → (GPU ∧ 4K): {} nodes, {} configs",
        mgr.size(kb2),
        mgr.model_count(kb2)
    );

    // Add: Budget option excludes premium
    let budget = mgr.neg(mgr.or(gpu, display_4k));
    let c7 = mgr.implies(budget, mgr.neg(warranty));
    let kb3 = mgr.and(kb2, c7);

    println!(
        "  + Budget → ¬Warranty:    {} nodes, {} configs",
        mgr.size(kb3),
        mgr.model_count(kb3)
    );

    println!();
    println!("  Key insight: SDD operations compose efficiently.");
    println!();

    // ────────────────────────────────────────────────────────────────────────
    // CONFIGURATION ENUMERATION
    // ────────────────────────────────────────────────────────────────────────

    println!("── 7. Configuration Enumeration ──\n");

    let names = ["GPU", "Battery", "Slim", "CPU", "4K", "Warranty"];

    // Find slim configurations
    let slim_configs = mgr.and(kb, slim);
    let count = mgr.model_count(slim_configs);

    println!("Slim configurations ({} total):\n", count);

    // Enumerate by conditioning
    enumerate_configs(&mgr, slim_configs, &names, 3);

    // ────────────────────────────────────────────────────────────────────────
    // ABSTRACTION (FORGETTING)
    // ────────────────────────────────────────────────────────────────────────

    println!("── 8. Variable Abstraction ──\n");

    println!("Forget internal details, keep only customer-facing options.\n");
    println!("Keep: GPU (1), CPU (4), 4K (5), Warranty (6)");
    println!("Forget: Battery (2), Slim (3)\n");

    let mut abstracted = kb;
    for var in [2, 3] {
        // Forget Battery and Slim
        abstracted = mgr.exists(abstracted, var);
    }

    println!("  Original:   {} configs", mgr.model_count(kb));
    println!("  Abstracted: {} configs (over 4 vars)", mgr.model_count(abstracted));
    println!();

    println!("  Valid (GPU, CPU, 4K, Warranty) combinations:\n");

    println!("  GPU CPU 4K  War  Valid");
    println!("  ─── ─── ──  ───  ─────");

    // Test all combinations of remaining 4 variables
    for w in 0..=1 {
        for d in 0..=1 {
            for c in 0..=1 {
                for g in 0..=1 {
                    let test = mgr.and_all([
                        if g == 1 { gpu } else { mgr.neg(gpu) },
                        if c == 1 { cpu } else { mgr.neg(cpu) },
                        if d == 1 { display_4k } else { mgr.neg(display_4k) },
                        if w == 1 { warranty } else { mgr.neg(warranty) },
                    ]);
                    let valid = mgr.is_satisfiable(mgr.and(abstracted, test));
                    if valid {
                        println!("   {}   {}   {}    {}   ✓", g, c, d, w);
                    }
                }
            }
        }
    }
    println!();

    // ────────────────────────────────────────────────────────────────────────
    // STATISTICS
    // ────────────────────────────────────────────────────────────────────────

    println!("── Compilation Statistics ──\n");

    let stats = mgr.stats();
    let hit_rate = if stats.apply_calls > 0 {
        100.0 * stats.cache_hits as f64 / stats.apply_calls as f64
    } else {
        0.0
    };

    println!("Metric              Value");
    println!("──────────────────  ──────────");
    println!("Variables           {:>10}", stats.num_vars);
    println!("Total nodes         {:>10}", stats.num_nodes);
    println!("Apply calls         {:>10}", stats.apply_calls);
    println!("Cache hit rate      {:>9.1}%", hit_rate);
    println!();
    println!("Key benefit: Once compiled, all queries are O(|SDD|)!");
    println!();

    println!("Done.");
}

/// Enumerate configurations by conditioning.
fn enumerate_configs(mgr: &SddManager, formula: ananke_sdd::SddId, names: &[&str], max: usize) {
    let mut count = 0;
    let mut current = formula;

    while mgr.is_satisfiable(current) && count < max {
        if let Some(assignment) = mgr.any_sat(current) {
            count += 1;
            print!("  {}: ", count);
            for (i, &lit) in assignment.iter().enumerate() {
                if i < names.len() {
                    if lit > 0 {
                        print!("{} ", names[i]);
                    }
                }
            }
            println!();

            // Block this assignment
            let blocking = mgr.neg(mgr.cube(assignment));
            current = mgr.and(current, blocking);
        } else {
            break;
        }
    }

    let remaining = mgr.model_count(current);
    if remaining > num_bigint::BigUint::from(0u32) {
        println!("  ... and {} more\n", remaining);
    } else {
        println!();
    }
}

/// Get explanation for conflict.
fn get_conflict_reason(name: &str) -> &'static str {
    match name {
        "GPU ∧ Slim" => "C1: GPU→Battery, C2: Slim→¬Battery",
        "4K ∧ ¬CPU" => "C3: 4K→CPU",
        "Warranty ∧ ¬GPU ∧ ¬4K" => "C5: Warranty→GPU∨4K",
        "GPU ∧ ¬Battery" => "C1: GPU→Battery",
        _ => "",
    }
}

/// Helper: yes/no with checkmark.
fn yn(v: bool) -> &'static str {
    if v {
        "✓ yes"
    } else {
        "✗ no"
    }
}
