//! Digital Circuit Analysis with SDDs
//!
//! SDDs can represent Boolean functions computed by digital circuits.
//! This enables:
//!   - Functional verification (equivalence checking)
//!   - Fault detection and test generation
//!   - Output probability under random inputs
//!   - Path sensitization analysis
//!
//! This example demonstrates building circuit representations and
//! performing various analyses using SDD operations.

use ananke_sdd::{SddId, SddManager};

fn main() {
    println!("─── Digital Circuit Analysis with SDDs ───\n");

    basic_gates();
    combinational_circuit();
    equivalence_checking();
    fault_detection();
    circuit_probability();
}

/// Demonstrate basic gate representations
fn basic_gates() {
    println!("── Basic Gates ──\n");

    let mgr = SddManager::new(2);
    let a = mgr.var(1);
    let b = mgr.var(2);

    // NOT gate
    let not_a = mgr.neg(a);

    // AND gate
    let and_ab = mgr.and(a, b);

    // OR gate
    let or_ab = mgr.or(a, b);

    // NAND gate
    let nand_ab = mgr.neg(and_ab);

    // NOR gate
    let nor_ab = mgr.neg(or_ab);

    // XOR gate: (A ∧ ¬B) ∨ (¬A ∧ B)
    let not_b = mgr.neg(b);
    let xor_ab = mgr.xor(a, b);

    // XNOR gate
    let xnor_ab = mgr.neg(xor_ab);

    println!("Gate Truth Tables (A=1, B=2):\n");
    println!("A  B │ NOT A  AND  OR   NAND  NOR  XOR  XNOR");
    println!("─────┼────────────────────────────────────────");

    for a_val in [false, true] {
        for b_val in [false, true] {
            // Condition on inputs
            let cond_a = if a_val { a } else { not_a };
            let cond_b = if b_val { b } else { not_b };
            let input = mgr.and(cond_a, cond_b);

            // Evaluate each gate under this input
            let eval = |gate: SddId| {
                let result = mgr.and(gate, input);
                if mgr.is_false(result) {
                    '0'
                } else {
                    '1'
                }
            };

            println!(
                "{}  {} │   {}      {}    {}     {}     {}    {}     {}",
                if a_val { '1' } else { '0' },
                if b_val { '1' } else { '0' },
                eval(not_a),
                eval(and_ab),
                eval(or_ab),
                eval(nand_ab),
                eval(nor_ab),
                eval(xor_ab),
                eval(xnor_ab)
            );
        }
    }

    println!("\nSDD sizes for 2-input gates:");
    println!("  NOT:   {} nodes", mgr.size(not_a));
    println!("  AND:   {} nodes", mgr.size(and_ab));
    println!("  OR:    {} nodes", mgr.size(or_ab));
    println!("  XOR:   {} nodes", mgr.size(xor_ab));
    println!();
}

/// Build and analyze a combinational circuit (4-bit adder)
fn combinational_circuit() {
    println!("── Combinational Circuit: 4-bit Ripple Carry Adder ──\n");

    // 4-bit adder: A[0..3], B[0..3], Cin -> S[0..3], Cout
    // Variables: A0=1, A1=2, A2=3, A3=4, B0=5, B1=6, B2=7, B3=8, Cin=9
    let n_vars = 9;
    let mgr = SddManager::new(n_vars);

    // Full adder circuit diagram
    println!("Full Adder (FA) building block:");
    println!();
    println!("  Si = Ai ⊕ Bi ⊕ Cin");
    println!("  Cout = (Ai ∧ Bi) ∨ (Cin ∧ (Ai ⊕ Bi))");
    println!();

    println!("4-bit Ripple Carry Adder:");
    println!();
    println!("         A0 B0       A1 B1       A2 B2       A3 B3        ");
    println!("         │  │        │  │        │  │        │  │         ");
    println!("        ┌┴──┴┐  C0  ┌┴──┴┐  C1  ┌┴──┴┐  C2  ┌┴──┴┐        ");
    println!("  Cin ──┤ FA ├──────┤ FA ├──────┤ FA ├──────┤ FA ├── Cout ");
    println!("        └─┬──┘      └─┬──┘      └─┬──┘      └─┬──┘        ");
    println!("          │           │           │           │           ");
    println!("          S0          S1          S2          S3          ");
    println!();
    println!("  (Si,Ci) = FA(Ai,Bi,C[i-1]) for i=0..3");
    println!("  C[-1] = Cin");
    println!("  Cout = C3");
    println!();

    // Get input variables
    let a: Vec<_> = (1..=4).map(|v| mgr.var(v)).collect();
    let b: Vec<_> = (5..=8).map(|v| mgr.var(v)).collect();
    let cin = mgr.var(9);

    // Build full adders for each bit position
    // Full adder: S = A ⊕ B ⊕ Cin, Cout = (A ∧ B) ∨ (Cin ∧ (A ⊕ B))
    let mut carry = cin;
    let mut sum_bits = Vec::new();

    for i in 0..4 {
        // XOR for sum
        let a_xor_b = mgr.xor(a[i], b[i]);
        let sum = mgr.xor(a_xor_b, carry);
        sum_bits.push(sum);

        // Carry out: (A ∧ B) ∨ (Cin ∧ (A ⊕ B))
        let a_and_b = mgr.and(a[i], b[i]);
        let cin_and_axorb = mgr.and(carry, a_xor_b);
        carry = mgr.or(a_and_b, cin_and_axorb);
    }
    let cout = carry;

    println!("Inputs:");
    println!("  A = A3 A2 A1 A0  (vars 4, 3, 2, 1)");
    println!("  B = B3 B2 B1 B0  (vars 8, 7, 6, 5)");
    println!("  Cin             (var 9)");
    println!();

    println!("Outputs:");
    println!("  S = S3 S2 S1 S0  (sum bits)");
    println!("  Cout             (carry out)");
    println!();

    println!("SDD sizes for outputs:");
    for (i, s) in sum_bits.iter().enumerate() {
        println!("    S{}: {:3} nodes", i, mgr.size(*s));
    }
    println!("  Cout: {:3} nodes", mgr.size(cout));
    println!();

    // Verify adder correctness by testing a few cases
    println!("Verification (sampling a few inputs):\n");
    println!("  A    B    Cin │ Result   Expected");
    println!("────────────────┼────────────────────");

    let test_cases = [
        (0b0000u8, 0b0000u8, false, 0b00000u8), // 0 + 0 + 0 = 0
        (0b0001, 0b0001, false, 0b00010),       // 1 + 1 = 2
        (0b0111, 0b0001, false, 0b01000),       // 7 + 1 = 8
        (0b1111, 0b0001, false, 0b10000),       // 15 + 1 = 16 (overflow)
        (0b1010, 0b0101, false, 0b01111),       // 10 + 5 = 15
        (0b1111, 0b1111, false, 0b11110),       // 15 + 15 = 30
        (0b1111, 0b1111, true, 0b11111),        // 15 + 15 + 1 = 31
    ];

    for (a_val, b_val, cin_val, expected) in test_cases {
        // Build input constraint
        let mut input = mgr.true_sdd();
        for i in 0..4 {
            let bit_set = (a_val >> i) & 1 == 1;
            let a_cond = if bit_set { a[i] } else { mgr.neg(a[i]) };
            input = mgr.and(input, a_cond);

            let bit_set = (b_val >> i) & 1 == 1;
            let b_cond = if bit_set { b[i] } else { mgr.neg(b[i]) };
            input = mgr.and(input, b_cond);
        }
        let cin_cond = if cin_val { cin } else { mgr.neg(cin) };
        input = mgr.and(input, cin_cond);

        // Evaluate outputs
        let mut result = 0u8;
        for (i, s) in sum_bits.iter().enumerate() {
            let out = mgr.and(*s, input);
            if !mgr.is_false(out) {
                result |= 1 << i;
            }
        }
        let cout_out = mgr.and(cout, input);
        if !mgr.is_false(cout_out) {
            result |= 1 << 4;
        }

        let a_str = format!("{:04b}", a_val);
        let b_str = format!("{:04b}", b_val);
        let cin_str = if cin_val { "1" } else { "0" };
        let check = if result == expected { "✓" } else { "✗" };

        println!("  {} {} {}   │ {:05b}    {:05b} {}", a_str, b_str, cin_str, result, expected, check);
    }

    println!("\nTotal manager statistics:");
    let stats = mgr.stats();
    println!("  Total nodes: {}", stats.num_nodes);
    println!("  Apply operations: {}", stats.apply_calls);
    println!();
}

/// Equivalence checking between two circuit implementations
fn equivalence_checking() {
    println!("── Equivalence Checking ──\n");

    // Two implementations of XOR:
    // 1. Standard: (A ∧ ¬B) ∨ (¬A ∧ B)
    // 2. NAND-based: NAND(NAND(A, NAND(A,B)), NAND(B, NAND(A,B)))

    let mgr = SddManager::new(2);
    let a = mgr.var(1);
    let b = mgr.var(2);

    println!("Comparing two XOR implementations:\n");
    println!("  Impl 1: (A ∧ ¬B) ∨ (¬A ∧ B)");
    println!("  Impl 2: NAND(NAND(A, NAND(A,B)), NAND(B, NAND(A,B)))\n");

    // Implementation 1: Standard XOR
    let not_a = mgr.neg(a);
    let not_b = mgr.neg(b);
    let a_and_not_b = mgr.and(a, not_b);
    let not_a_and_b = mgr.and(not_a, b);
    let xor1 = mgr.or(a_and_not_b, not_a_and_b);

    // Implementation 2: NAND-based XOR
    let nand = |mgr: &SddManager, x: SddId, y: SddId| mgr.neg(mgr.and(x, y));
    let nand_ab = nand(&mgr, a, b);
    let nand_a_nandab = nand(&mgr, a, nand_ab);
    let nand_b_nandab = nand(&mgr, b, nand_ab);
    let xor2 = nand(&mgr, nand_a_nandab, nand_b_nandab);

    // Check equivalence: XOR of implementations should be False
    let diff = mgr.xor(xor1, xor2);
    let equivalent = mgr.is_false(diff);

    println!("Equivalence check: XOR(Impl1, Impl2)");
    if equivalent {
        println!("  Result: ⊥ (False)");
        println!("  The implementations are EQUIVALENT ✓");
    } else {
        println!("  Result: non-False");
        println!("  The implementations are NOT equivalent ✗");
    }

    println!("\nSDD sizes:");
    println!("  Impl 1 (standard): {} nodes", mgr.size(xor1));
    println!("  Impl 2 (NAND):     {} nodes", mgr.size(xor2));
    println!();

    // Also check miter approach
    println!("Alternative: Miter circuit approach");
    println!("  Miter = (Out1 ⊕ Out2) should be unsatisfiable");
    let model_count = mgr.model_count(diff);
    println!("  Model count of miter: {}", model_count);
    if model_count.to_string() == "0" {
        println!("  Unsatisfiable -> circuits are equivalent ✓");
    }
    println!();
}

/// Fault detection and test generation
fn fault_detection() {
    println!("── Fault Detection ──\n");

    // Simple circuit: C = (A ∧ B) ∨ (¬A ∧ D)
    // We'll analyze stuck-at faults

    let n_vars = 4;
    let mgr = SddManager::new(n_vars);

    let a = mgr.var(1);
    let b = mgr.var(2);
    // Variable 3 unused in circuit
    let d = mgr.var(4);

    println!("Circuit: Out = (A ∧ B) ∨ (¬A ∧ D)\n");
    println!("        ┌─────┐                             ");
    println!("  A ────┤ AND ├────────────┐                ");
    println!("  B ────┤     │            │  ┌────┐        ");
    println!("        └─────┘            └──┤    │        ");
    println!("                              │ OR ├─── Out ");
    println!("        ┌─────┐   ┌─────┐  ┌──┤    │        ");
    println!("  A ────┤ NOT ├───┤ AND ├──┘  └────┘        ");
    println!("        └─────┘   │     │                   ");
    println!("  D ──────────────┤     │                   ");
    println!("                  └─────┘                   ");
    println!();

    // Fault-free circuit
    let not_a = mgr.neg(a);
    let a_and_b = mgr.and(a, b);
    let not_a_and_d = mgr.and(not_a, d);
    let out_good = mgr.or(a_and_b, not_a_and_d);

    // Stuck-at-0 fault on wire A (input to first AND gate)
    // A is replaced with constant 0
    let false_const = mgr.false_sdd();
    let a_and_b_fault = mgr.and(false_const, b); // becomes 0
    let out_sa0_a = mgr.or(a_and_b_fault, not_a_and_d);

    // Stuck-at-1 fault on wire A
    let true_const = mgr.true_sdd();
    let a_and_b_sa1 = mgr.and(true_const, b); // becomes B
    let not_a_sa1 = mgr.neg(true_const); // becomes 0
    let not_a_and_d_sa1 = mgr.and(not_a_sa1, d); // becomes 0
    let out_sa1_a = mgr.or(a_and_b_sa1, not_a_and_d_sa1);

    println!("Fault analysis for wire A:");
    println!();

    // Find detecting tests (inputs where faulty output differs from good)
    let detect_sa0 = mgr.xor(out_good, out_sa0_a);
    let detect_sa1 = mgr.xor(out_good, out_sa1_a);

    let sa0_tests = mgr.model_count(detect_sa0);
    let sa1_tests = mgr.model_count(detect_sa1);

    println!("  Stuck-at-0 on A:");
    println!("    Detecting inputs: {} (of {} total)", sa0_tests, 1 << n_vars);
    if sa0_tests.to_string() != "0" {
        println!("    Fault is detectable ✓");
    }

    println!();
    println!("  Stuck-at-1 on A:");
    println!("    Detecting inputs: {} (of {} total)", sa1_tests, 1 << n_vars);
    if sa1_tests.to_string() != "0" {
        println!("    Fault is detectable ✓");
    }

    // Show some detecting test vectors
    println!();
    println!("Sample test vectors for stuck-at-0 on A:");
    println!("  A B C D │ Good  Faulty  Detects?");
    println!("──────────┼─────────────────────────");

    let not_b = mgr.neg(b);
    let not_d = mgr.neg(d);

    for a_val in [false, true] {
        for b_val in [false, true] {
            for d_val in [false, true] {
                // Condition on inputs (C doesn't affect circuit)
                let cond_a = if a_val { a } else { not_a };
                let cond_b = if b_val { b } else { not_b };
                let cond_d = if d_val { d } else { not_d };
                let input = mgr.and(cond_a, mgr.and(cond_b, cond_d));

                let good = !mgr.is_false(mgr.and(out_good, input));
                let faulty = !mgr.is_false(mgr.and(out_sa0_a, input));
                let detects = good != faulty;

                println!(
                    "  {} {} - {} │   {}      {}       {}",
                    if a_val { '1' } else { '0' },
                    if b_val { '1' } else { '0' },
                    if d_val { '1' } else { '0' },
                    if good { '1' } else { '0' },
                    if faulty { '1' } else { '0' },
                    if detects { "Yes" } else { "No" }
                );
            }
        }
    }
    println!();
}

/// Compute output probability under random inputs
fn circuit_probability() {
    println!("── Circuit Output Probability ──\n");

    // For random inputs, what's the probability the output is 1?
    // Using weighted model counting with uniform weights.

    let n_vars = 4usize;
    let mgr = SddManager::new(n_vars as u32);

    let a = mgr.var(1);
    let b = mgr.var(2);
    let c = mgr.var(3);
    let d = mgr.var(4);

    println!("Circuit: Out = (A ∧ B) ∨ (C ∧ D)\n");

    let a_and_b = mgr.and(a, b);
    let c_and_d = mgr.and(c, d);
    let out = mgr.or(a_and_b, c_and_d);

    // Model count approach: P(out=1) = |{inputs: out=1}| / 2^n
    let sat_count = mgr.model_count(out);
    let total = 1u64 << n_vars;
    // Convert BigUint to f64
    let sat_count_f64: f64 = sat_count.to_string().parse().unwrap_or(0.0);
    let prob_counting = sat_count_f64 / total as f64;

    println!("Using model counting:");
    println!("  Satisfying assignments: {}", sat_count);
    println!("  Total assignments:      {}", total);
    println!("  P(Out=1) = {}/{} = {:.4}", sat_count, total, prob_counting);
    println!();

    // WMC approach with uniform weights (P(x=1) = P(x=0) = 0.5)
    // Weight for positive literal = 0.5, negative = 0.5
    let pos_weights = vec![0.5; n_vars + 1]; // index 0 unused
    let neg_weights = vec![0.5; n_vars + 1];
    let prob_wmc = mgr.wmc(out, &pos_weights, &neg_weights);

    println!("Using WMC with uniform weights:");
    println!("  P(x=1) = P(x=0) = 0.5 for all x");
    println!("  P(Out=1) = {:.4}", prob_wmc);
    println!();

    // Non-uniform case: A has 80% probability of being 1
    println!("Non-uniform inputs: P(A=1)=0.8, others=0.5");
    let mut pos_biased = vec![0.5; n_vars + 1];
    let mut neg_biased = vec![0.5; n_vars + 1];
    pos_biased[1] = 0.8; // P(A=1) = 0.8
    neg_biased[1] = 0.2; // P(A=0) = 0.2

    let prob_biased = mgr.wmc(out, &pos_biased, &neg_biased);
    println!("  P(Out=1) = {:.4}", prob_biased);
    println!();

    // Analytical verification
    // (A ∧ B) ∨ (C ∧ D) = 1 - (1 - P(A)P(B))(1 - P(C)P(D))
    // For uniform: 1 - (1 - 0.25)(1 - 0.25) = 1 - 0.5625 = 0.4375
    // For biased:  1 - (1 - 0.8*0.5)(1 - 0.5*0.5) = 1 - (0.6)(0.75) = 0.55
    println!("Analytical verification:");
    let p_ab = 0.5 * 0.5;
    let p_cd = 0.5 * 0.5;
    let analytical_uniform = 1.0 - (1.0 - p_ab) * (1.0 - p_cd);
    println!("  Uniform: 1 - (1-0.25)(1-0.25) = {:.4}", analytical_uniform);

    let p_ab_biased = 0.8 * 0.5;
    let p_cd_biased = 0.5 * 0.5;
    let analytical_biased = 1.0 - (1.0 - p_ab_biased) * (1.0 - p_cd_biased);
    println!("  Biased:  1 - (1-0.40)(1-0.25) = {:.4}", analytical_biased);
    println!();

    let stats = mgr.stats();
    println!("Manager statistics:");
    println!("  Total nodes: {}", stats.num_nodes);
    println!("  Apply operations: {}", stats.apply_calls);
    println!();

    println!("─── Summary ───\n");
    println!("SDDs enable efficient circuit analysis:");
    println!("  • Represent arbitrary combinational logic");
    println!("  • Equivalence checking via miter circuits");
    println!("  • Fault detection and test generation");
    println!("  • Output probability via WMC");
    println!();
    println!("Done.");
}
