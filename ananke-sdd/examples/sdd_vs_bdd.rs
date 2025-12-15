//! SDD vs BDD Comparison.
//!
//! Compares SDDs and BDDs on various Boolean functions, demonstrating
//! their relationship and when each representation might be preferred.
//!
//! Key insights:
//! - SDDs generalize BDDs (every BDD is an SDD with right-linear vtree)
//! - SDDs can be exponentially more succinct for some functions
//! - Both support polytime conjunction, disjunction, and negation
//!
//! Run with: `cargo run --example sdd_vs_bdd`
//! With options: `cargo run --example sdd_vs_bdd -- -n 8`

use clap::Parser;
use ananke_sdd::SddManager;

#[derive(Parser, Debug)]
#[command(name = "sdd_vs_bdd")]
#[command(about = "Compare SDD and BDD representations")]
struct Args {
    /// Number of variables
    #[arg(short, long, default_value_t = 6)]
    n: u32,

    /// Verbose output
    #[arg(short, long)]
    verbose: bool,
}

fn main() {
    let args = Args::parse();
    let n = args.n;

    println!("─── SDDs vs BDDs: A Comparative Study ───\n");

    // ────────────────────────────────────────────────────────────────────────
    // BACKGROUND
    // ────────────────────────────────────────────────────────────────────────

    println!("── Background ──\n");

    println!("Both SDDs and BDDs are canonical Boolean function representations");
    println!("supporting tractable (polynomial-time) operations.\n");

    println!("Key differences:\n");

    println!("  Feature        BDD                    SDD");
    println!("  ─────────────  ─────────────────────  ─────────────────────────");
    println!("  Decomposition  Shannon (one var)      (X, A)-decomposition");
    println!("  Structure      Linear var ordering    Tree (vtree)");
    println!("  Node type      ITE (if-then-else)     (prime, sub) pairs");
    println!("  Canonicity     Per variable order     Per vtree");
    println!("  Negation       O(1) complement edge   O(1) or O(n) (no comp.)");
    println!();

    println!("Tractable operations (polynomial time):");
    println!("  • Conjunction (∧)");
    println!("  • Disjunction (∨)");
    println!("  • Negation (¬)");
    println!("  • Model counting (#SAT)");
    println!("  • Conditioning");
    println!("  • Existential quantification");
    println!();

    println!("Variables: n = {}\n", n);

    // ────────────────────────────────────────────────────────────────────────
    // CASE 1: XOR CHAIN
    // ────────────────────────────────────────────────────────────────────────

    println!("── Case 1: XOR Chain ──\n");

    println!("Formula: x₁ ⊕ x₂ ⊕ ... ⊕ x{}", n);
    println!();

    let mgr = SddManager::new(n);
    let mut xor_chain = mgr.var(1);
    for i in 2..=n {
        xor_chain = mgr.xor(xor_chain, mgr.var(i));
    }

    println!("  SDD size:    {} nodes", mgr.size(xor_chain));
    println!("  Model count: {} (2^{}/2)", mgr.model_count(xor_chain), n);
    println!();
    println!("Analysis:");
    println!("  • Both BDD and SDD: O(n) nodes");
    println!("  • XOR is symmetric — structure doesn't matter much");
    println!();

    // ────────────────────────────────────────────────────────────────────────
    // CASE 2: INTERLEAVED EQUALITY
    // ────────────────────────────────────────────────────────────────────────

    if n >= 4 {
        println!("── Case 2: Interleaved Equality ──\n");

        let half = n / 2;
        println!("Formula: (x1 ↔ x{}) ∧ (x2 ↔ x{}) ∧ ...", half + 1, half + 2);
        println!("  (pairs: x_i with x_{{n/2+i}})\n");

        // Compare vtree types
        println!("  Vtree Type     Size   Model Count");
        println!("  ────────────   ─────  ───────────");

        for (name, mgr) in [
            ("Balanced    ", SddManager::new(n)),
            ("Right-linear", SddManager::with_right_linear_vtree(n)),
            ("Left-linear ", SddManager::with_left_linear_vtree(n)),
        ] {
            let mut eq = mgr.true_sdd();
            for i in 1..=half {
                let equiv = mgr.equiv(mgr.var(i), mgr.var(half + i));
                eq = mgr.and(eq, equiv);
            }
            println!("  {}   {:>5}  {}", name, mgr.size(eq), mgr.model_count(eq));
        }
        println!();
        println!("Analysis:");
        println!("  • Variables that interact should be near in vtree/ordering");
        println!("  • BDD with bad ordering: O(2^(n/2)) nodes");
        println!("  • SDD with good vtree: O(n) nodes");
        println!();
    }

    // ────────────────────────────────────────────────────────────────────────
    // CASE 3: HIDDEN WEIGHTED BIT (EXPONENTIAL SEPARATION)
    // ────────────────────────────────────────────────────────────────────────

    if n >= 4 {
        println!("── Case 3: Hierarchical XOR (Exponential Separation Example) ──\n");

        // ((x₁ ⊕ x₂) ∧ (x₃ ⊕ x₄)) ∨ (¬(x₁ ⊕ x₂) ∧ (x₅ ⊕ x₆))
        // This type of formula can show exponential SDD vs BDD differences

        let mgr = SddManager::new(n.max(6));
        let x1 = mgr.var(1);
        let x2 = mgr.var(2);
        let x3 = mgr.var(3);
        let x4 = mgr.var(4);
        let x5 = mgr.var(5);
        let x6 = mgr.var(6);

        let xor12 = mgr.xor(x1, x2);
        let xor34 = mgr.xor(x3, x4);
        let xor56 = mgr.xor(x5, x6);

        let hwb = mgr.or(mgr.and(xor12, xor34), mgr.and(mgr.neg(xor12), xor56));

        println!("Formula: ((x₁ ⊕ x₂) ∧ (x₃ ⊕ x₄)) ∨ (¬(x₁ ⊕ x₂) ∧ (x₅ ⊕ x₆))\n");

        println!("  SDD size:    {} nodes", mgr.size(hwb));
        println!("  Model count: {}", mgr.model_count(hwb));
        println!();
        println!("Analysis:");
        println!("  • This formula selects which subformula based on x₁⊕x₂");
        println!("  • With balanced vtree: compact representation");
        println!("  • Generalizing: SDDs can be exponentially smaller than BDDs");
        println!("  • Reference: Darwiche (2011) 'SDD: A New Canonical Representation'");
        println!();
    }

    // ────────────────────────────────────────────────────────────────────────
    // CASE 4: AT-MOST-K
    // ────────────────────────────────────────────────────────────────────────

    if n >= 4 {
        println!("── Case 4: At-Most-1 (Threshold Function) ──\n");

        let mgr = SddManager::new(n);
        let vars: Vec<_> = (1..=n).map(|i| mgr.var(i)).collect();

        // At most 1: for all pairs (i,j), ¬(xᵢ ∧ xⱼ)
        let mut at_most_1 = mgr.true_sdd();
        for i in 0..vars.len() {
            for j in (i + 1)..vars.len() {
                let not_both = mgr.neg(mgr.and(vars[i], vars[j]));
                at_most_1 = mgr.and(at_most_1, not_both);
            }
        }

        println!("Formula: At-Most-1(x1, ..., x{})", n);
        println!("  = ∧_{{i<j}} ¬(xᵢ ∧ xⱼ)\n");

        println!("  SDD size:    {} nodes", mgr.size(at_most_1));
        println!("  Model count: {} (n+1 = {} choices)", mgr.model_count(at_most_1), n + 1);
        println!();
        println!("Analysis:");
        println!("  • Threshold functions have O(n²) BDD size");
        println!("  • SDDs also O(n²) for this encoding");
        println!("  • Both benefit from good variable grouping");
        println!();
    }

    // ────────────────────────────────────────────────────────────────────────
    // CASE 5: PRODUCT OF SUMS
    // ────────────────────────────────────────────────────────────────────────

    if n >= 6 {
        println!("── Case 5: CNF (Product of Sums) ──\n");

        let mgr = SddManager::new(n);

        // Random-ish 3-CNF
        let c1 = mgr.clause([1, 2, 3]);
        let c2 = mgr.clause([-1, 4, 5]);
        let c3 = mgr.clause([2, -4, 6]);
        let c4 = mgr.clause([-2, -3, -5]);
        let c5 = mgr.clause([1, -6, 3]);

        let cnf = mgr.and_all([c1, c2, c3, c4, c5]);

        println!("Formula: 5 clauses of 3-CNF over {} variables\n", n);

        println!("  SDD size:    {} nodes", mgr.size(cnf));
        println!("  Model count: {}", mgr.model_count(cnf));
        println!();
        println!("Analysis:");
        println!("  • CNF compilation is core to SAT solving");
        println!("  • SDDs enable efficient #SAT after compilation");
        println!("  • Vtree should group variables appearing together");
        println!();
    }

    // ────────────────────────────────────────────────────────────────────────
    // CASE 6: HIERARCHICAL STRUCTURE
    // ────────────────────────────────────────────────────────────────────────

    if n >= 8 {
        println!("── Case 6: Hierarchical Structure ──\n");

        let mgr = SddManager::new(8);
        let vars: Vec<_> = (1..=8).map(|i| mgr.var(i)).collect();

        // Build ((x₁∧x₂)∨(x₃∧x₄)) ∧ ((x₅∧x₆)∨(x₇∧x₈))
        let left = mgr.or(mgr.and(vars[0], vars[1]), mgr.and(vars[2], vars[3]));
        let right = mgr.or(mgr.and(vars[4], vars[5]), mgr.and(vars[6], vars[7]));
        let hierarchical = mgr.and(left, right);

        println!("Formula: ((x₁∧x₂)∨(x₃∧x₄)) ∧ ((x₅∧x₆)∨(x₇∧x₈))\n");

        println!("  SDD size:    {} nodes", mgr.size(hierarchical));
        println!("  Model count: {}", mgr.model_count(hierarchical));
        println!();
        println!("Analysis:");
        println!("  • Formula has natural tree structure");
        println!("  • Balanced vtree mirrors formula structure → compact SDD");
        println!("  • Linear ordering loses this structure → larger BDD");
        println!();
    }

    // ────────────────────────────────────────────────────────────────────────
    // RIGHT-LINEAR = BDD
    // ────────────────────────────────────────────────────────────────────────

    println!("── BDD as Special Case of SDD ──\n");

    println!("With a right-linear vtree, SDDs reduce to BDDs:\n");

    println!("  Right-linear vtree (for n=4):");
    println!();
    println!("        (root)");
    println!("        /    \\");
    println!("       x₁    ( )");
    println!("            /   \\");
    println!("           x₂   ( )");
    println!("               /   \\");
    println!("              x₃   x₄");
    println!();
    println!("  Each internal node decomposes on one variable,");
    println!("  equivalent to Shannon expansion in BDDs.");
    println!();

    // Compare sizes across vtree types
    let test_n = n.min(6);
    println!("Comparison for x1 ∧ x2 ∧ ... ∧ x{}:\n", test_n);

    println!("  Vtree Type     Size");
    println!("  ────────────   ─────");

    for (name, mgr) in [
        ("Balanced    ", SddManager::new(test_n)),
        ("Right-linear", SddManager::with_right_linear_vtree(test_n)),
        ("Left-linear ", SddManager::with_left_linear_vtree(test_n)),
    ] {
        let mut conj = mgr.var(1);
        for i in 2..=test_n {
            conj = mgr.and(conj, mgr.var(i));
        }
        println!("  {}   {:>5}", name, mgr.size(conj));
    }
    println!();

    // ────────────────────────────────────────────────────────────────────────
    // SUMMARY
    // ────────────────────────────────────────────────────────────────────────

    println!("─── Summary: When to Use Each ───\n");

    println!("Choose SDDs when:");
    println!("  ✓ Formula has hierarchical/tree structure");
    println!("  ✓ Related variables can be grouped in vtree");
    println!("  ✓ Need vtree optimization flexibility");
    println!("  ✓ Working with probabilistic inference (WMC)");
    println!();

    println!("Choose BDDs when:");
    println!("  ✓ Natural linear variable ordering exists");
    println!("  ✓ Simpler implementation is needed");
    println!("  ✓ Dynamic variable reordering is sufficient");
    println!("  ✓ Formula is already in good linear order");
    println!();

    println!("Theoretical relationship:");
    println!("  • BDDs ⊂ SDDs (strict subset)");
    println!("  • Some functions: SDD exponentially smaller than any BDD");
    println!("  • No function: BDD exponentially smaller than optimal SDD");
    println!();

    println!("Done.");
}
