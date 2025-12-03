//! Vtree Exploration Example.
//!
//! Demonstrates different vtree structures and their impact on SDD size:
//! - Balanced vtrees: good general-purpose choice
//! - Right-linear: similar to BDD variable ordering
//! - Left-linear: reversed ordering
//! - Custom vtrees: user-defined variable groupings
//!
//! The vtree structure determines SDD canonicity and can dramatically
//! affect the size of the representation.
//!
//! Run with: `cargo run --example vtree`
//! Or with options: `cargo run --example vtree -- -n 6 -v`

use clap::Parser;
use sdd::vtree::{VtreeId, VtreeNode};
use sdd::SddManager;

#[derive(Parser, Debug)]
#[command(name = "vtree")]
#[command(about = "Explore vtree structures and their impact on SDD size")]
struct Args {
    /// Number of variables (must be even for some examples)
    #[arg(short, long, default_value_t = 4)]
    n: u32,

    /// Show verbose vtree structure
    #[arg(short, long)]
    verbose: bool,
}

fn main() {
    let args = Args::parse();
    let n = args.n;

    println!("─── Vtree Structures and Their Impact on SDDs ───\n");

    // ────────────────────────────────────────────────────────────────────────
    // INTRODUCTION
    // ────────────────────────────────────────────────────────────────────────

    println!("── Introduction ──\n");

    println!("A vtree (variable tree) is a full binary tree whose leaves are");
    println!("Boolean variables. The structure determines how SDDs decompose");
    println!("formulas into (prime, sub) pairs.\n");

    println!("Key insight: Different vtrees can yield exponentially different");
    println!("SDD sizes for the same Boolean function!\n");

    println!("Variables: n = {}\n", n);

    // ────────────────────────────────────────────────────────────────────────
    // BALANCED VTREE
    // ────────────────────────────────────────────────────────────────────────

    println!("── 1. Balanced Vtree ──\n");

    println!("Structure (for n=4):\n");
    println!("            (6)       <- root, position=6");
    println!("           /   \\");
    println!("         (2)   (5)     <- internal nodes");
    println!("         / \\   / \\");
    println!("        x₁ x₂ x₃  x₄    <- leaves (positions 0,1,3,4)");
    println!();
    println!("Properties:");
    println!("  • Height: O(log n)");
    println!("  • Balanced decomposition");
    println!("  • Good for symmetric formulas");
    println!();

    let mgr_balanced = SddManager::new(n);
    if args.verbose {
        println!("Vtree structure:");
        print_vtree(&mgr_balanced);
        println!();
    }
    demo_formulas(&mgr_balanced, "Balanced", n);

    // ────────────────────────────────────────────────────────────────────────
    // RIGHT-LINEAR VTREE
    // ────────────────────────────────────────────────────────────────────────

    println!("── 2. Right-Linear Vtree ──\n");

    println!("Structure (for n=4):\n");
    println!("            (6)     <- root");
    println!("            / \\");
    println!("           x₁ (4)");
    println!("              / \\");
    println!("             x₂ (2)");
    println!("                / \\");
    println!("               x₃ x₄");
    println!();
    println!("Properties:");
    println!("  • Similar to BDD variable ordering");
    println!("  • Height: O(n)");
    println!("  • Good when natural left-to-right order exists");
    println!("  • Apply algorithm recursively refines on the right");
    println!();

    let mgr_right = SddManager::with_right_linear_vtree(n);
    if args.verbose {
        println!("Vtree structure:");
        print_vtree(&mgr_right);
        println!();
    }
    demo_formulas(&mgr_right, "Right-linear", n);

    // ────────────────────────────────────────────────────────────────────────
    // LEFT-LINEAR VTREE
    // ────────────────────────────────────────────────────────────────────────

    println!("── 3. Left-Linear Vtree ──\n");

    println!("Structure (for n=4):\n");
    println!("        (6)         <- root");
    println!("        / \\");
    println!("       (4) x₄");
    println!("      / \\");
    println!("     (2) x₃");
    println!("    / \\");
    println!("   x₁ x₂");
    println!();
    println!("Properties:");
    println!("  • Opposite of right-linear");
    println!("  • Last variable at top level");
    println!("  • Height: O(n)");
    println!("  • Apply algorithm recursively refines on the left");
    println!();

    let mgr_left = SddManager::with_left_linear_vtree(n);
    if args.verbose {
        println!("Vtree structure:");
        print_vtree(&mgr_left);
        println!();
    }
    demo_formulas(&mgr_left, "Left-linear", n);

    // ────────────────────────────────────────────────────────────────────────
    // POSITION TRACKING
    // ────────────────────────────────────────────────────────────────────────

    println!("── 4. Vtree Position Tracking ──\n");

    println!("Each vtree node has an in-order position used by the apply algorithm");
    println!("to determine which case to use:\n");

    let mgr4 = SddManager::new(4);
    let vtree = mgr4.vtree();

    println!("Positions for balanced vtree with 4 variables:\n");
    println!("  Node  Type       Position");
    println!("  ────  ─────────  ────────");

    for i in 0..vtree.num_nodes() {
        let id = VtreeId::new(i as u32);
        let node = vtree.node(id);
        let pos = vtree.position(id);

        match node {
            VtreeNode::Leaf { var } => {
                println!("  v{:<3}  Leaf(x{})   {}", i, var, pos);
            }
            VtreeNode::Internal { .. } => {
                println!("  v{:<3}  Internal   {}", i, pos);
            }
        }
    }
    println!();

    println!("Apply algorithm uses positions to detect cases:");
    println!("  • pos(a) == pos(b)  → equal vtrees");
    println!("  • pos(a) < pos(b)   → a is strictly left of b");
    println!("  • pos(a) > pos(b)   → a is strictly right of b");
    println!("  • otherwise         → incomparable (need LCA)");
    println!();

    // ────────────────────────────────────────────────────────────────────────
    // SIZE COMPARISON
    // ────────────────────────────────────────────────────────────────────────

    println!("── 5. Size Comparison ──\n");

    compare_xor_chain(n);
    println!();
    compare_equality(n);
    println!();
    compare_interleaved(n);
    println!();

    // ────────────────────────────────────────────────────────────────────────
    // EXPONENTIAL SEPARATION
    // ────────────────────────────────────────────────────────────────────────

    println!("── 6. Exponential Separation ──\n");

    println!("Some formulas exhibit exponential size differences between vtrees.\n");

    // Hidden weighted bit function: a classic separation example
    if n >= 4 {
        let n2 = n.min(8); // limit for demo

        println!("Formula: Parity with interleaved groups\n");
        println!("  f = (x₁ ⊕ x₂) ∧ (x₃ ⊕ x₄) ∧ ... (for half the vars)");
        println!("      i.e., adjacent pairs must have different values\n");

        for (name, mgr) in [
            ("Balanced    ", SddManager::new(n2)),
            ("Right-linear", SddManager::with_right_linear_vtree(n2)),
            ("Left-linear ", SddManager::with_left_linear_vtree(n2)),
        ] {
            let mut f = mgr.true_sdd();
            for i in (1..n2).step_by(2) {
                let xor = mgr.xor(mgr.var(i), mgr.var(i + 1));
                f = mgr.and(f, xor);
            }
            println!("    {}: {:>4} nodes, #SAT = {}", name, mgr.size(f), mgr.model_count(f));
        }
        println!();
    }

    // ────────────────────────────────────────────────────────────────────────
    // DOT VISUALIZATION
    // ────────────────────────────────────────────────────────────────────────

    println!("── 7. Vtree Visualization ──\n");

    println!("Generate DOT output for vtree visualization:\n");

    let mgr = SddManager::new(4);
    let dot = mgr.vtree_to_dot();

    // Write DOT to temp file
    let dot_path = "/tmp/vtree_example.dot";
    std::fs::write(dot_path, &dot).expect("Failed to write DOT file");

    println!("DOT output written to: {}", dot_path);
    println!("  Lines: {}", dot.lines().count());
    println!();
    println!("Render with: dot -O -Tsvg {}", dot_path);
    println!();

    // ────────────────────────────────────────────────────────────────────────
    // SUMMARY
    // ────────────────────────────────────────────────────────────────────────

    println!("─── Summary ───\n");

    println!("Vtree structure significantly impacts SDD size:");
    println!("  • Variables in same subtree share decomposition");
    println!("  • Related variables should be grouped together");
    println!("  • Finding optimal vtree is NP-hard");
    println!("  • Balanced vtrees are a good default choice");
    println!();
    println!("Practical guidelines:");
    println!("  • Group variables that interact strongly");
    println!("  • XOR/parity: any order works well");
    println!("  • Equivalence chains: group paired variables");
    println!("  • CNF: group variables in same clause");
    println!();

    println!("Done.");
}

/// Print vtree in compact text format.
fn print_vtree(mgr: &SddManager) {
    let vtree = mgr.vtree();
    for i in 0..vtree.num_nodes() {
        let id = VtreeId::new(i as u32);
        let node = vtree.node(id);
        let pos = vtree.position(id);

        match node {
            VtreeNode::Leaf { var } => {
                println!("  [{}] Leaf(x{})  pos={}", i, var, pos);
            }
            VtreeNode::Internal { left, right } => {
                println!("  [{}] Internal(L={}, R={})  pos={}", i, left.raw(), right.raw(), pos);
            }
        }
    }
}

/// Demonstrates key formulas on a given manager.
fn demo_formulas(mgr: &SddManager, name: &str, n: u32) {
    // Build (x₁ ∧ x₂) ∨ (x_{n-1} ∧ x_n)
    let x1 = mgr.var(1);
    let x2 = mgr.var(2);
    let xn1 = mgr.var(n - 1);
    let xn = mgr.var(n);

    let f = mgr.or(mgr.and(x1, x2), mgr.and(xn1, xn));

    println!("  {} vtree:", name);
    println!("    f = (x₁ ∧ x₂) ∨ (x_{} ∧ x{})", n - 1, n);
    println!("    Size: {} nodes", mgr.size(f));
    println!("    #SAT: {}", mgr.model_count(f));
    println!();
}

/// Compares XOR chain across vtree types.
fn compare_xor_chain(n: u32) {
    println!("XOR chain: x₁ ⊕ x₂ ⊕ ... ⊕ x{}\n", n);

    println!("  Vtree Type     Nodes  #SAT");
    println!("  ────────────   ─────  ────────");

    for (name, mgr) in [
        ("Balanced    ", SddManager::new(n)),
        ("Right-linear", SddManager::with_right_linear_vtree(n)),
        ("Left-linear ", SddManager::with_left_linear_vtree(n)),
    ] {
        // Build XOR chain incrementally
        let mut xor = mgr.var(1);
        for i in 2..=n {
            xor = mgr.xor(xor, mgr.var(i));
        }

        println!("  {}   {:>5}  {}", name, mgr.size(xor), mgr.model_count(xor));
    }

    println!();
    println!("  Note: XOR is symmetric, so vtree structure has moderate impact.");
}

/// Compares equality formula across vtree types.
fn compare_equality(n: u32) {
    // Need even n for pairing
    let n = if n % 2 == 1 { n - 1 } else { n };
    if n < 2 {
        return;
    }

    println!("Equality: (x₁ ↔ x{}) ∧ (x₂ ↔ x{}) ∧ ...\n", n / 2 + 1, n / 2 + 2);

    println!("  Vtree Type     Nodes  #SAT");
    println!("  ────────────   ─────  ────────");

    for (name, mgr) in [
        ("Balanced    ", SddManager::new(n)),
        ("Right-linear", SddManager::with_right_linear_vtree(n)),
        ("Left-linear ", SddManager::with_left_linear_vtree(n)),
    ] {
        // Build conjunction of equivalences: xᵢ ↔ x_{n/2+i}
        let half = n / 2;
        let mut eq = mgr.true_sdd();
        for i in 1..=half {
            let equiv = mgr.equiv(mgr.var(i), mgr.var(half + i));
            eq = mgr.and(eq, equiv);
        }

        println!("  {}   {:>5}  {}", name, mgr.size(eq), mgr.model_count(eq));
    }

    println!();
    println!("  Note: This formula benefits when paired variables are");
    println!("        grouped together in the vtree.");
}

/// Compares interleaved AND-OR pattern.
fn compare_interleaved(n: u32) {
    if n < 4 {
        return;
    }

    println!("Interleaved: (x₁ ∨ x₂) ∧ (x₃ ∨ x₄) ∧ ...\n");

    println!("  Vtree Type     Nodes  #SAT");
    println!("  ────────────   ─────  ────────");

    for (name, mgr) in [
        ("Balanced    ", SddManager::new(n)),
        ("Right-linear", SddManager::with_right_linear_vtree(n)),
        ("Left-linear ", SddManager::with_left_linear_vtree(n)),
    ] {
        let mut f = mgr.true_sdd();
        for i in (1..n).step_by(2) {
            let clause = mgr.or(mgr.var(i), mgr.var(i + 1));
            f = mgr.and(f, clause);
        }

        println!("  {}   {:>5}  {}", name, mgr.size(f), mgr.model_count(f));
    }

    println!();
    println!("  Note: Adjacent pairs are grouped, so vtree matters less.");
}
