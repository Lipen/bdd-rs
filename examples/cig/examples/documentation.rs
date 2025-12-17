//! Examples from CIG.md documentation
//!
//! Implements Examples 3.10, 4.8, 4.9, 4.10, 4.11 from the specification.
//! Run with: cargo run --example documentation

use cig::{CigBuilder, TruthTable};

fn main() {
    println!("═══════════════════════════════════════════════════════════");
    println!("                CIG Documentation Examples");
    println!("═══════════════════════════════════════════════════════════\n");

    let mut builder = CigBuilder::new();

    // Example 3.10
    println!("Example 3.10: Interaction Partition");
    println!("Function: f = (x1 AND x2) XOR x3\n");

    let f_3_10 = TruthTable::from_expr(3, |x| (x[0] && x[1]) ^ x[2]);
    let cig = builder.build(&f_3_10);

    println!("Analysis:");
    println!("  Partition: {{x1, x2}}, {{x3}}");
    println!("  Separable via XOR");
    println!("  CIG nodes: {}, depth: {}\n", cig.size(), cig.depth());

    // Example 4.8
    println!("Example 4.8: Parity Function");
    println!("Function: f = x1 XOR x2 XOR x3 XOR x4 XOR x5\n");

    let parity_5 = TruthTable::from_expr(5, |x| x.iter().fold(false, |acc, &b| acc ^ b));
    let cig = builder.build(&parity_5);

    println!("Analysis:");
    println!("  All variables independent");
    println!("  Fully separable");
    println!("  CIG nodes: {}, depth: {}\n", cig.size(), cig.depth());

    // Example 4.9
    println!("Example 4.9: Majority Function");
    println!("Function: f = MAJ3(x1, x2, x3)");
    println!("          = (x1 AND x2) OR (x2 AND x3) OR (x1 AND x3)\n");

    let maj_3 = TruthTable::from_expr(3, |x| (x[0] && x[1]) || (x[1] && x[2]) || (x[0] && x[2]));
    let cig = builder.build(&maj_3);

    println!("Analysis:");
    println!("  All variables interact irreducibly");
    println!("  NOT separable");
    println!("  CIG nodes: {}, depth: {}\n", cig.size(), cig.depth());

    // Example 4.10
    println!("Example 4.10: Multiplexer");
    println!("Function: f = MUX(s, x, y) = (NOT s AND x) OR (s AND y)\n");

    let mux = TruthTable::from_expr(3, |x| (!x[0] && x[1]) || (x[0] && x[2]));
    let cig = builder.build(&mux);

    println!("Analysis:");
    println!("  All variables interact");
    println!("  Cannot separate over any 2-1 partition");
    println!("  CIG nodes: {}, depth: {}\n", cig.size(), cig.depth());

    // Example 4.11
    println!("Example 4.11: Composed Function");
    println!("Function: f = (x1 XOR x2) AND (x3 OR x4)\n");

    let composed = TruthTable::from_expr(4, |x| (x[0] ^ x[1]) && (x[2] || x[3]));
    let cig = builder.build(&composed);

    println!("Analysis:");
    println!("  Partition: {{x1, x2}}, {{x3, x4}}");
    println!("  Separable at root via AND");
    println!("  CIG nodes: {}, depth: {}\n", cig.size(), cig.depth());

    println!("───────────────────────────────────────────────────────────");
    println!("                            SUMMARY");
    println!("───────────────────────────────────────────────────────────\n");
    println!("  Example 3.10: Decomposable structure");
    println!("  Example 4.8: Fully separable (parity)");
    println!("  Example 4.9: Fully irreducible (majority)");
    println!("  Example 4.10: Fully irreducible (multiplexer)");
    println!("  Example 4.11: Hierarchical decomposition");
    println!("\n═══════════════════════════════════════════════════════════");
}
