//! Loop Analysis Example
//!
//! Demonstrates loop detection in CFGs.
//!
//! Run with: `cargo run -p tbdd-pbt --example loop_analysis`

use tbdd_pbt::cfg::{CfgBuilder, Terminator};
use tbdd_pbt::loops::{find_containing_loop, is_back_edge, LoopDetector};
use tbdd_pbt::{BlockId, Predicate};

fn main() {
    println!("══════════════════════════════════════════════════════════════");
    println!("  T-BDD: Loop Detection and Analysis");
    println!("══════════════════════════════════════════════════════════════\n");

    // ─────────────────────────────────────────────────────────────────────────
    // Example 1: Simple while loop
    // ─────────────────────────────────────────────────────────────────────────

    println!("── EXAMPLE 1: Simple While Loop ───────────────────────────────");
    println!();
    println!("  Modeling:");
    println!("    let mut sum = 0;");
    println!("    let mut i = 0;");
    println!("    while i < n {{");
    println!("        sum += i;");
    println!("        i += 1;");
    println!("    }}");
    println!();

    let cfg1 = build_simple_loop();
    let loops1 = LoopDetector::detect(&cfg1);

    println!("  CFG Statistics:");
    println!("    Blocks: {}", cfg1.num_blocks());
    println!("    Edges:  {}", cfg1.num_edges());
    println!();

    println!("  Detected Loops: {}", loops1.len());
    for (i, loop_info) in loops1.iter().enumerate() {
        println!("    Loop {}:", i + 1);
        println!("      Header: {}", loop_info.header);
        println!("      Tail:   {}", loop_info.tail);
        println!(
            "      Body:   {{{}}}",
            loop_info.body.iter().map(|id| id.to_string()).collect::<Vec<_>>().join(", ")
        );
        println!(
            "      Exits:  [{}]",
            loop_info
                .exit_targets
                .iter()
                .map(|id| id.to_string())
                .collect::<Vec<_>>()
                .join(", ")
        );
        println!("      Depth:  {}", loop_info.nesting_depth);
    }
    println!();

    // ─────────────────────────────────────────────────────────────────────────
    // Example 2: Nested loops
    // ─────────────────────────────────────────────────────────────────────────

    println!("── EXAMPLE 2: Nested Loops ────────────────────────────────────");
    println!();
    println!("  Modeling:");
    println!("    for i in 0..n {{");
    println!("        for j in 0..m {{");
    println!("            process(i, j);");
    println!("        }}");
    println!("    }}");
    println!();

    let cfg2 = build_nested_loop();
    let loops2 = LoopDetector::detect(&cfg2);

    println!("  CFG Statistics:");
    println!("    Blocks: {}", cfg2.num_blocks());
    println!("    Edges:  {}", cfg2.num_edges());
    println!();

    println!("  Detected Loops: {}", loops2.len());
    for (i, loop_info) in loops2.iter().enumerate() {
        let depth_str = match loop_info.nesting_depth {
            0 => "outermost",
            1 => "nested (depth 1)",
            _ => "deeply nested",
        };
        println!("    Loop {}: header={}, {}", i + 1, loop_info.header, depth_str);
        if let Some(parent) = loop_info.parent {
            println!("            parent={}", parent);
        }
    }
    println!();

    // ─────────────────────────────────────────────────────────────────────────
    // Example 3: Back edge detection
    // ─────────────────────────────────────────────────────────────────────────

    println!("── EXAMPLE 3: Back Edge Detection ─────────────────────────────");
    println!();

    println!("  Checking edges in simple loop CFG:");
    let edges_to_check = [
        (BlockId(0), BlockId(1), "entry -> header"),
        (BlockId(1), BlockId(2), "header -> body (true branch)"),
        (BlockId(1), BlockId(3), "header -> exit (false branch)"),
        (BlockId(2), BlockId(1), "body -> header (back edge!)"),
    ];

    for (from, to, description) in edges_to_check {
        let is_back = is_back_edge(from, to, &loops1);
        let marker = if is_back { "←── BACK EDGE" } else { "" };
        println!("    {} {} {}", description, if is_back { "✓" } else { "✗" }, marker);
    }
    println!();

    // ─────────────────────────────────────────────────────────────────────────
    // Example 4: Block containment
    // ─────────────────────────────────────────────────────────────────────────

    println!("── EXAMPLE 4: Loop Containment ────────────────────────────────");
    println!();

    println!("  Which blocks belong to which loops (nested CFG)?");
    for block in &cfg2.blocks {
        if let Some(loop_info) = find_containing_loop(block.id, &loops2) {
            println!("    {} → in loop with header {}", block.id, loop_info.header);
        } else {
            println!("    {} → not in any loop", block.id);
        }
    }
    println!();

    // ─────────────────────────────────────────────────────────────────────────
    // Example 5: Path enumeration with loop bound
    // ─────────────────────────────────────────────────────────────────────────

    println!("── EXAMPLE 5: Bounded Path Enumeration ────────────────────────");
    println!();

    println!("  For bounded testing, we limit loop iterations during path exploration.");
    println!("  With bound k, we explore paths with 0, 1, 2, ..., k loop iterations.");
    println!();

    let bound = 3;
    println!("  With bound = {}:", bound);
    for i in 0..=bound {
        let condition = if i == 0 {
            "¬(i < n)".to_string()
        } else {
            let enters: Vec<String> = (0..i).map(|j| format!("(i < n)@iter{}", j)).collect();
            let exit = format!("¬(i < n)@iter{}", i);
            format!("{} ∧ {}", enters.join(" ∧ "), exit)
        };
        println!("    {} iterations: {}", i, condition);
    }
    println!();

    println!("  Total distinct paths: {} (for single loop)", bound + 1);
    println!();

    // ─────────────────────────────────────────────────────────────────────────
    // DOT output
    // ─────────────────────────────────────────────────────────────────────────

    println!("── DOT VISUALIZATION ────────────────────────────────────────────");
    println!();
    println!("  Simple loop CFG:");
    println!("─────────────────────────────────────────────────────────────────");
    println!("{}", cfg1.to_dot());
    println!("─────────────────────────────────────────────────────────────────");

    println!();
    println!("══════════════════════════════════════════════════════════════");
    println!("  Loop analysis complete!");
    println!("══════════════════════════════════════════════════════════════");
}

/// Build CFG for simple while loop
fn build_simple_loop() -> tbdd_pbt::cfg::ControlFlowGraph {
    let mut builder = CfgBuilder::new();

    let entry = builder.entry();
    let header = builder.new_block("loop_header");
    let body = builder.new_block("loop_body");
    let exit = builder.new_block("exit");

    let p_lt_n = Predicate::lt_var("i", "n");

    builder.set_terminator(entry, Terminator::Goto(header));
    builder.set_terminator(
        header,
        Terminator::Branch {
            condition: p_lt_n,
            true_target: body,
            false_target: exit,
        },
    );
    builder.set_terminator(body, Terminator::Goto(header)); // Back edge!
    builder.set_terminator(exit, Terminator::Return);

    builder.build()
}

/// Build CFG for nested loops
fn build_nested_loop() -> tbdd_pbt::cfg::ControlFlowGraph {
    let mut builder = CfgBuilder::new();

    let entry = builder.entry();
    let outer_header = builder.new_block("outer_header");
    let inner_header = builder.new_block("inner_header");
    let inner_body = builder.new_block("inner_body");
    let outer_body = builder.new_block("outer_body");
    let exit = builder.new_block("exit");

    let p_i_lt_n = Predicate::lt_var("i", "n");
    let p_j_lt_m = Predicate::lt_var("j", "m");

    builder.set_terminator(entry, Terminator::Goto(outer_header));
    builder.set_terminator(
        outer_header,
        Terminator::Branch {
            condition: p_i_lt_n,
            true_target: inner_header,
            false_target: exit,
        },
    );
    builder.set_terminator(
        inner_header,
        Terminator::Branch {
            condition: p_j_lt_m,
            true_target: inner_body,
            false_target: outer_body,
        },
    );
    builder.set_terminator(inner_body, Terminator::Goto(inner_header)); // Inner back edge
    builder.set_terminator(outer_body, Terminator::Goto(outer_header)); // Outer back edge
    builder.set_terminator(exit, Terminator::Return);

    builder.build()
}
