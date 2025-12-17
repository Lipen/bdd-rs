//! ZDD to DOT visualization examples.
//!
//! This example demonstrates how to export ZDDs to GraphViz DOT format
//! and shows various ZDD operations and families.
//!
//! Run with:
//!   cargo run --example dot-visualization
//!   cargo run --example dot-visualization -- --render  # Also render to PNG/SVG/PDF

use std::env;
use std::fs;
use std::process::Command;

use ananke_zdd::types::Var;
use ananke_zdd::zdd::ZddManager;

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let output_dir = env::current_dir()?.join("dot_output");
    fs::create_dir_all(&output_dir)?;

    println!("=== ZDD to DOT Visualization Examples ===");
    println!("Output directory: {}\n", output_dir.display());

    let mut examples = Vec::new();

    // ========================================================================
    // Basic Operations
    // ========================================================================

    // Example: Base sets (singletons)
    {
        let name = "01_base_sets";
        let mgr = ZddManager::new();
        let x1 = mgr.base(1);
        let x2 = mgr.base(2);

        println!("Example: {}", name);
        println!("  Formula: {{{{1}}}}, {{{{2}}}}");
        println!("  Sizes: x1={} nodes, x2={} nodes\n", mgr.node_count(x1), mgr.node_count(x2));

        fs::write(
            output_dir.join(format!("{}.dot", name)),
            format!(
                "digraph {{\n  label=\"Base Sets: x1={{{{1}}}}, x2={{{{2}}}}\"\n\n{}\n}}",
                mgr.to_dot(x1)
                    .lines()
                    .filter(|l| !l.contains("digraph") && !l.contains("}}"))
                    .collect::<Vec<_>>()
                    .join("\n")
            ),
        )?;
        examples.push(name);
    }

    // Example: Union and Intersection
    {
        let name = "02_union_intersection";
        let mgr = ZddManager::new();
        let x1 = mgr.base(1);
        let x2 = mgr.base(2);
        let union = mgr.union(x1, x2);
        let inter = mgr.intersection(union, x1);

        println!("Example: {}", name);
        println!("  Formulas: {{{{1}}}} ∪ {{{{2}}}}, ({{{{1}}}} ∪ {{{{2}}}}) ∩ {{{{1}}}}");
        println!(
            "  Sizes: union={} nodes, inter={} nodes\n",
            mgr.node_count(union),
            mgr.node_count(inter)
        );

        fs::write(output_dir.join(format!("{}.dot", name)), mgr.to_dot(union))?;
        examples.push(name);
    }

    // Example: Join (Cross Product)
    {
        let name = "03_join";
        let mgr = ZddManager::new();
        let x1 = mgr.base(1);
        let x2 = mgr.base(2);
        let x3 = mgr.base(3);
        let join_12 = mgr.join(x1, x2);
        let join_123 = mgr.join(join_12, x3);

        println!("Example: {}", name);
        println!("  Formula: {{{{1}}}} ⊗ {{{{2}}}} ⊗ {{{{3}}}} = {{{{1,2,3}}}}");
        println!("  Size: {} nodes\n", mgr.node_count(join_123));

        fs::write(output_dir.join(format!("{}.dot", name)), mgr.to_dot(join_123))?;
        examples.push(name);
    }

    // ========================================================================
    // Set-Theoretic Operations
    // ========================================================================

    // Example: Powerset
    {
        let name = "04_powerset";
        let mgr = ZddManager::new();
        let ps = mgr.powerset([1u32, 2, 3]);

        println!("Example: {}", name);
        println!("  Formula: 2^{{1,2,3}} (power set)");
        println!("  Size: {} nodes, contains {} sets\n", mgr.node_count(ps), mgr.count(ps));

        fs::write(output_dir.join(format!("{}.dot", name)), mgr.to_dot(ps))?;
        examples.push(name);
    }

    // Example: Combinations
    {
        let name = "05_combinations";
        let mgr = ZddManager::new();
        let c43 = mgr.combinations([1u32, 2, 3, 4], 2);

        println!("Example: {}", name);
        println!("  Formula: C(4, 2) = all 2-element subsets of {{1,2,3,4}}");
        println!("  Size: {} nodes, contains {} sets\n", mgr.node_count(c43), mgr.count(c43));

        fs::write(output_dir.join(format!("{}.dot", name)), mgr.to_dot(c43))?;
        examples.push(name);
    }

    // ========================================================================
    // ZDD-Specific Operations
    // ========================================================================

    // Example: Subset Operations
    {
        let name = "06_subset_ops";
        let mgr = ZddManager::new();

        // Create family: {{1}, {2}, {1,2}}
        let x1 = mgr.base(1);
        let x2 = mgr.base(2);
        let x12 = mgr.join(x1, x2);
        let family = mgr.union(mgr.union(x1, x2), x12);

        // subset0: sets NOT containing variable 1
        let subset0 = mgr.subset0(family, Var::new(1));

        println!("Example: {}", name);
        println!("  Family: {{{{1}}, {{2}}, {{1,2}}}}");
        println!("  subset0(F, 1): sets without 1 = {{{{2}}}}");
        println!("  Size: {} nodes, contains {} sets\n", mgr.node_count(subset0), mgr.count(subset0));

        fs::write(output_dir.join(format!("{}.dot", name)), mgr.to_dot(subset0))?;
        examples.push(name);
    }

    // Example: Change Operation
    {
        let name = "07_change_op";
        let mgr = ZddManager::new();

        // Create family: {{1}, {2}, {1,2}}
        let x1 = mgr.base(1);
        let x2 = mgr.base(2);
        let x12 = mgr.join(x1, x2);
        let family = mgr.union(mgr.union(x1, x2), x12);

        // Toggle variable 1 in all sets
        let changed = mgr.change(family, Var::new(1));

        println!("Example: {}", name);
        println!("  Family: {{{{1}}, {{2}}, {{1,2}}}}");
        println!("  change(F, 1): toggle 1 in all sets");
        println!("  Size: {} nodes, contains {} sets\n", mgr.node_count(changed), mgr.count(changed));

        fs::write(output_dir.join(format!("{}.dot", name)), mgr.to_dot(changed))?;
        examples.push(name);
    }

    // Example: Difference Operation
    {
        let name = "08_difference";
        let mgr = ZddManager::new();

        // Create families: F = {{1}, {2}, {1,2}}, G = {{1}}
        let x1 = mgr.base(1);
        let x2 = mgr.base(2);
        let x12 = mgr.join(x1, x2);
        let f = mgr.union(mgr.union(x1, x2), x12);
        let g = x1;

        // F \ G
        let diff = mgr.difference(f, g);

        println!("Example: {}", name);
        println!("  F: {{{{1}}, {{2}}, {{1,2}}}}");
        println!("  G: {{{{1}}}}");
        println!("  F \\ G: {{{{2}}, {{1,2}}}}");
        println!("  Size: {} nodes, contains {} sets\n", mgr.node_count(diff), mgr.count(diff));

        fs::write(output_dir.join(format!("{}.dot", name)), mgr.to_dot(diff))?;
        examples.push(name);
    }

    // ========================================================================
    // Complex Examples
    // ========================================================================

    // Example: Meet Operation (pairwise intersection)
    {
        let name = "09_meet";
        let mgr = ZddManager::new();

        // Create families: F = {{1}, {1,2}}, G = {{1,3}, {1,2,3}}
        let x1 = mgr.base(1);
        let x2 = mgr.base(2);
        let x3 = mgr.base(3);

        let x12 = mgr.join(x1, x2);
        let x13 = mgr.join(x1, x3);
        let f = mgr.union(x1, x12);

        let x123 = mgr.join(x12, x3);
        let g = mgr.union(x13, x123);

        // Meet: pairwise intersections of non-empty sets
        let meet = mgr.meet(f, g);

        println!("Example: {}", name);
        println!("  F: {{{{1}}, {{1,2}}}}");
        println!("  G: {{{{1,3}}, {{1,2,3}}}}");
        println!("  meet(F, G): pairwise intersections");
        println!("  Size: {} nodes, contains {} sets\n", mgr.node_count(meet), mgr.count(meet));

        fs::write(output_dir.join(format!("{}.dot", name)), mgr.to_dot(meet))?;
        examples.push(name);
    }

    // Example: Singleton sets
    {
        let name = "10_singleton";
        let mgr = ZddManager::new();

        // Create singleton: {{1, 2, 3}}
        let singleton = mgr.singleton([1u32, 2, 3]);

        println!("Example: {}", name);
        println!("  Formula: {{{{1, 2, 3}}}} (single set with three elements)");
        println!(
            "  Size: {} nodes, contains {} set\n",
            mgr.node_count(singleton),
            mgr.count(singleton)
        );

        fs::write(output_dir.join(format!("{}.dot", name)), mgr.to_dot(singleton))?;
        examples.push(name);
    }

    // Example: Terminals
    {
        let name = "11_terminals";
        let mgr = ZddManager::new();

        // ZERO and ONE terminals
        let zero = mgr.zero();
        let one = mgr.one();

        println!("Example: {}", name);
        println!("  ZERO (⊥): empty family - no sets");
        println!("  ONE (⊤): family containing empty set {{∅}}");
        println!("  Sizes: zero={} nodes, one={} nodes\n", mgr.node_count(zero), mgr.node_count(one));

        fs::write(output_dir.join(format!("{}.dot", name)), mgr.to_dot(one))?;
        examples.push(name);
    }

    // ========================================================================
    // More Complex Examples
    // ========================================================================

    // Example: Onset - Keep sets containing variable while preserving the variable
    {
        let name = "12_onset";
        let mgr = ZddManager::new();

        // Create family: {{1}, {2}, {1,2}, {1,3}}
        let x1 = mgr.base(1);
        let x2 = mgr.base(2);
        let x3 = mgr.base(3);

        let x12 = mgr.join(x1, x2);
        let x13 = mgr.join(x1, x3);
        let family = mgr.union(mgr.union(mgr.union(x1, x2), x12), x13);

        // Onset: sets containing variable 1 (keeping 1)
        let onset = mgr.onset(family, Var::new(1));

        println!("Example: {}", name);
        println!("  Family: {{{{1}}, {{2}}, {{1,2}}, {{1,3}}}}");
        println!("  onset(F, 1): sets containing 1 = {{{{1}}, {{1,2}}, {{1,3}}}}");
        println!("  Size: {} nodes, contains {} sets\n", mgr.node_count(onset), mgr.count(onset));

        fs::write(output_dir.join(format!("{}.dot", name)), mgr.to_dot(onset))?;
        examples.push(name);
    }

    // Example: Symmetric difference
    {
        let name = "13_symmetric_diff";
        let mgr = ZddManager::new();

        // Create two families
        // F = {{1}, {1,2}}
        let x1 = mgr.base(1);
        let x2 = mgr.base(2);
        let x12 = mgr.join(x1, x2);
        let f = mgr.union(x1, x12);

        // G = {{2}, {1,2}}
        let g = mgr.union(x2, x12);

        // Symmetric difference: (F \ G) ∪ (G \ F)
        let sym_diff = mgr.symmetric_difference(f, g);

        println!("Example: {}", name);
        println!("  F: {{{{1}}, {{1,2}}}}");
        println!("  G: {{{{2}}, {{1,2}}}}");
        println!("  F △ G: {{{{1}}, {{2}}}} (elements in exactly one family)");
        println!(
            "  Size: {} nodes, contains {} sets\n",
            mgr.node_count(sym_diff),
            mgr.count(sym_diff)
        );

        fs::write(output_dir.join(format!("{}.dot", name)), mgr.to_dot(sym_diff))?;
        examples.push(name);
    }

    // ========================================================================
    // Render if requested
    // ========================================================================

    if env::args().any(|arg| arg == "--render") {
        println!("=== Rendering with Graphviz ===\n");

        for name in &examples {
            let input = output_dir.join(format!("{}.dot", name));
            for fmt in ["png", "svg", "pdf"] {
                let output = output_dir.join(format!("{}.{}", name, fmt));
                match Command::new("dot")
                    .arg(format!("-T{}", fmt))
                    .arg(&input)
                    .arg("-o")
                    .arg(&output)
                    .status()
                {
                    Ok(s) if s.success() => println!("  ✓ {}.{}", name, fmt),
                    Ok(_) => eprintln!("  ✗ Failed: {}.{}", name, fmt),
                    Err(e) => {
                        eprintln!("  ✗ Error: {} (Is Graphviz installed?)", e);
                        break;
                    }
                }
            }
        }

        println!("\nOpen in browser:");
        for name in &examples {
            println!("  file://{}/{}.svg", output_dir.display(), name);
        }
    } else {
        println!("=== DOT files created ===");
        println!("\nTo render: cargo run --example dot-visualization -- --render");
        println!("Or manually: dot -Tsvg {}/01_base_sets.dot -o out.svg", output_dir.display());
    }

    Ok(())
}
