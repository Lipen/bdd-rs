//! Example demonstrating BDD to DOT conversion and visualization.
//!
//! This example shows how to:
//! 1. Create BDD formulas
//! 2. Convert them to DOT format
//! 3. Customize the visualization
//! 4. Generate image files using Graphviz
//!
//! # Usage
//!
//! Generate DOT files only:
//! ```bash
//! cargo run --example dot_visualization
//! ```
//!
//! Generate DOT files and render to images (requires Graphviz):
//! ```bash
//! cargo run --example dot_visualization -- --render
//! ```

use std::env;
use std::fs;
use std::process::Command;

use bdd_rs::bdd::Bdd;
use bdd_rs::dot::DotConfig;

fn main() -> Result<(), Box<dyn std::error::Error>> {
    // Create output directory in examples folder
    let output_dir = env::current_dir()?.join("examples").join("dot_output");
    fs::create_dir_all(&output_dir)?;

    println!("=== BDD to DOT Visualization Examples ===");
    println!("Output directory: {}", output_dir.display());

    let mut examples = Vec::new();

    // Example 1: Simple variable
    {
        println!("\nExample 1: Single variable");
        let name = "example1_var";
        let bdd = Bdd::default();
        let x = bdd.mk_var(1);
        println!("  Formula: x1");
        println!("  BDD size: {}", bdd.size(x));
        let dot = bdd.to_dot(&[x])?;
        fs::write(output_dir.join(format!("{}.dot", name)), &dot)?;
        examples.push(name);
    }

    // Example 2: AND operation
    {
        println!("\nExample 2: AND operation");
        let name = "example2_and";
        let bdd = Bdd::default();
        let x1 = bdd.mk_var(1);
        let x2 = bdd.mk_var(2);
        let and = bdd.apply_and(x1, x2);
        println!("  Formula: x1 ∧ x2");
        println!("  BDD size: {}", bdd.size(and));
        let dot = bdd.to_dot(&[and])?;
        fs::write(output_dir.join(format!("{}.dot", name)), &dot)?;
        examples.push(name);
    }

    // Example 3: OR operation
    {
        println!("\nExample 3: OR operation");
        let name = "example3_or";
        let bdd = Bdd::default();
        let x1 = bdd.mk_var(1);
        let x2 = bdd.mk_var(2);
        let or = bdd.apply_or(x1, x2);
        println!("  Formula: x1 ∨ x2");
        println!("  BDD size: {}", bdd.size(or));
        let dot = bdd.to_dot(&[or])?;
        fs::write(output_dir.join(format!("{}.dot", name)), &dot)?;
        examples.push(name);
    }

    // Example 4: XOR operation
    {
        println!("\nExample 4: XOR operation");
        let name = "example4_xor";
        let bdd = Bdd::default();
        let x1 = bdd.mk_var(1);
        let x2 = bdd.mk_var(2);
        let xor = bdd.apply_xor(x1, x2);
        println!("  Formula: x1 ⊕ x2");
        println!("  BDD size: {}", bdd.size(xor));
        let dot = bdd.to_dot(&[xor])?;
        fs::write(output_dir.join(format!("{}.dot", name)), &dot)?;
        examples.push(name);
    }

    // Example 5: Complex formula
    {
        println!("\nExample 5: Complex formula");
        let name = "example5_complex";
        let bdd = Bdd::default();
        let x1 = bdd.mk_var(1);
        let x2 = bdd.mk_var(2);
        let x3 = bdd.mk_var(3);
        let complex = bdd.apply_or(bdd.apply_and(x1, x2), bdd.apply_and(-x1, x3));
        println!("  Formula: (x1 ∧ x2) ∨ (¬x1 ∧ x3)");
        println!("  BDD size: {}", bdd.size(complex));
        let dot = bdd.to_dot(&[complex])?;
        fs::write(output_dir.join(format!("{}.dot", name)), &dot)?;
        examples.push(name);
    }

    // Example 6: Multiple functions (shared nodes)
    {
        println!("\nExample 6: Multiple functions with shared nodes");
        let name = "example6_multiple";
        let bdd = Bdd::default();
        let x1 = bdd.mk_var(1);
        let x2 = bdd.mk_var(2);
        let and = bdd.apply_and(x1, x2);
        let or = bdd.apply_or(x1, x2);
        let xor = bdd.apply_xor(x1, x2);
        println!("  Formulas: AND, OR, XOR of x1 and x2");
        println!("  BDD sizes: AND={}, OR={}, XOR={}", bdd.size(and), bdd.size(or), bdd.size(xor));
        let dot = bdd.to_dot(&[and, or, xor])?;
        fs::write(output_dir.join(format!("{}.dot", name)), &dot)?;
        examples.push(name);
    }

    // Example 7: Cube (conjunction of literals)
    {
        println!("\nExample 7: Cube (conjunction of literals)");
        let name = "example7_cube";
        let bdd = Bdd::default();
        let cube = bdd.cube([-1, 2, -3]);
        println!("  Formula: ¬x1 ∧ x2 ∧ ¬x3");
        println!("  BDD size: {}", bdd.size(cube));
        let dot = bdd.to_dot(&[cube])?;
        fs::write(output_dir.join(format!("{}.dot", name)), &dot)?;
        examples.push(name);
    }

    // Example 8: Custom configuration
    {
        println!("\nExample 8: Custom visualization style");
        let name = "example8_custom";
        let bdd = Bdd::default();
        let x1 = bdd.mk_var(1);
        let x2 = bdd.mk_var(2);
        let x3 = bdd.mk_var(3);
        let complex = bdd.apply_or(bdd.apply_and(x1, x2), bdd.apply_and(-x1, x3));
        println!("  Formula: (x1 ∧ x2) ∨ (¬x1 ∧ x3)");
        println!("  BDD size: {}", bdd.size(complex));
        println!("  Custom shapes and plain text labels");
        let config = DotConfig {
            node_shape: "ellipse",
            terminal_shape: "box",
            root_shape: "diamond",
            use_html_labels: false,
            ..DotConfig::default()
        };
        let dot = bdd.to_dot_with_config(&[complex], &config)?;
        fs::write(output_dir.join(format!("{}.dot", name)), &dot)?;
        examples.push(name);
    }

    // Example 9: ITE (if-then-else)
    {
        println!("\nExample 9: ITE operation");
        let name = "example9_ite";
        let bdd = Bdd::default();
        let x1 = bdd.mk_var(1);
        let x2 = bdd.mk_var(2);
        let x4 = bdd.mk_var(4);
        let ite = bdd.apply_ite(x1, x2, x4);
        println!("  Formula: ITE(x1, x2, x4) = (x1 -> x2) ∧ (¬x1 -> x4)");
        println!("  BDD size: {}", bdd.size(ite));
        let dot = bdd.to_dot(&[ite])?;
        fs::write(output_dir.join(format!("{}.dot", name)), &dot)?;
        examples.push(name);
    }

    // Render images if requested
    if env::args().any(|arg| arg == "--render") {
        println!("\n=== Rendering images with Graphviz ===\n");

        let mut svg_files = Vec::new();

        for example in &examples {
            for format in ["png", "svg", "pdf"] {
                let input = output_dir.join(format!("{}.dot", example));
                let output = output_dir.join(format!("{}.{}", example, format));

                match Command::new("dot")
                    .arg(format!("-T{}", format))
                    .arg(&input)
                    .arg("-o")
                    .arg(&output)
                    .status()
                {
                    Ok(status) if status.success() => {
                        println!("  ✓ Generated: {}.{}", example, format);
                        if format == "svg" {
                            svg_files.push(output);
                        }
                    }
                    Ok(_) => {
                        eprintln!("  ✗ Failed to generate: {}.{}", example, format);
                    }
                    Err(e) => {
                        eprintln!("  ✗ Error running dot: {}", e);
                        eprintln!("     (Is Graphviz installed?)");
                        break;
                    }
                }
            }
        }

        println!("\n=== Rendering complete! ===");
        println!("\nOpen SVG files in your browser:");
        for svg_file in svg_files {
            println!("  file://{}", svg_file.display());
        }
    } else {
        println!("=== DOT files created! ===");
        println!("\nTo visualize the graphs:");
        println!("1. Install Graphviz: https://graphviz.org/download/");
        println!("2. Run this example with --render flag:");
        println!("   cargo run --example dot_visualization -- --render");
        println!("\nOr manually convert individual files:");
        println!("   cd {}", output_dir.display());
        println!("   dot -Tpng example1_var.dot -o example1_var.png");
        println!("   dot -Tsvg example2_and.dot -o example2_and.svg");
        println!("   dot -Tpdf example3_or.dot -o example3_or.pdf");
    }

    Ok(())
}
