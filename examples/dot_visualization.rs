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
    let bdd = Bdd::default();

    // Create output directory in examples folder
    let output_dir = env::current_dir()?.join("examples").join("dot_output");
    fs::create_dir_all(&output_dir)?;

    println!("=== BDD to DOT Visualization Examples ===");
    println!("Output directory: {}\n", output_dir.display());

    // Example 1: Simple variable
    println!("Example 1: Single variable");
    let x = bdd.mk_var(1);
    let dot = bdd.to_dot(&[x])?;
    fs::write(output_dir.join("example1_var.dot"), &dot)?;
    println!("  Formula: x1\n");

    // Example 2: AND operation
    println!("Example 2: AND operation");
    let x1 = bdd.mk_var(1);
    let x2 = bdd.mk_var(2);
    let and = bdd.apply_and(x1, x2);
    let dot = bdd.to_dot(&[and])?;
    fs::write(output_dir.join("example2_and.dot"), &dot)?;
    println!("  Formula: x1 ∧ x2\n");

    // Example 3: OR operation
    println!("Example 3: OR operation");
    let or = bdd.apply_or(x1, x2);
    let dot = bdd.to_dot(&[or])?;
    fs::write(output_dir.join("example3_or.dot"), &dot)?;
    println!("  Formula: x1 ∨ x2\n");

    // Example 4: XOR operation
    println!("Example 4: XOR operation");
    let xor = bdd.apply_xor(x1, x2);
    let dot = bdd.to_dot(&[xor])?;
    fs::write(output_dir.join("example4_xor.dot"), &dot)?;
    println!("  Formula: x1 ⊕ x2\n");

    // Example 5: Complex formula
    println!("Example 5: Complex formula");
    let x3 = bdd.mk_var(3);
    let complex = bdd.apply_or(bdd.apply_and(x1, x2), bdd.apply_and(-x1, x3));
    let dot = bdd.to_dot(&[complex])?;
    fs::write(output_dir.join("example5_complex.dot"), &dot)?;
    println!("  Formula: (x1 ∧ x2) ∨ (¬x1 ∧ x3)\n");

    // Example 6: Multiple functions (shared nodes)
    println!("Example 6: Multiple functions with shared nodes");
    let dot = bdd.to_dot(&[and, or, xor])?;
    fs::write(output_dir.join("example6_multiple.dot"), &dot)?;
    println!("  Formulas: AND, OR, XOR of x1 and x2\n");

    // Example 7: Cube (conjunction of literals)
    println!("Example 7: Cube (conjunction of literals)");
    let cube = bdd.cube([-1, 2, -3]);
    let dot = bdd.to_dot(&[cube])?;
    fs::write(output_dir.join("example7_cube.dot"), &dot)?;
    println!("  Formula: ¬x1 ∧ x2 ∧ ¬x3\n");

    // Example 8: Custom configuration
    println!("Example 8: Custom visualization style");
    let config = DotConfig {
        node_shape: "ellipse",
        terminal_shape: "box",
        root_shape: "diamond",
        use_html_labels: true,
        ..DotConfig::default()
    };
    let dot = bdd.to_dot_with_config(&[complex], &config)?;
    fs::write(output_dir.join("example8_custom.dot"), &dot)?;
    println!("  Custom shapes and plain text labels\n");

    // Example 9: ITE (if-then-else)
    println!("Example 9: ITE operation");
    let x4 = bdd.mk_var(4);
    let ite = bdd.apply_ite(x1, x2, x4);
    let dot = bdd.to_dot(&[ite])?;
    fs::write(output_dir.join("example9_ite.dot"), &dot)?;
    println!("  Formula: ITE(x1, x2, x4) = (x1 → x2) ∧ (¬x1 → x4)\n");

    // Render images if requested
    if env::args().any(|arg| arg == "--render") {
        println!("\n=== Rendering images with Graphviz ===\n");

        let examples = [
            "example1_var",
            "example2_and",
            "example3_or",
            "example4_xor",
            "example5_complex",
            "example6_multiple",
            "example7_cube",
            "example8_custom",
            "example9_ite",
        ];

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
