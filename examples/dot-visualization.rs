//! BDD to DOT visualization examples.
//!
//! This example demonstrates how to export BDDs to GraphViz DOT format
//! and shows how variable ordering dramatically affects BDD size.
//!
//! Run with:
//!   cargo run --example dot-visualization
//!   cargo run --example dot-visualization -- --render  # Also render to PNG/SVG/PDF

use std::env;
use std::fs;
use std::process::Command;

use bdd_rs::bdd::Bdd;

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let output_dir = env::current_dir()?.join("examples").join("dot_output");
    fs::create_dir_all(&output_dir)?;

    println!("=== BDD to DOT Visualization Examples ===");
    println!("Output directory: {}\n", output_dir.display());

    let mut examples = Vec::new();

    // ========================================================================
    // Basic Operations
    // ========================================================================

    // Example: Single variable
    {
        let name = "01_variable";
        let bdd = Bdd::default();
        let x = bdd.mk_var(1);
        println!("Example: {}", name);
        println!("  Formula: x₁");
        println!("  Size: {} nodes\n", bdd.size(x));
        fs::write(output_dir.join(format!("{}.dot", name)), bdd.to_dot(&[x])?)?;
        examples.push(name);
    }

    // Example: AND, OR, XOR
    {
        let name = "02_basic_ops";
        let bdd = Bdd::default();
        let x1 = bdd.mk_var(1);
        let x2 = bdd.mk_var(2);
        let and = bdd.apply_and(x1, x2);
        let or = bdd.apply_or(x1, x2);
        let xor = bdd.apply_xor(x1, x2);
        println!("Example: {}", name);
        println!("  Formulas: x₁∧x₂, x₁∨x₂, x₁⊕x₂");
        println!("  Sizes: AND={}, OR={}, XOR={}\n", bdd.size(and), bdd.size(or), bdd.size(xor));
        fs::write(output_dir.join(format!("{}.dot", name)), bdd.to_dot(&[and, or, xor])?)?;
        examples.push(name);
    }

    // ========================================================================
    // Variable Ordering Impact: Interleaved Addition
    // ========================================================================
    //
    // Function: (a₁ ↔ b₁) ∧ (a₂ ↔ b₂) ∧ (a₃ ↔ b₃) ∧ (a₄ ↔ b₄)
    //
    // This function checks if two 4-bit numbers are equal.
    // With GOOD ordering (a₁,b₁,a₂,b₂,...): O(n) nodes - linear!
    // With BAD ordering (a₁,a₂,a₃,a₄,b₁,b₂,...): O(2ⁿ) nodes - exponential!

    println!("=== Variable Ordering Impact: Bit Equality ===\n");

    // Good ordering: interleaved (a₁,b₁,a₂,b₂,a₃,b₃,a₄,b₄)
    {
        let name = "03_equality_good_order";
        let bdd = Bdd::default();

        // Pre-allocate variables in GOOD order: a₁,b₁,a₂,b₂,a₃,b₃,a₄,b₄
        let a1 = bdd.mk_var(1); // level 0
        let b1 = bdd.mk_var(5); // level 1
        let a2 = bdd.mk_var(2); // level 2
        let b2 = bdd.mk_var(6); // level 3
        let a3 = bdd.mk_var(3); // level 4
        let b3 = bdd.mk_var(7); // level 5
        let a4 = bdd.mk_var(4); // level 6
        let b4 = bdd.mk_var(8); // level 7

        // Build: (a₁↔b₁) ∧ (a₂↔b₂) ∧ (a₃↔b₃) ∧ (a₄↔b₄)
        let eq1 = bdd.apply_eq(a1, b1);
        let eq2 = bdd.apply_eq(a2, b2);
        let eq3 = bdd.apply_eq(a3, b3);
        let eq4 = bdd.apply_eq(a4, b4);
        let result = bdd.apply_and(bdd.apply_and(eq1, eq2), bdd.apply_and(eq3, eq4));

        println!("Example: {} (GOOD ordering)", name);
        println!("  Formula: (a₁↔b₁) ∧ (a₂↔b₂) ∧ (a₃↔b₃) ∧ (a₄↔b₄)");
        println!("  Order: a₁,b₁,a₂,b₂,a₃,b₃,a₄,b₄ (interleaved)");
        println!("  Size: {} nodes ← LINEAR!\n", bdd.size(result));
        fs::write(output_dir.join(format!("{}.dot", name)), bdd.to_dot(&[result])?)?;
        examples.push(name);
    }

    // Bad ordering: grouped (a₁,a₂,a₃,a₄,b₁,b₂,b₃,b₄)
    {
        let name = "04_equality_bad_order";
        let bdd = Bdd::default();

        // Pre-allocate variables in BAD order: a₁,a₂,a₃,a₄,b₁,b₂,b₃,b₄
        let a1 = bdd.mk_var(1); // level 0
        let a2 = bdd.mk_var(2); // level 1
        let a3 = bdd.mk_var(3); // level 2
        let a4 = bdd.mk_var(4); // level 3
        let b1 = bdd.mk_var(5); // level 4
        let b2 = bdd.mk_var(6); // level 5
        let b3 = bdd.mk_var(7); // level 6
        let b4 = bdd.mk_var(8); // level 7

        // Build: (a₁↔b₁) ∧ (a₂↔b₂) ∧ (a₃↔b₃) ∧ (a₄↔b₄)
        let eq1 = bdd.apply_eq(a1, b1);
        let eq2 = bdd.apply_eq(a2, b2);
        let eq3 = bdd.apply_eq(a3, b3);
        let eq4 = bdd.apply_eq(a4, b4);
        let result = bdd.apply_and(bdd.apply_and(eq1, eq2), bdd.apply_and(eq3, eq4));

        println!("Example: {} (BAD ordering)", name);
        println!("  Formula: (a₁↔b₁) ∧ (a₂↔b₂) ∧ (a₃↔b₃) ∧ (a₄↔b₄)");
        println!("  Order: a₁,a₂,a₃,a₄,b₁,b₂,b₃,b₄ (grouped)");
        println!("  Size: {} nodes ← EXPONENTIAL!\n", bdd.size(result));
        fs::write(output_dir.join(format!("{}.dot", name)), bdd.to_dot(&[result])?)?;
        examples.push(name);
    }

    // ========================================================================
    // Variable Ordering Impact: Addition Carry Chain
    // ========================================================================
    //
    // Function: x₁⊕y₁⊕x₂⊕y₂⊕x₃⊕y₃ (simplified carry propagation pattern)
    //
    // Good ordering keeps related variables together.

    println!("=== Variable Ordering Impact: XOR Chain ===\n");

    // Good ordering for XOR chain
    {
        let name = "05_xor_chain_good";
        let bdd = Bdd::default();

        // Interleaved order
        let x1 = bdd.mk_var(1);
        let y1 = bdd.mk_var(4);
        let x2 = bdd.mk_var(2);
        let y2 = bdd.mk_var(5);
        let x3 = bdd.mk_var(3);
        let y3 = bdd.mk_var(6);

        let result = bdd.apply_xor(bdd.apply_xor(bdd.apply_xor(x1, y1), bdd.apply_xor(x2, y2)), bdd.apply_xor(x3, y3));

        println!("Example: {} (GOOD ordering)", name);
        println!("  Formula: x₁⊕y₁⊕x₂⊕y₂⊕x₃⊕y₃");
        println!("  Order: x₁,y₁,x₂,y₂,x₃,y₃");
        println!("  Size: {} nodes\n", bdd.size(result));
        fs::write(output_dir.join(format!("{}.dot", name)), bdd.to_dot(&[result])?)?;
        examples.push(name);
    }

    // Bad ordering for XOR chain
    {
        let name = "06_xor_chain_bad";
        let bdd = Bdd::default();

        // Grouped order
        let x1 = bdd.mk_var(1);
        let x2 = bdd.mk_var(2);
        let x3 = bdd.mk_var(3);
        let y1 = bdd.mk_var(4);
        let y2 = bdd.mk_var(5);
        let y3 = bdd.mk_var(6);

        let result = bdd.apply_xor(bdd.apply_xor(bdd.apply_xor(x1, y1), bdd.apply_xor(x2, y2)), bdd.apply_xor(x3, y3));

        println!("Example: {} (BAD ordering)", name);
        println!("  Formula: x₁⊕y₁⊕x₂⊕y₂⊕x₃⊕y₃");
        println!("  Order: x₁,x₂,x₃,y₁,y₂,y₃");
        println!("  Size: {} nodes\n", bdd.size(result));
        fs::write(output_dir.join(format!("{}.dot", name)), bdd.to_dot(&[result])?)?;
        examples.push(name);
    }

    // ========================================================================
    // Additional Examples
    // ========================================================================

    // ITE operation
    {
        let name = "07_ite";
        let bdd = Bdd::default();
        let c = bdd.mk_var(1);
        let t = bdd.mk_var(2);
        let e = bdd.mk_var(3);
        let ite = bdd.apply_ite(c, t, e);
        println!("Example: {}", name);
        println!("  Formula: ITE(c, t, e) = (c ∧ t) ∨ (¬c ∧ e)");
        println!("  Size: {} nodes\n", bdd.size(ite));
        fs::write(output_dir.join(format!("{}.dot", name)), bdd.to_dot(&[ite])?)?;
        examples.push(name);
    }

    // Cube (conjunction of literals)
    {
        let name = "08_cube";
        let bdd = Bdd::default();
        let cube = bdd.mk_cube([-1, 2, -3, 4]);
        println!("Example: {}", name);
        println!("  Formula: ¬x₁ ∧ x₂ ∧ ¬x₃ ∧ x₄");
        println!("  Size: {} nodes\n", bdd.size(cube));
        fs::write(output_dir.join(format!("{}.dot", name)), bdd.to_dot(&[cube])?)?;
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
        println!("Or manually: dot -Tsvg {}/01_variable.dot -o out.svg", output_dir.display());
    }

    Ok(())
}
