//! File I/O for SDDs and Vtrees
//!
//! Demonstrates saving and loading SDDs and Vtrees in libsdd format.
//! This enables:
//!   - Persistence of compiled SDDs
//!   - Sharing between different runs or programs
//!   - Interoperability with UCLA's libsdd
//!
//! Run with: `cargo run --example file_io`

use std::fs;

use ananke_sdd::vtree::Vtree;
use ananke_sdd::SddManager;

fn main() {
    println!("─── SDD and Vtree File I/O ───\n");

    vtree_io_demo();
    sdd_io_demo();
    format_explanation();
    roundtrip_verification();
}

/// Demonstrate saving and loading Vtrees
fn vtree_io_demo() {
    println!("── Vtree File I/O ──\n");

    // Create a balanced vtree for 4 variables
    let vtree = Vtree::balanced(4);

    println!("Original vtree (balanced, 4 variables):");
    print_vtree_structure(&vtree);
    println!();

    // Save to file
    let vtree_path = "/tmp/example.vtree";
    match vtree.save(vtree_path) {
        Ok(()) => println!("Saved vtree to: {}", vtree_path),
        Err(e) => println!("Error saving vtree: {}", e),
    }
    println!();

    // Show the file contents
    println!("Vtree file contents:");
    println!("────────────────────");
    if let Ok(content) = fs::read_to_string(vtree_path) {
        for line in content.lines() {
            println!("  {}", line);
        }
    }
    println!();

    // Load from file
    println!("Loading vtree from file...");
    match Vtree::load(vtree_path) {
        Ok(loaded) => {
            println!("Loaded vtree:");
            print_vtree_structure(&loaded);
        }
        Err(e) => println!("Error loading vtree: {}", e),
    }
    println!();
}

/// Demonstrate saving and loading SDDs
fn sdd_io_demo() {
    println!("── SDD File I/O ──\n");

    // Create an SDD
    let mgr = SddManager::new(4);
    let a = mgr.var(1);
    let b = mgr.var(2);
    let c = mgr.var(3);
    let d = mgr.var(4);

    // (A ∧ B) ∨ (C ∧ D)
    let ab = mgr.and(a, b);
    let cd = mgr.and(c, d);
    let f = mgr.or(ab, cd);

    println!("Original SDD: (A ∧ B) ∨ (C ∧ D)");
    println!("  Variables: 4");
    println!("  Size: {} nodes", mgr.size(f));
    println!("  Model count: {}", mgr.model_count(f));
    println!();

    // Save SDD to file
    let sdd_path = "/tmp/example.sdd";
    match mgr.save_sdd(f, sdd_path) {
        Ok(()) => println!("Saved SDD to: {}", sdd_path),
        Err(e) => println!("Error saving SDD: {}", e),
    }
    println!();

    // Show the file contents
    println!("SDD file contents:");
    println!("──────────────────");
    if let Ok(content) = fs::read_to_string(sdd_path) {
        for line in content.lines() {
            println!("  {}", line);
        }
    }
    println!();

    // Also save the corresponding vtree
    let vtree_path2 = "/tmp/example_sdd.vtree";
    mgr.vtree().save(vtree_path2).unwrap();
    println!("Saved corresponding vtree to: {}", vtree_path2);
    println!();
}

/// Explain the file formats
fn format_explanation() {
    println!("── File Format Reference ──\n");

    println!("Vtree Format (.vtree):");
    println!("──────────────────────");
    println!("  vtree <node_count>           Header");
    println!("  L <id> <var>                 Leaf node (variable)");
    println!("  I <id> <left> <right>        Internal node");
    println!();
    println!("  Nodes appear bottom-up (children before parents)");
    println!("  IDs are in-order positions (0-indexed)");
    println!("  Variables are 1-indexed");
    println!();

    println!("SDD Format (.sdd):");
    println!("──────────────────");
    println!("  sdd <node_count>             Header");
    println!("  F <id>                       False terminal");
    println!("  T <id>                       True terminal");
    println!("  L <id> <vtree_id> <lit>      Literal node");
    println!("  D <id> <vtree_id> <n> {{p s}}* Decision node");
    println!();
    println!("  Nodes appear bottom-up (children before parents)");
    println!("  Literals: positive = var, negative = -var");
    println!("  Decision: n elements, each with prime p and sub s");
    println!();

    println!("Example Decision Node:");
    println!("  D 5 2 2 1 3 4 0    Node 5 at vtree 2:");
    println!("                     2 elements: (prime=1, sub=3), (prime=4, sub=0)");
    println!();
}

/// Verify roundtrip preservation
fn roundtrip_verification() {
    println!("── Roundtrip Verification ──\n");

    println!("Testing that save/load preserves semantics...\n");

    // Create an SDD
    let mgr = SddManager::new(4);
    let a = mgr.var(1);
    let b = mgr.var(2);
    let c = mgr.var(3);

    // A ⊕ B ⊕ C (parity function)
    let xor_ab = mgr.xor(a, b);
    let f = mgr.xor(xor_ab, c);

    let original_count = mgr.model_count(f);
    let original_size = mgr.size(f);

    println!("Original SDD (A ⊕ B ⊕ C):");
    println!("  Model count: {}", original_count);
    println!("  Size: {} nodes", original_size);
    println!();

    // Save
    let sdd_path = "/tmp/parity.sdd";
    let vtree_path = "/tmp/parity.vtree";
    mgr.save_sdd(f, sdd_path).unwrap();
    mgr.vtree().save(vtree_path).unwrap();

    // Load into new manager
    println!("Loading into new manager...");
    let loaded_vtree = Vtree::load(vtree_path).unwrap();
    let mgr2 = SddManager::with_vtree(loaded_vtree);
    let f2 = mgr2.load_sdd(sdd_path).unwrap();

    let loaded_count = mgr2.model_count(f2);
    let loaded_size = mgr2.size(f2);

    println!("Loaded SDD:");
    println!("  Model count: {}", loaded_count);
    println!("  Size: {} nodes", loaded_size);
    println!();

    // Verify
    let count_match = original_count == loaded_count;
    let size_match = original_size == loaded_size;

    println!("Verification:");
    println!(
        "  Model count preserved: {} {}",
        original_count == loaded_count,
        if count_match { "✓" } else { "✗" }
    );
    println!(
        "  Size preserved: {} {}",
        original_size == loaded_size,
        if size_match { "✓" } else { "✗" }
    );
    println!();

    // Additional test: verify truth table matches
    println!("Truth table verification:");
    let mut matches = 0;
    let total = 8; // 2^3 for variables 1,2,3

    for bits in 0..8u8 {
        let a_val = (bits >> 0) & 1 == 1;
        let b_val = (bits >> 1) & 1 == 1;
        let c_val = (bits >> 2) & 1 == 1;

        // Evaluate original
        let mut cond1 = f;
        cond1 = mgr.condition(cond1, if a_val { 1 } else { -1 });
        cond1 = mgr.condition(cond1, if b_val { 2 } else { -2 });
        cond1 = mgr.condition(cond1, if c_val { 3 } else { -3 });
        let orig_result = mgr.is_true(cond1);

        // Evaluate loaded
        let mut cond2 = f2;
        cond2 = mgr2.condition(cond2, if a_val { 1 } else { -1 });
        cond2 = mgr2.condition(cond2, if b_val { 2 } else { -2 });
        cond2 = mgr2.condition(cond2, if c_val { 3 } else { -3 });
        let load_result = mgr2.is_true(cond2);

        if orig_result == load_result {
            matches += 1;
        }
    }

    println!(
        "  Matching entries: {}/{} {}",
        matches,
        total,
        if matches == total { "✓" } else { "✗" }
    );
    println!();

    // Summary
    println!("─── Summary ───\n");
    println!("File I/O operations:");
    println!("  • vtree.save(path)       Save vtree to file");
    println!("  • Vtree::load(path)      Load vtree from file");
    println!("  • mgr.save_sdd(f, path)  Save SDD to file");
    println!("  • mgr.load_sdd(path)     Load SDD from file");
    println!();
    println!("String operations:");
    println!("  • vtree.to_vtree_string()    Convert to string");
    println!("  • Vtree::from_vtree_string() Parse from string");
    println!("  • mgr.sdd_to_string(f)       Convert to string");
    println!();
    println!("Tips:");
    println!("  • Always save vtree alongside SDD");
    println!("  • Load vtree first, then create manager");
    println!("  • Format is compatible with UCLA libsdd");
    println!();
    println!("Done.");
}

/// Helper to print vtree structure
fn print_vtree_structure(vtree: &Vtree) {
    println!("  Number of variables: {}", vtree.num_vars());
    println!("  Number of nodes: {}", vtree.num_nodes());
}
