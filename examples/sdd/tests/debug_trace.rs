//! Debug test for tracing SDD operations.
//!
//! Run with: RUST_LOG=debug cargo test test_debug_trace -- --nocapture

use sdd::SddManager;

fn init_logging() {
    let _ = env_logger::builder().is_test(true).filter_level(log::LevelFilter::Debug).try_init();
}

#[test]
fn test_debug_trace_xor() {
    init_logging();

    println!("\n=== Testing XOR ===");
    let mgr = SddManager::new(2);
    let x1 = mgr.var(1);

    println!("Computing x1 XOR x1 (should be FALSE)...");
    let result = mgr.xor(x1, x1);
    println!("Result: {:?}, is_false: {}", result, mgr.is_false(result));

    println!("\nComputing x1 XOR FALSE (should be x1)...");
    let result2 = mgr.xor(x1, mgr.false_sdd());
    println!("Result: {:?}", result2);

    println!("\nComputing x1 XOR TRUE (should be NOT x1)...");
    let result3 = mgr.xor(x1, mgr.true_sdd());
    println!("Result: {:?}", result3);
}

#[test]
fn test_debug_trace_simple_and() {
    init_logging();

    println!("\n=== Testing simple AND ===");
    let mgr = SddManager::new(2);
    let x = mgr.var(1);
    let y = mgr.var(2);

    println!("Vtree structure:");
    let vtree = mgr.vtree();
    for v in 1..=2 {
        let vt = vtree.var_vtree(v);
        println!("  Variable {} is at vtree node {:?}, position {}", v, vt, vtree.position(vt));
    }
    println!("  Root: {:?}, position {}", vtree.root(), vtree.position(vtree.root()));

    println!("\nComputing x AND y...");
    let result = mgr.and(x, y);
    println!("Result: {:?}", result);
    println!("Display: {}", mgr.display(result));
}

#[test]
fn test_debug_trace_simple_or() {
    init_logging();

    println!("\n=== Testing simple OR ===");
    let mgr = SddManager::new(2);
    let x = mgr.var(1);
    let y = mgr.var(2);

    println!("Computing x OR y...");
    let result = mgr.or(x, y);
    println!("Result: {:?}", result);
}

#[test]
fn test_debug_trace_negation() {
    init_logging();

    println!("\n=== Testing negation in AND ===");
    let mgr = SddManager::new(2);
    let x = mgr.var(1);

    println!("Computing x AND (NOT x)...");
    let result = mgr.and(x, mgr.neg(x));
    println!("Result: {:?}", result);
    assert!(mgr.is_false(result));
}

#[test]
fn test_debug_trace_ite() {
    init_logging();

    println!("\n=== Testing ITE ===");
    let mgr = SddManager::new(3);
    let x1 = mgr.var(1);
    let x2 = mgr.var(2);
    let x3 = mgr.var(3);

    println!("x1 = {:?}", x1);
    println!("x2 = {:?}", x2);
    println!("x3 = {:?}", x3);

    println!("\nComputing ITE(TRUE, x2, x3)...");
    let result1 = mgr.ite(mgr.true_sdd(), x2, x3);
    println!("Result: {:?}", result1);
    assert_eq!(result1, x2);

    println!("\nComputing ITE(FALSE, x2, x3)...");
    let result2 = mgr.ite(mgr.false_sdd(), x2, x3);
    println!("Result: {:?}", result2);
    assert_eq!(result2, x3);

    println!("\nComputing ITE(x1, x2, x2)...");
    let result3 = mgr.ite(x1, x2, x2);
    println!("Result: {:?}", result3);
    assert_eq!(result3, x2);
}

#[test]
fn test_debug_trace_de_morgan_step_by_step() {
    init_logging();

    println!("\n=== Testing De Morgan step by step ===");
    let mgr = SddManager::new(3);

    // Print vtree structure
    println!("\nVtree structure:");
    let vtree = mgr.vtree();
    for v in 1..=3 {
        let vt = vtree.var_vtree(v);
        println!("  Variable {} is at vtree node {:?}", v, vt);
    }

    let x = mgr.var(1);
    let y = mgr.var(2);

    println!("\nStep 1: Computing x AND y...");
    let x_and_y = mgr.and(x, y);
    println!("x AND y = {:?}", x_and_y);
    println!("  Display: {}", mgr.display(x_and_y));

    println!("\nStep 2: Computing NOT(x AND y)...");
    let not_x_and_y = mgr.neg(x_and_y);
    println!("NOT(x AND y) = {:?}", not_x_and_y);
    println!("  Display: {}", mgr.display(not_x_and_y));

    println!("\nStep 3: Computing NOT x...");
    let not_x = mgr.neg(x);
    println!("NOT x = {:?}", not_x);

    println!("\nStep 4: Computing NOT y...");
    let not_y = mgr.neg(y);
    println!("NOT y = {:?}", not_y);

    println!("\nStep 5: Computing (NOT x) OR (NOT y)...");
    let not_x_or_not_y = mgr.or(not_x, not_y);
    println!("(NOT x) OR (NOT y) = {:?}", not_x_or_not_y);
    println!("  Display: {}", mgr.display(not_x_or_not_y));

    println!("\nComparing model counts...");
    let lhs_count = mgr.model_count(not_x_and_y);
    let rhs_count = mgr.model_count(not_x_or_not_y);
    println!("LHS model count: {}", lhs_count);
    println!("RHS model count: {}", rhs_count);

    assert_eq!(lhs_count, rhs_count, "De Morgan's law should hold!");
}
