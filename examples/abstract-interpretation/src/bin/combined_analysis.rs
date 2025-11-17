//! Combined domain analysis example.
//!
//! This example demonstrates using multiple domains together:
//! - Sign, Constant, and Interval domains side-by-side
//! - How different domains provide complementary information
//! - Precision trade-offs

use abstract_interpretation::constant::{ConstValue, ConstantDomain};
use abstract_interpretation::expr::{NumExpr, NumPred};
use abstract_interpretation::interval::{Bound, Interval, IntervalDomain};
use abstract_interpretation::numeric::NumericDomain;
use abstract_interpretation::sign::{Sign, SignDomain, SignElement};

fn main() {
    println!("=== Combined Domain Analysis Examples ===\n");

    example_sign_constant_cooperation();
    example_sign_interval_cooperation();
    example_constant_interval_cooperation();
    example_triple_domain_analysis();
}

/// Example 1: Sign and Constant cooperation
fn example_sign_constant_cooperation() {
    println!("Example 1: Sign × Constant Domain");
    println!("----------------------------------");

    let sign_domain = SignDomain;
    let const_domain = ConstantDomain;

    println!("Program:");
    println!("  x = 0;");
    println!("  y = x + 5;");
    println!();

    // Sign analysis
    let sign_elem = sign_domain.constant(&"x".to_string(), 0);
    println!("Sign domain: x = {}", sign_elem.get("x"));

    let expr = NumExpr::Add(Box::new(NumExpr::Var("x".to_string())), Box::new(NumExpr::Const(5)));
    let sign_result = sign_domain.assign(&sign_elem, &"y".to_string(), &expr);
    println!("Sign domain: y = {} (0 + positive = positive)", sign_result.get("y"));

    // Constant analysis
    let const_elem = const_domain.constant(&"x".to_string(), 0);
    println!("\nConstant domain: x = {}", const_elem.get("x"));

    let const_result = const_domain.assign(&const_elem, &"y".to_string(), &expr);
    println!("Constant domain: y = {} (exact value!)", const_result.get("y"));

    println!("\n✓ Constant domain is more precise for this case");
    println!("  Sign: y is positive");
    println!("  Constant: y is exactly 5");

    println!("\n");
}

/// Example 2: Sign and Interval cooperation
fn example_sign_interval_cooperation() {
    println!("Example 2: Sign × Interval Domain");
    println!("----------------------------------");

    let sign_domain = SignDomain;
    let interval_domain = IntervalDomain;

    println!("Program:");
    println!("  x = input();  // x ∈ [-10, 10]");
    println!("  if (x > 0) {{");
    println!("    y = x * x;");
    println!("  }}");
    println!();

    // Initial interval
    let mut interval_elem = interval_domain.interval(&"x".to_string(), -10, 10);
    println!("Interval domain: x ∈ {}", interval_elem.get("x"));

    // Initial sign
    let mut sign_elem = SignElement::new();
    sign_elem.set("x".to_string(), Sign::Top);
    println!("Sign domain: x = {}", sign_elem.get("x"));

    // Assume x > 0
    let pred = NumPred::Gt(NumExpr::Var("x".to_string()), NumExpr::Const(0));

    interval_elem = interval_domain.assume(&interval_elem, &pred);
    sign_elem = sign_domain.assume(&sign_elem, &pred);

    println!("\nAfter 'x > 0':");
    println!("  Interval: x ∈ {}", interval_elem.get("x"));
    println!("  Sign: x = {}", sign_elem.get("x"));

    // y = x * x
    let expr = NumExpr::Mul(Box::new(NumExpr::Var("x".to_string())), Box::new(NumExpr::Var("x".to_string())));

    interval_elem = interval_domain.assign(&interval_elem, &"y".to_string(), &expr);
    sign_elem = sign_domain.assign(&sign_elem, &"y".to_string(), &expr);

    println!("\nAfter 'y = x * x':");
    println!("  Interval: y ∈ {} (precise bounds)", interval_elem.get("y"));
    println!("  Sign: y = {} (positive, but no bounds)", sign_elem.get("y"));

    println!("\n✓ Domains provide complementary information:");
    println!("  Interval: precise range [1, 100]");
    println!("  Sign: guaranteed positive");

    println!("\n");
}

/// Example 3: Constant and Interval cooperation
fn example_constant_interval_cooperation() {
    println!("Example 3: Constant × Interval Domain");
    println!("--------------------------------------");

    let const_domain = ConstantDomain;
    let interval_domain = IntervalDomain;

    println!("Program:");
    println!("  x = 5;");
    println!("  y = input();  // y ∈ [1, 10]");
    println!("  z = x + y;");
    println!();

    // Constant domain
    let mut const_elem = const_domain.constant(&"x".to_string(), 5);
    const_elem.set("y".to_string(), ConstValue::Top); // Unknown

    println!("Constant domain:");
    println!("  x = {}", const_elem.get("x"));
    println!("  y = {}", const_elem.get("y"));

    let expr = NumExpr::Add(Box::new(NumExpr::Var("x".to_string())), Box::new(NumExpr::Var("y".to_string())));
    const_elem = const_domain.assign(&const_elem, &"z".to_string(), &expr);
    println!("  z = x + y = {} (lost precision)", const_elem.get("z"));

    // Interval domain
    let mut interval_elem = interval_domain.interval(&"x".to_string(), 5, 5);
    interval_elem.set("y".to_string(), Interval::new(Bound::Finite(1), Bound::Finite(10)));

    println!("\nInterval domain:");
    println!("  x ∈ {}", interval_elem.get("x"));
    println!("  y ∈ {}", interval_elem.get("y"));

    interval_elem = interval_domain.assign(&interval_elem, &"z".to_string(), &expr);
    println!("  z = x + y ∈ {} (maintains bounds)", interval_elem.get("z"));

    println!("\n✓ Interval domain maintains useful bounds when constant is lost");
    println!("  z ∈ [6, 15]");

    println!("\n");
}

/// Example 4: Triple domain analysis (Sign + Constant + Interval)
fn example_triple_domain_analysis() {
    println!("Example 4: Sign + Constant + Interval Analysis");
    println!("-----------------------------------------------");

    let sign_domain = SignDomain;
    let const_domain = ConstantDomain;
    let interval_domain = IntervalDomain;

    println!("Program:");
    println!("  x = 5;");
    println!("  y = x * 2;");
    println!("  if (y > 0) {{");
    println!("    z = y - 3;");
    println!("  }}");
    println!();

    // Create initial elements with x = 5
    let mut sign_elem = sign_domain.constant(&"x".to_string(), 5);
    let mut const_elem = const_domain.constant(&"x".to_string(), 5);
    let mut interval_elem = interval_domain.interval(&"x".to_string(), 5, 5);

    println!("Initial state: x = 5");
    println!("  Sign: {}", sign_elem.get("x"));
    println!("  Constant: {}", const_elem.get("x"));
    println!("  Interval: {}", interval_elem.get("x"));

    // y = x * 2
    let expr = NumExpr::Mul(Box::new(NumExpr::Var("x".to_string())), Box::new(NumExpr::Const(2)));

    sign_elem = sign_domain.assign(&sign_elem, &"y".to_string(), &expr);
    const_elem = const_domain.assign(&const_elem, &"y".to_string(), &expr);
    interval_elem = interval_domain.assign(&interval_elem, &"y".to_string(), &expr);

    println!("\nAfter 'y = x * 2':");
    println!("  Sign: {}", sign_elem.get("y"));
    println!("  Constant: {}", const_elem.get("y"));
    println!("  Interval: {}", interval_elem.get("y"));

    // Assume y > 0 (redundant but demonstrates refinement)
    let pred = NumPred::Gt(NumExpr::Var("y".to_string()), NumExpr::Const(0));

    sign_elem = sign_domain.assume(&sign_elem, &pred);
    const_elem = const_domain.assume(&const_elem, &pred);
    interval_elem = interval_domain.assume(&interval_elem, &pred);

    println!("\nAfter 'y > 0' (all domains confirm y is positive/10):");
    println!("  Sign: {}", sign_elem.get("y"));
    println!("  Constant: {}", const_elem.get("y"));
    println!("  Interval: {}", interval_elem.get("y"));

    // z = y - 3
    let expr = NumExpr::Sub(Box::new(NumExpr::Var("y".to_string())), Box::new(NumExpr::Const(3)));

    sign_elem = sign_domain.assign(&sign_elem, &"z".to_string(), &expr);
    const_elem = const_domain.assign(&const_elem, &"z".to_string(), &expr);
    interval_elem = interval_domain.assign(&interval_elem, &"z".to_string(), &expr);

    println!("\nAfter 'z = y - 3':");
    println!("  Sign: {} (positive)", sign_elem.get("z"));
    println!("  Constant: {} (exact!)", const_elem.get("z"));
    println!("  Interval: {} (precise bound)", interval_elem.get("z"));

    println!("\n✓ Combined analysis provides maximum precision:");
    println!("  - Sign: z is positive");
    println!("  - Constant: z is exactly 7");
    println!("  - Interval: z ∈ [7, 7]");
    println!("  All domains agree and provide complementary views!");

    println!("\n");
}
