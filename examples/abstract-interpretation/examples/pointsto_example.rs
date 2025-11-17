//! Example demonstrating the Points-to domain for pointer analysis.
//!
//! This example shows how to use the BDD-based points-to domain to track
//! which memory locations pointers may point to during program execution.

use std::rc::Rc;

use abstract_interpretation::{
    AbstractDomain, Location, PointsToDomain, PointsToElement,
};

fn main() {
    println!("=== Points-to Analysis Examples ===\n");

    example_1_basic_assignment();
    example_2_pointer_copy();
    example_3_join_analysis();
    example_4_alias_detection();
}

/// Example 1: Basic pointer assignments
///
/// ```c
/// int x, y;
/// int *p, *q;
/// p = &x;  // p points to x
/// q = &y;  // q points to y
/// ```
fn example_1_basic_assignment() {
    println!("Example 1: Basic pointer assignment");
    println!("-----------------------------------");
    println!("Code:");
    println!("  int x, y;");
    println!("  int *p, *q;");
    println!("  p = &x;");
    println!("  q = &y;");
    println!();

    let domain = PointsToDomain::new();
    let mut elem = PointsToElement::new(Rc::clone(domain.manager()));

    // p = &x
    let x_loc = Location::Stack("x".to_string());
    elem = domain.assign_address(&elem, "p", &x_loc);

    // q = &y
    let y_loc = Location::Stack("y".to_string());
    elem = domain.assign_address(&elem, "q", &y_loc);

    println!("Analysis results:");
    println!("  p points-to: {}", format_points_to(&domain, &elem, "p"));
    println!("  q points-to: {}", format_points_to(&domain, &elem, "q"));
    println!();
}

/// Example 2: Pointer copy
///
/// ```c
/// int x;
/// int *p, *q;
/// p = &x;
/// q = p;   // q now points to same location as p
/// ```
fn example_2_pointer_copy() {
    println!("Example 2: Pointer copy");
    println!("-----------------------");
    println!("Code:");
    println!("  int x;");
    println!("  int *p, *q;");
    println!("  p = &x;");
    println!("  q = p;");
    println!();

    let domain = PointsToDomain::new();
    let mut elem = PointsToElement::new(Rc::clone(domain.manager()));

    // p = &x
    let x_loc = Location::Stack("x".to_string());
    elem = domain.assign_address(&elem, "p", &x_loc);

    // q = p
    elem = domain.assign_copy(&elem, "q", "p");

    println!("Analysis results:");
    println!("  p points-to: {}", format_points_to(&domain, &elem, "p"));
    println!("  q points-to: {}", format_points_to(&domain, &elem, "q"));
    println!("  May-alias(p, q): {}", elem.may_alias(&domain, "p", "q"));
    println!("  Must-alias(p, q): {}", elem.must_alias(&domain, "p", "q"));
    println!();
}

/// Example 3: Join analysis (control flow merge)
///
/// ```c
/// int x, y;
/// int *p;
/// if (condition) {
///     p = &x;
/// } else {
///     p = &y;
/// }
/// // Here: p may point to x or y
/// ```
fn example_3_join_analysis() {
    println!("Example 3: Join analysis (if-else merge)");
    println!("-----------------------------------------");
    println!("Code:");
    println!("  int x, y;");
    println!("  int *p;");
    println!("  if (condition) {{");
    println!("      p = &x;");
    println!("  }} else {{");
    println!("      p = &y;");
    println!("  }}");
    println!("  // After merge: p may point to x or y");
    println!();

    let domain = PointsToDomain::new();
    let init = PointsToElement::new(Rc::clone(domain.manager()));

    // Then branch: p = &x
    let x_loc = Location::Stack("x".to_string());
    let then_elem = domain.assign_address(&init, "p", &x_loc);

    // Else branch: p = &y
    let y_loc = Location::Stack("y".to_string());
    let else_elem = domain.assign_address(&init, "p", &y_loc);

    // Join at merge point
    let joined = domain.join(&then_elem, &else_elem);

    println!("Analysis results:");
    println!("  Then branch - p points-to: {}", format_points_to(&domain, &then_elem, "p"));
    println!("  Else branch - p points-to: {}", format_points_to(&domain, &else_elem, "p"));
    println!("  After merge - p points-to: {}", format_points_to(&domain, &joined, "p"));
    println!();
}

/// Example 4: Alias detection
///
/// ```c
/// int x, y;
/// int *p, *q, *r;
/// p = &x;
/// q = &x;  // p and q are aliases (both point to x)
/// r = &y;  // r points to different location
/// ```
fn example_4_alias_detection() {
    println!("Example 4: Alias detection");
    println!("--------------------------");
    println!("Code:");
    println!("  int x, y;");
    println!("  int *p, *q, *r;");
    println!("  p = &x;");
    println!("  q = &x;  // alias");
    println!("  r = &y;  // no alias");
    println!();

    let domain = PointsToDomain::new();
    let mut elem = PointsToElement::new(Rc::clone(domain.manager()));

    let x_loc = Location::Stack("x".to_string());
    let y_loc = Location::Stack("y".to_string());

    // p = &x
    elem = domain.assign_address(&elem, "p", &x_loc);

    // q = &x
    elem = domain.assign_address(&elem, "q", &x_loc);

    // r = &y
    elem = domain.assign_address(&elem, "r", &y_loc);

    println!("Analysis results:");
    println!("  p points-to: {}", format_points_to(&domain, &elem, "p"));
    println!("  q points-to: {}", format_points_to(&domain, &elem, "q"));
    println!("  r points-to: {}", format_points_to(&domain, &elem, "r"));
    println!();
    println!("  May-alias(p, q): {} (both can point to x)", elem.may_alias(&domain, "p", "q"));
    println!("  Must-alias(p, q): {} (both always point to x)", elem.must_alias(&domain, "p", "q"));
    println!("  May-alias(p, r): {} (point to different locations)", elem.may_alias(&domain, "p", "r"));
    println!("  Must-alias(p, r): {} (point to different locations)", elem.must_alias(&domain, "p", "r"));
    println!();
}

/// Format the points-to set for a variable
fn format_points_to(domain: &PointsToDomain, elem: &PointsToElement, var: &str) -> String {
    let bdd = elem.get(var);
    let locs = domain.decode_bdd(bdd);

    if locs.is_empty() {
        return "∅ (empty)".to_string();
    }

    let loc_strs: Vec<String> = locs.iter().map(|l| l.to_string()).collect();
    format!("{{{}}}", loc_strs.join(", "))
}
