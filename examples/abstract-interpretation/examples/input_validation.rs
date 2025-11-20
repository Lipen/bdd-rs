//! Input Validation Analysis Example.
//!
//! This example demonstrates:
//! 1. **String Length Domain**: Analyzing input validation logic based on string length.
//!    - Scenario: Validating that a password meets minimum length requirements.

use abstract_interpretation::*;

fn main() {
    println!("=== Input Validation Analysis ===");
    println!("This example demonstrates analyzing input validation logic using string length abstraction.");
    println!("Scenario: Validating that a password meets minimum length requirements.");

    println!("\nProgram being analyzed:");
    println!("  password = input();");
    println!("  assume(len(password) >= 0); // Implicit");
    println!("  if (len(password) >= 8) {{");
    println!("    // Valid password");
    println!("  }} else {{");
    println!("    // Invalid password");
    println!("  }}");

    let domain = StringLengthDomain::new();

    // 1. Initial state: password is unknown (Top)
    // In StringLengthDomain, Top means length is [0, +∞] (implicitly)
    // But IntervalDomain::top() is [-∞, +∞]. Lengths can't be negative.
    // So we should probably start with length >= 0.

    let mut state = domain.top();

    // Refine: length of password must be >= 0
    let non_neg = NumPred::Ge(NumExpr::Var("password".to_string()), NumExpr::Const(0));
    state = domain.assume_length(&state, &non_neg);
    println!("\nInitial State (after input):");
    println!("  len(password) = {}", domain.get_length(&state, "password"));

    // 2. Branch: if (len(password) >= 8)
    println!("\n--- Analyzing Branch: if (len(password) >= 8) ---");

    let cond = NumPred::Ge(NumExpr::Var("password".to_string()), NumExpr::Const(8));

    // True branch
    let true_branch = domain.assume_length(&state, &cond);
    println!("True Branch (Valid):");
    println!("  len(password) = {}", domain.get_length(&true_branch, "password"));

    // False branch (Negation of condition)
    let false_cond = NumPred::Not(Box::new(cond));
    let false_branch = domain.assume_length(&state, &false_cond);
    println!("False Branch (Invalid):");
    println!("  len(password) = {}", domain.get_length(&false_branch, "password"));

    // 3. Check properties
    println!("\n--- Verification Results ---");

    // In true branch, is length >= 8?
    let true_len = domain.get_length(&true_branch, "password");
    // We expect [8, +inf]
    assert_eq!(true_len.low, Bound::Finite(8), "Lower bound should be 8");
    assert_eq!(true_len.high, Bound::PosInf, "Upper bound should be infinite");
    println!("  ✓ Verified: Password length is at least 8 in valid branch.");

    // In false branch, is length < 8?
    let false_len = domain.get_length(&false_branch, "password");
    // We expect [0, 7]
    assert_eq!(false_len.low, Bound::Finite(0), "Lower bound should be 0");
    assert_eq!(false_len.high, Bound::Finite(7), "Upper bound should be 7");
    println!("  ✓ Verified: Password length is strictly less than 8 in invalid branch.");
}
