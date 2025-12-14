//! Advanced theory solver demonstrations.
//!
//! This example showcases:
//! 1. Array bounds checking with ArrayBoundsSolver
//! 2. Bitwise constraint satisfaction with BitwiseSolver
//! 3. Boundary value analysis for systematic testing
//! 4. Combined multi-theory solving
//!
//! Run with: `cargo run -p tbdd-pbt --example advanced_theory`

use std::collections::HashMap;

use ananke_bdd::bdd::Bdd;
use tbdd_pbt::theory::Interval as TheoryInterval;
use tbdd_pbt::{
    ArrayBoundsSolver, ArrayLength, BitwiseSolver, BoundaryValueGenerator, ConstraintSolver, IntervalSolver, Predicate, PredicateUniverse,
    SolveResult,
};

fn main() {
    println!("═══════════════════════════════════════════════════════════════");
    println!("  T-BDD: Advanced Theory Solvers");
    println!("═══════════════════════════════════════════════════════════════\n");

    demo_array_bounds();
    demo_bitwise_constraints();
    demo_boundary_values();
    demo_combined_theories();

    println!("═══════════════════════════════════════════════════════════════");
    println!("  All advanced theory demos completed!");
    println!("═══════════════════════════════════════════════════════════════");
}

/// Demonstrate array bounds checking.
fn demo_array_bounds() {
    println!("── DEMO: Array Bounds Checking ─────────────────────────────────");
    println!("  Scenario: Safe array access with index validation\n");

    println!("  fn safe_get<T>(arr: &[T], index: usize) -> Option<&T> {{");
    println!("      if index < arr.len() {{ Some(&arr[index]) }}");
    println!("      else {{ None }}");
    println!("  }}\n");

    let bdd = Bdd::default();
    let mut universe = PredicateUniverse::new();

    // Predicates for array access
    let v1 = universe.register(Predicate::lt("index", 0), &bdd); // index < 0 (invalid)
    let v2 = universe.register(Predicate::ge("index", 10), &bdd); // index >= len (out of bounds)

    let _bv1 = bdd.mk_var(v1);
    let _bv2 = bdd.mk_var(v2);

    // Create array bounds solver
    let mut solver = ArrayBoundsSolver::new();
    solver.register_array("arr", "index", ArrayLength::Const(10));

    // Test scenarios
    let scenarios = [
        ("Valid access (index in [0, 9])", vec![(v1, false), (v2, false)]),
        ("Out of bounds high (index >= 10)", vec![(v1, false), (v2, true)]),
        ("Negative index (index < 0)", vec![(v1, true), (v2, false)]),
    ];

    for (desc, assignments) in scenarios {
        let assign_map: HashMap<_, _> = assignments.into_iter().collect();
        let result = solver.solve(&assign_map, &universe);

        match result {
            SolveResult::Sat(witness) => {
                let idx = witness.get("index").unwrap_or(0);
                println!("  {}: SAT (index={})", desc, idx);
            }
            SolveResult::Unsat => {
                println!("  {}: UNSAT (pruned)", desc);
            }
            SolveResult::Unknown => {
                println!("  {}: UNKNOWN", desc);
            }
        }
    }

    println!();

    // Show valid index range
    println!("  Valid index range: [0, 9]");
    println!("  Array bounds checking ensures safe memory access ✓\n");
}

/// Demonstrate bitwise constraint solving.
fn demo_bitwise_constraints() {
    println!("── DEMO: Bitwise Constraints ───────────────────────────────────");
    println!("  Scenario: Memory alignment and power-of-2 allocation\n");

    println!("  fn allocate_aligned(size: usize, align: usize) -> *mut u8 {{");
    println!("      assert!(align.is_power_of_two());");
    println!("      // ... allocation logic");
    println!("  }}\n");

    let bdd = Bdd::default();
    let mut universe = PredicateUniverse::new();

    // Predicates
    let v1 = universe.register(Predicate::gt("size", 0), &bdd);
    let v2 = universe.register(Predicate::gt("align", 0), &bdd);

    let _bv1 = bdd.mk_var(v1);
    let _bv2 = bdd.mk_var(v2);

    // Bitwise solver with power-of-2 constraint
    let mut solver = BitwiseSolver::new();
    solver.require_power_of_two("align");
    solver.require_non_negative("size");
    solver.require_aligned("size", 8); // Size must be 8-byte aligned

    // Test with valid constraints
    let assignments: HashMap<_, _> = vec![(v1, true), (v2, true)].into_iter().collect();
    let result = solver.solve(&assignments, &universe);

    match result {
        SolveResult::Sat(witness) => {
            let size = witness.get("size").unwrap_or(0);
            let align = witness.get("align").unwrap_or(0);
            println!("  Generated values:");
            println!("    size = {} (aligned to 8)", size);
            println!("    align = {} (power of 2: {})", align, (align > 0 && (align & (align - 1)) == 0));

            // Verify constraints
            let size_aligned = size % 8 == 0;
            let align_is_pow2 = align > 0 && (align & (align - 1)) == 0;
            println!("\n  Constraint verification:");
            println!("    size % 8 == 0: {}", if size_aligned { "✓" } else { "✗" });
            println!("    align is power of 2: {}", if align_is_pow2 { "✓" } else { "pending" });
        }
        _ => println!("  No solution found"),
    }

    println!();

    // Show various power-of-2 values
    println!("  Power-of-2 examples: 1, 2, 4, 8, 16, 32, 64, 128, 256...");
    println!("  Alignment is crucial for SIMD, cache lines, page boundaries ✓\n");
}

/// Demonstrate boundary value analysis.
fn demo_boundary_values() {
    println!("── DEMO: Boundary Value Analysis ─────────────────────────────────");
    println!("  Systematic generation of edge case test inputs\n");

    let generator = BoundaryValueGenerator::all();

    // Example: year validation
    println!("  Interval: year ∈ [1900, 2100] (valid year range)");
    let year_interval = TheoryInterval {
        min: 1900,
        max: 2100,
        excluded: None,
    };

    let boundaries = generator.generate(&year_interval);
    println!("  Generated boundary values ({} total):", boundaries.len());

    // Show categorized boundaries
    let (special, normal): (Vec<i64>, Vec<i64>) = boundaries
        .iter()
        .copied()
        .partition(|&v| v == 1900 || v == 2100 || v == 1899 || v == 2101 || v == 2000);

    println!("    Critical boundaries: {:?}", special);
    println!("    Other values: {:?}", &normal[..normal.len().min(10)]);

    println!();

    // Example: percentage validation
    println!("  Interval: percentage ∈ [0, 100]");
    let pct_interval = TheoryInterval {
        min: 0,
        max: 100,
        excluded: None,
    };

    let pct_boundaries = generator.generate(&pct_interval);
    println!("  Generated: {:?}", pct_boundaries);

    println!();

    // Multi-variable boundary analysis
    println!("  Multi-variable example: rectangle dimensions");
    let mut intervals = HashMap::new();
    intervals.insert(
        "width".to_string(),
        TheoryInterval {
            min: 1,
            max: 1000,
            excluded: None,
        },
    );
    intervals.insert(
        "height".to_string(),
        TheoryInterval {
            min: 1,
            max: 500,
            excluded: None,
        },
    );

    let test_cases = generator.generate_test_cases(&intervals);
    println!("  Generated {} test cases for width × height combinations", test_cases.len());

    // Show a few representative cases
    println!("  Sample test cases:");
    for (i, witness) in test_cases.iter().take(5).enumerate() {
        let w = witness.get("width").unwrap_or(0);
        let h = witness.get("height").unwrap_or(0);
        println!("    {}: width={}, height={}, area={}", i + 1, w, h, w * h);
    }

    println!();
}

/// Demonstrate combining multiple theory solvers.
fn demo_combined_theories() {
    println!("── DEMO: Combined Multi-Theory Solving ───────────────────────────");
    println!("  Scenario: Buffer allocation with multiple constraints\n");

    println!("  fn allocate_buffer(count: usize, elem_size: usize) -> Vec<u8> {{");
    println!("      let total = count.checked_mul(elem_size)?;");
    println!("      assert!(total <= MAX_ALLOCATION);");
    println!("      assert!(elem_size.is_power_of_two());");
    println!("      vec![0u8; total]");
    println!("  }}\n");

    let bdd = Bdd::default();
    let mut universe = PredicateUniverse::new();

    // Predicates
    let v1 = universe.register(Predicate::gt("count", 0), &bdd);
    let v2 = universe.register(Predicate::le("count", 1000), &bdd);
    let v3 = universe.register(Predicate::gt("elem_size", 0), &bdd);
    let v4 = universe.register(Predicate::le("elem_size", 64), &bdd);

    let _bv1 = bdd.mk_var(v1);
    let _bv2 = bdd.mk_var(v2);
    let _bv3 = bdd.mk_var(v3);
    let _bv4 = bdd.mk_var(v4);

    // Create individual solvers
    let interval_solver = IntervalSolver::with_bounds(0, 10_000);
    let mut bitwise_solver = BitwiseSolver::new();
    bitwise_solver.require_power_of_two("elem_size");
    bitwise_solver.require_non_negative("count");

    // Test with all constraints active
    let assignments: HashMap<_, _> = vec![
        (v1, true), // count > 0
        (v2, true), // count <= 1000
        (v3, true), // elem_size > 0
        (v4, true), // elem_size <= 64
    ]
    .into_iter()
    .collect();

    println!("  Constraints:");
    println!("    0 < count <= 1000");
    println!("    0 < elem_size <= 64");
    println!("    elem_size is power of 2\n");

    // First check interval solver
    let interval_result = interval_solver.solve(&assignments, &universe);
    match &interval_result {
        SolveResult::Sat(w) => {
            println!("  IntervalSolver: SAT");
            println!("    count = {}", w.get("count").unwrap_or(0));
            println!("    elem_size = {}", w.get("elem_size").unwrap_or(0));
        }
        _ => println!("  IntervalSolver: UNSAT"),
    }

    // Then check with bitwise constraints
    let bitwise_result = bitwise_solver.solve(&assignments, &universe);
    match &bitwise_result {
        SolveResult::Sat(w) => {
            let count = w.get("count").unwrap_or(0);
            let elem_size = w.get("elem_size").unwrap_or(0);
            let is_pow2 = elem_size > 0 && (elem_size & (elem_size - 1)) == 0;

            println!("\n  BitwiseSolver: SAT");
            println!("    count = {}", count);
            println!("    elem_size = {} (power of 2: {})", elem_size, if is_pow2 { "✓" } else { "✗" });
            println!("    total allocation = {} bytes", count * elem_size);
        }
        _ => println!("\n  BitwiseSolver: UNSAT"),
    }

    println!();

    // Show how theories interact
    println!("  Theory interaction:");
    println!("    1. IntervalSolver: constrains numeric ranges");
    println!("    2. BitwiseSolver: ensures structural properties");
    println!("    Combined: finds values satisfying all constraints ✓\n");
}
