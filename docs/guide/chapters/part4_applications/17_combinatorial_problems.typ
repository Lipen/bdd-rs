#import "../../theme.typ": *

= Combinatorial Problems <ch-combinatorial-problems>

// PLAN: BDDs for constraint satisfaction and enumeration.
// Target length: 10-12 pages

== Constraint Encoding

// Content to cover:
// - Constraints as Boolean functions
// - Conjunction represents "all constraints satisfied"
// - Solution set represented symbolically
// - Counting and enumeration

== The N-Queens Problem

// Content to cover:
// - Classic constraint satisfaction example
// - One-hot encoding of queen positions
// - At-least-one and at-most-one constraints
// - BDD construction and solution counting

#example-box(title: "N-Queens Constraints")[
  For an $n times n$ board with variables $x_(i,j)$ ("queen at row $i$, column $j$"):
  - *At least one per row*: $or.big_j x_(i,j)$ for each row $i$
  - *At most one per row*: $x_(i,j) -> not or.big_(k != j) x_(i,k)$
  - Similar constraints for columns and diagonals
]

== Graph Coloring

// Content to cover:
// - k-colorability as Boolean satisfiability
// - Encoding: variables for vertex-color assignments
// - Edge constraints: adjacent vertices differ
// - Counting valid colorings

== Satisfiability and \#SAT

// Content to cover:
// - SAT checking: is BDD non-zero?
// - Model counting (#SAT): count satisfying assignments
// - All-SAT: enumerate all solutions
// - Weighted counting

```rust
// Counting solutions with bdd-rs
let solutions = bdd.sat_count(constraint_bdd, num_variables);
println!("Number of solutions: {}", solutions);
```

== Combinatorial Enumeration

// Content to cover:
// - Paths in BDD correspond to satisfying assignments
// - Efficient enumeration without full expansion
// - Random sampling from solution space
// - Applications in testing and synthesis

== Comparison with SAT Solvers

// Content to cover:
// - When BDDs outperform SAT: solution counting, all-SAT
// - When SAT outperforms BDDs: large instances, no counting needed
// - Hybrid approaches
// - Decision procedures built on both
