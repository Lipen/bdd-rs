#import "../../theme.typ": *

= Case Study: N-Queens <ch-case-studies>

#reading-path(path: "advanced")

This chapter provides a detailed walkthrough of solving the N-Queens problem using `bdd-rs`.
We choose this example because it clearly demonstrates the strengths (canonical representation) and weaknesses (variable ordering sensitivity) of BDDs.

== Problem Statement

Place $N$ queens on an $N times N$ chessboard such that no two queens attack each other.
This means no two queens can share the same:
- Row
- Column
- Diagonal

== BDD Encoding

We use a boolean variable $x_(i,j)$ for each square $(i, j)$ on the board.
If $x_(i,j)$ is true, a queen is placed at row $i$, column $j$.

Total variables: $N^2$.

=== Constraints

The constraints can be built incrementally.
For each row $i$, we enforce:
+ *At least one queen:* $limits(or)_(j=1)^N x_(i,j)$
+ *At most one queen:* For all $j != k$, $not (x_(i,j) and x_(i,k))$

However, a more efficient way to build the BDD is to construct the valid configurations for *placing a queen at $(i,j)$* and then combine them.

== Walkthrough: 8-Queens

Let's trace the execution of `examples/queens.rs` for $N=8$.

=== Step 1: Variable Allocation

We allocate $8 times 8 = 64$ variables.
The variable ordering is crucial.
- *Row-major ordering:* $x_(1,1), x_(1,2), ..., x_(8,8)$
- *Column-major ordering:* $x_(1,1), x_(2,1), ..., x_(8,8)$

`bdd-rs` uses 1-based indexing, so variable IDs range from 1 to 64.

=== Step 2: Row-by-Row Construction

We build the solution by intersecting the constraints for each row.
Let $R_i$ be the BDD representing "Row $i$ has a valid queen placement AND it doesn't conflict with any other placed queens".

```rust
let mut node = bdd.one; // Start with TRUE (all configurations valid)

for r in 0..n {
    // Build constraints for row 'r'
    let row_constraint = encode_queens_row(&bdd, n, r);

    // Intersect with previous rows
    node = bdd.apply_and(node, row_constraint);

    println!("Row {}: BDD Size = {}", r, bdd.size(node));
}
```

=== Step 3: Intermediate Explosion

A common phenomenon in BDD construction is *intermediate explosion*.
The final BDD might be small, but the intermediate steps (before all constraints are applied) can be huge.

For 8-Queens:
- Row 0: Small
- Row 4: Peak size (thousands of nodes)
- Row 7: Final size shrinks (92 solutions)

#insight-box[
  *The Garbage Collection Factor:*
  Because we create many temporary nodes during `apply_and`, the BDD manager fills up.
  Calling `bdd.collect_garbage(&[node])` after each row is essential for larger $N$ (e.g., $N=12$) to keep memory usage low.
]

== Performance Analysis

#table(
  columns: 4,
  table.header([N], [Variables], [Solutions], [Time (s)]),
  [8], [64], [92], [0.01],
  [10], [100], [724], [0.4],
  [12], [144], [14,200], [720.0],
)

The exponential growth for $N=12$ illustrates the limits of pure BDDs for combinatorial search without heuristics.
However, for $N=8$, it is instantaneous, and the resulting BDD *contains all 92 solutions* in a compressed form.

== Code Snippet

The core logic for encoding a single square's constraints:

```rust
// If we place a queen at (i, j):
// 1. It must be TRUE (high edge)
// 2. All other squares in row i, col j, and diagonals must be FALSE (low edge)
if row == i && col == j {
    // This is the queen
    node = bdd.mk_node(var, bdd.zero, node);
} else if conflicts(row, col, i, j) {
    // This square must be empty
    node = bdd.mk_node(var, node, bdd.zero);
} else {
    // Don't care (can be anything, subject to other constraints)
    node = bdd.mk_node(var, node, node);
}
```

This "don't care" handling is where BDDs shine --- they automatically compress the state space where variables don't matter.
