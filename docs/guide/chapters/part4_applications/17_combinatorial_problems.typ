#import "../../theme.typ": *

= Combinatorial Problems <ch-combinatorial-problems>

BDDs aren't just for verification --- they're a remarkably powerful tool for combinatorics.
Where SAT solvers find *one* satisfying assignment, BDDs can count *all* of them.
Where constraint solvers enumerate solutions one by one, BDDs represent the entire solution space as a single, compact data structure.

This chapter explores encoding constraints, counting solutions, and solving classic combinatorial puzzles.

== Constraint Encoding

The pattern is elegant in its simplicity:
+ Encode each constraint as a Boolean function (BDD)
+ Conjoin all constraints: $f = c_1 and c_2 and ... and c_k$
+ The resulting BDD represents *every* feasible solution

#figure(
  cetz.canvas(length: 1cm, {
    import cetz.draw: *

    content((5, 6.5), text(weight: "bold", size: 1em)[Constraint Conjunction])

    // Constraints as BDDs
    rect(
      (0.5, 4),
      (2.5, 5.5),
      fill: colors.box-definition.lighten(40%),
      stroke: 1pt + colors.primary.lighten(20%),
      radius: 4pt,
    )
    content((1.5, 5), text(size: 0.8em)[$c_1$])
    content((1.5, 4.4), text(size: 0.7em, fill: colors.text-muted)[1M sols])

    rect(
      (3.5, 4),
      (5.5, 5.5),
      fill: colors.box-example.lighten(40%),
      stroke: 1pt + colors.success.lighten(20%),
      radius: 4pt,
    )
    content((4.5, 5), text(size: 0.8em)[$c_2$])
    content((4.5, 4.4), text(size: 0.7em, fill: colors.text-muted)[500K sols])

    rect(
      (6.5, 4),
      (8.5, 5.5),
      fill: colors.box-warning.lighten(40%),
      stroke: 1pt + colors.warning.lighten(20%),
      radius: 4pt,
    )
    content((7.5, 5), text(size: 0.8em)[$c_3$])
    content((7.5, 4.4), text(size: 0.7em, fill: colors.text-muted)[2M sols])

    // AND operations
    content((3, 3), text(size: 1em)[$and$])
    line((1.5, 3.9), (3, 3.3), stroke: 1pt + colors.text-muted)
    line((4.5, 3.9), (3, 3.3), stroke: 1pt + colors.text-muted)

    content((6, 3), text(size: 1em)[$and$])
    line((3.3, 2.7), (5.7, 2.7), stroke: 1pt + colors.text-muted)
    line((7.5, 3.9), (6, 3.3), stroke: 1pt + colors.text-muted)

    // Result
    rect((3.5, 0.8), (6.5, 2.3), fill: colors.box-insight.lighten(30%), stroke: 2pt + colors.info, radius: 4pt)
    content((5, 1.8), text(size: 0.8em, weight: "semibold")[$f = c_1 and c_2 and c_3$])
    content((5, 1.2), text(size: 0.7em, fill: colors.success)[42,000 solutions])

    line((5, 2.7), (5, 2.4), stroke: 1pt + colors.text-muted, mark: (end: ">"))
  }),
  caption: [Conjoining constraint BDDs yields a BDD representing exactly the feasible solutions.],
)

#insight-box[
  Once you have the constraint BDD:
  - *SAT check*: Is the BDD non-zero? ($O(1)$)
  - *Count solutions*: Traverse the BDD ($O(|f|)$)
  - *Enumerate solutions*: Walk all paths to 1
  - *Random sample*: Weighted path selection
]

== The N-Queens Problem

Place $n$ queens on an $n times n$ chessboard so no two attack each other.
This classic problem illustrates BDD-based constraint solving beautifully.

=== Encoding

For each cell $(i,j)$, variable $x_(i,j)$ indicates whether a queen is present.

#example-box(title: "N-Queens Constraints")[
  For an $n times n$ board:
  + *At least one queen per row*: $or.big_(j=1)^n x_(i,j)$ for each row $i$
  + *At most one queen per row*: For each row $i$, pairs $(j, k)$ with $j < k$:
    $ not (x_(i,j) and x_(i,k)) $
  + *Column constraints*: Similar to rows
  + *Diagonal constraints*: For each diagonal, at most one queen
]

#figure(
  cetz.canvas(length: 1cm, {
    import cetz.draw: *

    content((5.5, 7), text(weight: "bold", size: 1em)[4-Queens: One Solution])

    // Draw 4x4 board
    let cell-size = 1
    let start-x = 3
    let start-y = 2

    for i in range(4) {
      for j in range(4) {
        let x = start-x + j * cell-size
        let y = start-y + (3 - i) * cell-size
        let fill-color = if calc.rem(i + j, 2) == 0 { colors.bg-code } else { colors.box-definition.lighten(60%) }
        rect((x, y), (x + cell-size, y + cell-size), fill: fill-color, stroke: 0.5pt + colors.line)
      }
    }

    // Place queens (one valid solution)
    let queens = ((0, 1), (1, 3), (2, 0), (3, 2))
    for (row, col) in queens {
      let x = start-x + col * cell-size + cell-size / 2
      let y = start-y + (3 - row) * cell-size + cell-size / 2
      content((x, y), text(size: 1em)[♛])
    }

    // Solution count annotation
    content((9, 4.5), align(left)[
      #set text(size: 0.8em)
      $n = 4$: 2 solutions\
      $n = 8$: 92 solutions\
      $n = 12$: 14,200 solutions
    ])

    // BDD annotation
    content((9, 2.5), align(left)[
      #set text(size: 0.7em, fill: colors.text-muted)
      BDD counts all\
      solutions in seconds
    ])
  }),
  caption: [One of the two solutions to the 4-Queens problem.],
)

=== Implementation

```rust
fn n_queens(bdd: &Bdd, n: usize) -> Ref {
    let mut vars = vec![vec![Ref::default(); n]; n];

    // Create variables for each cell
    for i in 0..n {
        for j in 0..n {
            vars[i][j] = bdd.variable(/* (i, j) index */);
        }
    }

    let mut constraint = bdd.one();

    // Row constraints
    for i in 0..n {
        // At least one queen in row i
        let at_least_one = vars[i].iter().fold(bdd.zero(), |acc, &v| bdd.or(acc, v));
        constraint = bdd.and(constraint, at_least_one);

        // At most one queen in row i
        for j in 0..n {
            for k in (j + 1)..n {
                let not_both = bdd.nand(vars[i][j], vars[i][k]);
                constraint = bdd.and(constraint, not_both);
            }
        }
    }

    // Similar for columns and diagonals...
    constraint
}

// Count solutions
let queens_bdd = n_queens(&bdd, 8);
let count = bdd.sat_count(queens_bdd, 64);  // 64 variables for 8x8
println!("8-Queens has {} solutions", count);  // 92
```

== Graph Coloring

Given a graph $G = (V, E)$, can we color vertices with $k$ colors so adjacent vertices differ?

=== Encoding

For each vertex $v$ and color $c$, variable $x_(v,c)$ indicates "vertex $v$ has color $c$".

#example-box(title: "Graph Coloring Constraints")[
  For $k$-coloring:
  + *Each vertex has at least one color*: $or.big_(c=1)^k x_(v,c)$
  + *Each vertex has at most one color*: $not (x_(v,c_1) and x_(v,c_2))$ for $c_1 != c_2$
  + *Adjacent vertices differ*: For each edge $(u, v) in E$ and color $c$:
    $ not (x_(u,c) and x_(v,c)) $
]

#figure(
  cetz.canvas(length: 1cm, {
    import cetz.draw: *

    content((5, 6.5), text(weight: "bold", size: 1em)[3-Coloring a Graph])

    // Draw a small graph (triangle plus one vertex)
    circle((2, 4), radius: 0.5, fill: rgb("#ff6b6b"), stroke: 1.5pt + colors.line, name: "a")
    content((2, 4), text(size: 0.8em)[A])

    circle((4, 4), radius: 0.5, fill: rgb("#4ecdc4"), stroke: 1.5pt + colors.line, name: "b")
    content((4, 4), text(size: 0.8em)[B])

    circle((3, 2), radius: 0.5, fill: rgb("#ffe66d"), stroke: 1.5pt + colors.line, name: "c")
    content((3, 2), text(size: 0.8em)[C])

    circle((5.5, 2), radius: 0.5, fill: rgb("#ff6b6b"), stroke: 1.5pt + colors.line, name: "d")
    content((5.5, 2), text(size: 0.8em)[D])

    // Edges
    line("a", "b", stroke: 1.5pt + colors.line)
    line("a", "c", stroke: 1.5pt + colors.line)
    line("b", "c", stroke: 1.5pt + colors.line)
    line("b", "d", stroke: 1.5pt + colors.line)

    // Legend
    content((8, 5), align(left)[
      #set text(size: 0.8em)
      #box(width: 0.8em, height: 0.8em, fill: rgb("#ff6b6b")) Red\
      #box(width: 0.8em, height: 0.8em, fill: rgb("#4ecdc4")) Cyan\
      #box(width: 0.8em, height: 0.8em, fill: rgb("#ffe66d")) Yellow
    ])

    // Explanation
    content((8, 3), align(left)[
      #set text(size: 0.7em, fill: colors.text-muted)
      BDD encodes all\
      valid colorings
    ])
  }),
  caption: [A valid 3-coloring. The BDD encodes all possible valid colorings simultaneously.],
)

== Satisfiability and \#SAT

BDDs provide *O(1)* SAT checking and *O(|f|)* solution counting:

#comparison-table(
  [*Query*],
  [*BDD Complexity*],
  [*Notes*],
  [SAT (is $f$ satisfiable?)],
  [$O(1)$],
  [Just check if BDD ≠ 0],
  [\#SAT (count solutions)],
  [$O(|f|)$],
  [Dynamic programming on BDD],
  [All-SAT (enumerate all)],
  [$O("output")$],
  [Traverse paths to 1],
  [Random solution],
  [$O(n)$],
  [Weighted random walk],
)

=== Solution Counting Algorithm

#algorithm(title: "Solution Counting")[
  ```
  SatCount(f, n):   // n = number of variables
    if f == 0: return 0
    if f == 1: return 2^n  // All assignments satisfy

    // Memoized recursion
    if f in CountCache: return CountCache[f]

    v = var(f)
    // Account for "skipped" variables above v
    skip_factor = 2^(v - expected_var)

    low_count = SatCount(low(f), n - v - 1)
    high_count = SatCount(high(f), n - v - 1)

    result = skip_factor * (low_count + high_count)
    CountCache[f] = result
    return result
  ```
]

#warning-box(title: "Skipped Variables")[
  If the BDD jumps from variable $x_1$ to $x_5$, variables $x_2, x_3, x_4$ are "don't cares".
  Each skipped variable doubles the solution count (either value works).
]

== Combinatorial Enumeration

Beyond counting, BDDs support efficient enumeration:

```rust
// Enumerate all solutions
fn all_solutions(bdd: &Bdd, f: Ref) -> Vec<Vec<bool>> {
    let mut solutions = Vec::new();
    let mut path = Vec::new();

    fn traverse(bdd: &Bdd, node: Ref, path: &mut Vec<bool>, solutions: &mut Vec<Vec<bool>>) {
        if bdd.is_zero(node) { return; }
        if bdd.is_one(node) {
            solutions.push(path.clone());
            return;
        }

        // Try low branch (variable = false)
        path.push(false);
        traverse(bdd, bdd.low(node), path, solutions);
        path.pop();

        // Try high branch (variable = true)
        path.push(true);
        traverse(bdd, bdd.high(node), path, solutions);
        path.pop();
    }

    traverse(bdd, f, &mut path, &mut solutions);
    solutions
}
```

#insight-box[
  Enumeration is efficient when you need *all* solutions.
  For huge solution spaces, use *random sampling*: at each node, randomly choose low/high weighted by solution counts in each subtree.
]

== Comparison with SAT Solvers

#comparison-table(
  [*Aspect*],
  [*BDDs*],
  [*SAT Solvers*],
  [Finding one solution],
  [Build BDD, then $O(n)$],
  [Often faster directly],
  [Counting solutions],
  [Excellent: $O(|f|)$],
  [Hard: specialized \#SAT],
  [Enumerating all],
  [Excellent: traverse BDD],
  [Requires blocking clauses],
  [Memory],
  [Can explode],
  [Usually modest],
  [Incremental solving],
  [Add constraints = AND],
  [Native support],
  [Certificates],
  [BDD is certificate],
  [Proof traces],
)

#info-box(title: "Choosing the Right Tool")[
  *Use BDDs when*:
  - You need to count or enumerate solutions
  - The same constraint structure appears repeatedly
  - The problem has exploitable regularity

  *Use SAT solvers when*:
  - You only need one solution (or unsatisfiability)
  - The instance is very large
  - The structure is irregular or data-dependent
]
