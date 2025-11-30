#import "../../theme.typ": *

= Variable Ordering <ch-variable-ordering>

Variable ordering is the Achilles' heel of BDDs.
The same Boolean function can have a linear-sized BDD under one ordering and an exponential-sized BDD under another.
Understanding and controlling variable ordering is essential for practical BDD use --- it often makes the difference between a solution in milliseconds and a computation that never terminates.

== Why Ordering Matters

The size of a BDD depends *critically* on the variable ordering.
This is not merely a constant factor --- it is the difference between tractable and intractable, between success and failure.

#figure(
  cetz.canvas(length: 1cm, {
    import cetz.draw: *

    // Good ordering
    content((3.5, 7.5), text(weight: "bold", fill: colors.success)[Good Ordering: $x_1 < y_1 < x_2 < y_2$])

    // Linear BDD structure (schematic)
    bdd-decision-node((3.5, 6), [$x_1$], name: "x1g")
    bdd-decision-node((3.5, 4.5), [$y_1$], name: "y1g")
    bdd-decision-node((3.5, 3), [$x_2$], name: "x2g")
    bdd-decision-node((3.5, 1.5), [$y_2$], name: "y2g")

    line((3.5, 5.6), (3.5, 4.9), stroke: 1pt + colors.line, mark: (end: ">"))
    line((3.5, 4.1), (3.5, 3.4), stroke: 1pt + colors.line, mark: (end: ">"))
    line((3.5, 2.6), (3.5, 1.9), stroke: 1pt + colors.line, mark: (end: ">"))

    content((3.5, 0.5), text(size: 0.9em, fill: colors.success)[Size: $O(n)$])

    // Bad ordering
    content((10, 7.5), text(weight: "bold", fill: colors.error)[Bad Ordering: $x_1 < x_2 < y_1 < y_2$])

    // Exponential BDD structure (schematic)
    bdd-decision-node((10, 6), [$x_1$], name: "x1b")

    bdd-decision-node((8.5, 4.5), [$x_2$], name: "x2b-l")
    bdd-decision-node((11.5, 4.5), [$x_2$], name: "x2b-r")

    bdd-decision-node((7.5, 3), [$y_1$], name: "y1b-ll")
    bdd-decision-node((9.5, 3), [$y_1$], name: "y1b-lr")
    bdd-decision-node((10.5, 3), [$y_1$], name: "y1b-rl")
    bdd-decision-node((12.5, 3), [$y_1$], name: "y1b-rr")

    // Edges
    line((9.6, 5.6), (8.7, 4.9), stroke: (dash: "dashed", paint: colors.line, thickness: 1pt))
    line((10.4, 5.6), (11.3, 4.9), stroke: 1pt + colors.line)

    line((8.1, 4.1), (7.7, 3.4), stroke: (dash: "dashed", paint: colors.line, thickness: 0.8pt))
    line((8.9, 4.1), (9.3, 3.4), stroke: 0.8pt + colors.line)
    line((11.1, 4.1), (10.7, 3.4), stroke: (dash: "dashed", paint: colors.line, thickness: 0.8pt))
    line((11.9, 4.1), (12.3, 3.4), stroke: 0.8pt + colors.line)

    content((10, 0.5), text(size: 0.9em, fill: colors.error)[Size: $O(2^n)$])

    // Center explanation
    content((6.75, -0.5), align(center)[
      #set text(size: 0.8em)
      Function: $(x_1 and y_1) or (x_2 and y_2)$
    ])
  }),
  caption: [The same function with different orderings: linear vs. exponential size.],
)

#warning-box(title: "Ordering Can Make or Break Performance")[
  For the function $f = (x_1 and y_1) or (x_2 and y_2) or ... or (x_n and y_n)$:
  - *Interleaved ordering* $x_1 < y_1 < x_2 < y_2 < ...$: $O(n)$ nodes
  - *Separated ordering* $x_1 < x_2 < ... < y_1 < y_2 < ...$: $O(2^n)$ nodes

  The difference grows with $n$ --- for $n = 20$, this is 40 nodes vs. over a million!
]

=== The Intuition

Why does interleaved ordering work better?
Consider what happens when we decide $x_1 = 0$ in each ordering:

- *Interleaved*: The term $x_1 and y_1$ becomes $0$. Variable $y_1$ is tested next, but it doesn't matter --- we move directly to $x_2$. The subproblem simplifies.

- *Separated*: After deciding all $x_i$, we still need to track *which* $x_i$ were 1 to know which $y_i$ matter. This "remembering" causes exponential blowup.

#insight-box[
  Good orderings keep *related variables close together*.
  When $x$ and $y$ appear in a term $x and y$, testing them consecutively allows early simplification.
]

== Static Ordering Heuristics

Before building a BDD, we can choose an initial ordering based on the structure of the input.

=== DFS Ordering

For circuits, a depth-first traversal from outputs to inputs often produces good orderings:

```rust
fn dfs_ordering(circuit: &Circuit) -> Vec<Var> {
    let mut order = Vec::new();
    let mut visited = HashSet::new();

    for output in circuit.outputs() {
        dfs_visit(output, &mut order, &mut visited);
    }
    order
}
```

Variables encountered earlier in DFS tend to be "closer" to outputs and get lower indices.

=== FORCE Algorithm

The FORCE algorithm iteratively improves ordering by minimizing a "span" metric --- how far apart related variables are placed:

#algorithm(title: "FORCE Heuristic")[
  ```
  FORCE(clauses, iterations):
    ordering = initial_random_ordering()

    for i in 1..iterations:
      for each variable v:
        // Compute center of gravity
        cog = average position of variables
              that share a clause with v

        // Move v toward its COG
        target[v] = cog

      // Sort variables by target position
      ordering = sort_by(target)

    return ordering
  ```
]

== Dynamic Variable Reordering

Even with good heuristics, the initial ordering may become suboptimal as computation proceeds.
*Dynamic reordering* adjusts the ordering during BDD operations.

=== The Sifting Algorithm

Sifting (Rudell, 1993) is the most widely used reordering algorithm:

#figure(
  cetz.canvas(length: 1cm, {
    import cetz.draw: *

    // Sifting visualization
    content((6, 7), text(weight: "bold", size: 1em)[Sifting: Finding the Best Position])

    // Level bars
    let levels = ("$x$", "$y$", "$z$", "$w$")
    for (i, name) in levels.enumerate() {
      let y = 5.5 - i * 1.2
      rect(
        (1, y - 0.3),
        (11, y + 0.3),
        fill: if i == 1 { colors.box-warning.lighten(30%) } else { colors.bg-code },
        stroke: 0.5pt + colors.line,
        radius: 2pt,
      )
      content((0.5, y), text(size: 0.8em)[#name], anchor: "east")
      content((11.5, y), text(size: 0.7em, fill: colors.text-muted)[Level #i], anchor: "west")
    }

    // Highlight sifting variable
    content((6, 6.5), text(size: 0.8em, fill: colors.warning)[Sifting variable $y$...])

    // Arrows showing movement
    line((6, 4.3), (6, 3.5), stroke: 2pt + colors.warning, mark: (end: ">", fill: colors.warning))
    line((6, 3), (6, 2.2), stroke: 2pt + colors.warning, mark: (end: ">", fill: colors.warning))
    line((6, 1.7), (6, 0.9), stroke: 2pt + colors.warning, mark: (end: ">", fill: colors.warning))

    // Size annotations
    content((8, 4.3), text(size: 0.7em)[size = 150])
    content((8, 3), text(size: 0.7em, fill: colors.success)[size = 120 ✓ best])
    content((8, 1.7), text(size: 0.7em)[size = 180])
    content((8, 0.4), text(size: 0.7em)[size = 200])

    // Return arrow
    line((4, 0.4), (4, 3), stroke: 1.5pt + colors.success, mark: (end: ">", fill: colors.success))
    content((3, 1.7), text(size: 0.7em, fill: colors.success)[return])
  }),
  caption: [Sifting moves a variable through all positions, tracking where total BDD size is minimized.],
)

#algorithm(title: "Sifting (Rudell 1993)")[
  ```
  Sifting():
    for each variable v (in decreasing size order):
      best_pos = current_level(v)
      best_size = total_nodes()

      // Move v down through all levels
      while not at_bottom(v):
        swap_adjacent(v, below(v))
        if total_nodes() < best_size:
          best_pos = current_level(v)
          best_size = total_nodes()

      // Move v back up to best position
      while current_level(v) > best_pos:
        swap_adjacent(above(v), v)
  ```
]

=== Level Swapping

The core operation in sifting is *swapping adjacent levels*.
This is a local operation that only affects nodes at those two levels:

#figure(
  cetz.canvas(length: 1cm, {
    import cetz.draw: *

    // Before swap
    content((3, 6.5), text(weight: "bold")[Before Swap])

    bdd-decision-node((3, 5), "x", name: "x-before")
    bdd-decision-node((2, 3.5), "y", name: "y-before-l")
    bdd-decision-node((4, 3.5), "y", name: "y-before-r")
    bdd-terminal-node((1, 2), "a", name: "a-before")
    bdd-terminal-node((2.5, 2), "b", name: "b-before")
    bdd-terminal-node((3.5, 2), "c", name: "c-before")
    bdd-terminal-node((5, 2), "d", name: "d-before")

    bdd-low-edge("x-before", "y-before-l")
    bdd-high-edge("x-before", "y-before-r")
    bdd-low-edge("y-before-l", "a-before")
    bdd-high-edge("y-before-l", "b-before")
    bdd-low-edge("y-before-r", "c-before")
    bdd-high-edge("y-before-r", "d-before")

    // Arrow
    line((5.5, 4), (7, 4), stroke: 2pt + colors.primary, mark: (end: ">", fill: colors.primary))
    content((6.25, 4.5), text(size: 0.8em)[swap])

    // After swap
    content((10, 6.5), text(weight: "bold")[After Swap])

    bdd-decision-node((10, 5), "y", name: "y-after")
    bdd-decision-node((9, 3.5), "x", name: "x-after-l")
    bdd-decision-node((11, 3.5), "x", name: "x-after-r")
    bdd-terminal-node((8, 2), "a", name: "a-after")
    bdd-terminal-node((9.5, 2), "c", name: "c-after")
    bdd-terminal-node((10.5, 2), "b", name: "b-after")
    bdd-terminal-node((12, 2), "d", name: "d-after")

    bdd-low-edge("y-after", "x-after-l")
    bdd-high-edge("y-after", "x-after-r")
    bdd-low-edge("x-after-l", "a-after")
    bdd-high-edge("x-after-l", "c-after")
    bdd-low-edge("x-after-r", "b-after")
    bdd-high-edge("x-after-r", "d-after")
  }),
  caption: [Swapping levels $x$ and $y$ restructures the BDD while preserving the function.],
)

The swap operation:
+ Takes each node at the upper level
+ Computes new children based on the grandchildren
+ Creates new nodes at both levels as needed
+ Updates the unique table

== Reordering in bdd-rs

`bdd-rs` provides explicit variable ordering control through the `var_order` and `level_map` data structures:

```rust
// Get the level of a variable
let level: Level = bdd.get_level(var)?;

// Get the variable at a level
let var: Var = bdd.get_var_at_level(level);

// Iterate variables in order
for level in 0..bdd.num_levels() {
    let var = bdd.get_var_at_level(Level(level));
    // Process variables top-to-bottom
}
```

#info-box(title: "Current Capabilities")[
  `bdd-rs` currently supports:
  - Explicit variable ordering during construction
  - Level/variable mapping queries
  - Manual ordering specification

  Dynamic reordering (sifting) is planned for future releases.
]

== Ordering for Specific Domains

Different problem domains have different optimal ordering strategies.

=== Circuits

For circuits, follow signal flow --- inputs near the top, internal signals in the middle, outputs near the bottom.
Variables that share gates should be adjacent.

=== Transition Relations

For symbolic model checking with transition relations on state variables $(s_1, ..., s_n)$ and next-state variables $(s'_1, ..., s'_n)$:

- *Interleaved*: $s_1 < s'_1 < s_2 < s'_2 < ...$ (usually best)
- *Separated*: $s_1 < s_2 < ... < s'_1 < s'_2 < ...$ (often exponential)

=== Arithmetic

For arithmetic functions like addition or multiplication:
- *MSB-first*: Often better for multiplication
- *LSB-first*: Often better for addition
- Experiment with both!

#comparison-table(
  [*Domain*],
  [*Strategy*],
  [*Rationale*],
  [Circuits],
  [Follow signal flow],
  [Related signals stay close],
  [FSMs],
  [Interleave state/next],
  [Transition locality],
  [Arithmetic],
  [Try both MSB/LSB],
  [Problem-dependent],
  [Feature models],
  [Respect hierarchy],
  [Parent before children],
)
