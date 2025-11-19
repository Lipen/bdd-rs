#import "../../theme.typ": *

= Enter Binary Decision Diagrams <enter-bdds>

We've seen why path explosion is a problem and glimpsed that BDDs solve it.
Now we examine _how_ BDDs achieve this compression.

Binary Decision Diagrams are a data structure for representing Boolean functions.
Despite worst-case exponential size, they often provide dramatic compression for structured problems.

== Boolean Functions: The Foundation

A Boolean function maps Boolean inputs to a Boolean output.

#definition(title: "Boolean Function")[
  A function $f : bb(B)^n -> bb(B)$ where $bb(B) = {0, 1}$.

  With $n$ inputs, there are $2^n$ possible input combinations and $2^(2^n)$ possible functions.
]

Examples:

```rust
// AND: f(x, y) = x ∧ y
fn and(x: bool, y: bool) -> bool {
    x && y
}

// XOR: f(x, y) = x ⊕ y = (x ∧ ¬y) ∨ (¬x ∧ y)
fn xor(x: bool, y: bool) -> bool {
    x != y
}

// Majority: f(x, y, z) = (x ∧ y) ∨ (x ∧ z) ∨ (y ∧ z)
fn majority(x: bool, y: bool, z: bool) -> bool {
    (x && y) || (x && z) || (y && z)
}
```

We have several ways to represent Boolean functions.
- Truth tables require $2^n$ rows --- exponential size.
- Boolean formulas vary in size but lack a canonical form.
- BDDs often achieve compact representation while providing a _canonical_ form.

== Decision Trees: The Starting Point

A decision tree evaluates a Boolean function by testing variables sequentially.

#figure(
  caption: [Decision tree for AND($x$, $y$). Each path from root to leaf represents one input combination. Dashed edges are for false (0), solid edges for true (1).],

  cetz.canvas({
    import cetz.draw: *

    // Helper functions for decision tree elements
    let draw-decision-node(pos, label) = {
      circle(pos, radius: 0.4, fill: white, stroke: colors.primary + 2pt)
      content(pos, text(fill: colors.primary, size: 0.9em, weight: "bold")[#label])
    }

    let draw-terminal(pos, value) = {
      let term-color = if value == "0" { colors.error } else { colors.success }
      rect(
        (pos.at(0) - 0.35, pos.at(1) - 0.35),
        (pos.at(0) + 0.35, pos.at(1) + 0.35),
        fill: term-color.lighten(70%),
        stroke: term-color + 2pt,
        radius: 0.1,
      )
      content(pos, text(fill: term-color, size: 0.9em, weight: "bold")[#value])
    }

    let draw-branch(from, to, is-true) = {
      let edge-color = if is-true { colors.primary } else { colors.secondary }
      let edge-style = if is-true {
        (paint: edge-color, thickness: 1.5pt)
      } else {
        (paint: edge-color, thickness: 1.5pt, dash: "dashed")
      }
      line(from, to, stroke: edge-style)
    }

    // Tree structure
    let root = (0, 3)
    let left-leaf = (-2, 0)
    let right = (2, 1.5)
    let right-left = (1, 0)
    let right-right = (3, 0)

    // Draw edges with labels
    draw-branch(root, left-leaf, false)
    content((-1.2, 1.8), text(fill: colors.text-light, size: 0.7em)[0], anchor: "east")

    draw-branch(root, right, true)
    content((1.2, 1.8), text(fill: colors.text-light, size: 0.7em)[1], anchor: "west")

    draw-branch(right, right-left, false)
    content((1.3, 0.9), text(fill: colors.text-light, size: 0.7em)[0], anchor: "east")

    draw-branch(right, right-right, true)
    content((2.7, 0.9), text(fill: colors.text-light, size: 0.7em)[1], anchor: "west")

    // Draw nodes
    draw-decision-node(root, [$x$])
    draw-decision-node(right, [$y$])
    draw-terminal(left-leaf, "0")
    draw-terminal(right-left, "0")
    draw-terminal(right-right, "1")

    // Legend
    content((4.5, 3), text(fill: colors.text-light, size: 0.75em)[Dashed = 0], anchor: "west")
    content((4.5, 2.5), text(fill: colors.text-light, size: 0.75em)[Solid = 1], anchor: "west")
  }),
) <fig:decision-tree-and>
#v(0.5em)

Each path from root to leaf represents one input combination.
Leaves are labeled with output values (0 or 1).

For function $f(x, y) = x and y$:
- Path `x=0`: Output 0 (regardless of y)
- Path `x=1, y=0`: Output 0
- Path `x=1, y=1`: Output 1

#info-box(title: "Decision Tree Properties")[
  A decision tree has $O(2^n)$ nodes for $n$ variables.
  Evaluation takes $O(n)$ time since we test each variable at most once along any path.
  However, the same subtrees may appear multiple times throughout the tree without sharing.
]

== From Trees to DAGs: Sharing Structure

Key observation: decision trees have redundancy.

In the AND tree above:
- The left subtree (when x=0) always outputs 0
- We don't need to test y

We can _share_ subtrees that compute the same function.

#definition(title: "Binary Decision Diagram (BDD)")[
  A directed acyclic graph (DAG) representing a Boolean function where:
  - Each non-terminal node tests one variable
  - Two outgoing edges: low (dashed, variable=0) and high (solid, variable=1)
  - Terminal nodes (leaves) are labeled 0 or 1
  - All paths testing variables in the same order
]

#figure(
  caption: [BDD for AND($x$, $y$) with node sharing. Both paths that lead to 0 point to the same terminal node (highlighted in cyan), demonstrating structure sharing.],

  cetz.canvas({
    import cetz.draw: *

    // Helper functions
    let draw-bdd-node(pos, label) = {
      circle(pos, radius: 0.4, fill: white, stroke: colors.primary + 2pt)
      content(pos, text(fill: colors.primary, size: 0.9em, weight: "bold")[#label])
    }

    let draw-bdd-terminal(pos, value, is-shared: false) = {
      let term-color = if value == "0" {
        if is-shared { colors.accent } else { colors.error }
      } else { colors.success }
      let fill-color = if is-shared { colors.accent.lighten(80%) } else { term-color.lighten(70%) }
      let stroke-width = if is-shared { 2.5pt } else { 2pt }

      rect(
        (pos.at(0) - 0.4, pos.at(1) - 0.4),
        (pos.at(0) + 0.4, pos.at(1) + 0.4),
        fill: fill-color,
        stroke: term-color + stroke-width,
        radius: 0.1,
      )
      content(pos, text(fill: term-color, size: 0.9em, weight: "bold")[#value])
    }

    let draw-bdd-edge(from, to, is-high) = {
      let edge-style = if is-high {
        (paint: colors.primary, thickness: 1.5pt)
      } else {
        (paint: colors.secondary, thickness: 1.5pt, dash: "dashed")
      }
      line(from, to, stroke: edge-style)
    }

    // BDD structure
    let root = (0, 3)
    let terminal0 = (-1.5, 0)
    let ynode = (2, 1.5)
    let terminal1 = (2, 0)

    // Draw edges
    draw-bdd-edge(root, terminal0, false)
    draw-bdd-edge(root, ynode, true)
    draw-bdd-edge(ynode, terminal0, false)
    draw-bdd-edge(ynode, terminal1, true)

    // Draw nodes
    draw-bdd-node(root, [$x$])
    draw-bdd-node(ynode, [$y$])
    draw-bdd-terminal(terminal0, "0", is-shared: true)
    draw-bdd-terminal(terminal1, "1")

    // Annotation for sharing
    content(
      (terminal0.at(0) - 0.7, terminal0.at(1) - 0.8),
      text(fill: colors.accent, size: 0.7em, style: "italic")[← shared!],
      anchor: "east",
    )
  }),
) <fig:bdd-and-sharing>
#v(0.5em)

Here both "0" leaves are the _same node._
The left subtree when x=0 directly points to the 0 terminal.

== Reduced Ordered BDDs (ROBDDs)

Two reduction rules transform decision trees into canonical BDDs:

#definition(title: "Reduction Rules")[
  1. *Merge:* If two nodes compute identical functions, merge them into one
  2. *Eliminate:* If a node's low and high edges point to the same child, bypass the node
]

Apply these exhaustively to get a _Reduced Ordered BDD_ (ROBDD).

#example-box(number: "3.1", title: "Reduction in Action")[
  Consider the original decision tree for the function $f(x, y) = x$:

  #align(center)[
    #cetz.canvas({
      import cetz.draw: *

      // Three stages: Original tree -> After merge -> Final ROBDD
      let stage1-x = -5
      let stage2-x = 0
      let stage3-x = 5
      let top-y = 3

      // Stage 1: Original decision tree
      content(
        (stage1-x, top-y + 1),
        text(fill: colors.text, size: 0.8em, weight: "bold")[Original Tree],
        anchor: "north",
      )

      let s1-root = (stage1-x, top-y)
      let s1-left-y = (stage1-x - 1, top-y - 1.5)
      let s1-right-y = (stage1-x + 1, top-y - 1.5)
      let s1-ll = (stage1-x - 1.5, top-y - 3)
      let s1-lr = (stage1-x - 0.5, top-y - 3)
      let s1-rl = (stage1-x + 0.5, top-y - 3)
      let s1-rr = (stage1-x + 1.5, top-y - 3)

      // Edges
      line(s1-root, s1-left-y, stroke: (dash: "dashed", paint: colors.text-light))
      line(s1-root, s1-right-y, stroke: colors.text-light)
      line(s1-left-y, s1-ll, stroke: (dash: "dashed", paint: colors.text-light))
      line(s1-left-y, s1-lr, stroke: colors.text-light)
      line(s1-right-y, s1-rl, stroke: (dash: "dashed", paint: colors.text-light))
      line(s1-right-y, s1-rr, stroke: colors.text-light)

      // Nodes
      circle(s1-root, radius: 0.25, fill: white, stroke: colors.primary + 1pt)
      content(s1-root, text(size: 0.7em)[$x$])
      circle(s1-left-y, radius: 0.25, fill: white, stroke: colors.secondary + 1pt)
      content(s1-left-y, text(size: 0.7em)[$y$])
      circle(s1-right-y, radius: 0.25, fill: white, stroke: colors.secondary + 1pt)
      content(s1-right-y, text(size: 0.7em)[$y$])

      rect(
        (s1-ll.at(0) - 0.2, s1-ll.at(1) - 0.2),
        (s1-ll.at(0) + 0.2, s1-ll.at(1) + 0.2),
        fill: colors.error.lighten(70%),
        stroke: colors.error,
        radius: 0.05,
      )
      content(s1-ll, text(size: 0.6em)[0])

      rect(
        (s1-lr.at(0) - 0.2, s1-lr.at(1) - 0.2),
        (s1-lr.at(0) + 0.2, s1-lr.at(1) + 0.2),
        fill: colors.success.lighten(70%),
        stroke: colors.success,
        radius: 0.05,
      )
      content(s1-lr, text(size: 0.6em)[1])

      rect(
        (s1-rl.at(0) - 0.2, s1-rl.at(1) - 0.2),
        (s1-rl.at(0) + 0.2, s1-rl.at(1) + 0.2),
        fill: colors.error.lighten(70%),
        stroke: colors.error,
        radius: 0.05,
      )
      content(s1-rl, text(size: 0.6em)[0])

      rect(
        (s1-rr.at(0) - 0.2, s1-rr.at(1) - 0.2),
        (s1-rr.at(0) + 0.2, s1-rr.at(1) + 0.2),
        fill: colors.success.lighten(70%),
        stroke: colors.success,
        radius: 0.05,
      )
      content(s1-rr, text(size: 0.6em)[1])

      // Arrow to stage 2
      line((stage1-x + 2.2, top-y), (stage2-x - 2.2, top-y), stroke: colors.accent + 1.5pt, mark: (end: ">"))
      content(
        (stage1-x + 2.2 + (stage2-x - 2.2 - stage1-x - 2.2) / 2, top-y + 0.4),
        text(fill: colors.accent, size: 0.7em)[eliminate $y$],
        anchor: "south",
      )

      // Stage 2: Final ROBDD
      content(
        (stage2-x, top-y + 1),
        text(fill: colors.success, size: 0.8em, weight: "bold")[Final ROBDD],
        anchor: "north",
      )

      let s2-root = (stage2-x, top-y)
      let s2-left = (stage2-x - 0.8, top-y - 2)
      let s2-right = (stage2-x + 0.8, top-y - 2)

      // Edges
      line(s2-root, s2-left, stroke: (dash: "dashed", paint: colors.secondary, thickness: 1.5pt))
      line(s2-root, s2-right, stroke: (paint: colors.primary, thickness: 1.5pt))

      // Nodes
      circle(s2-root, radius: 0.35, fill: white, stroke: colors.primary + 2pt)
      content(s2-root, text(size: 0.85em, fill: colors.primary, weight: "bold")[$x$])

      rect(
        (s2-left.at(0) - 0.3, s2-left.at(1) - 0.3),
        (s2-left.at(0) + 0.3, s2-left.at(1) + 0.3),
        fill: colors.error.lighten(70%),
        stroke: colors.error + 2pt,
        radius: 0.1,
      )
      content(s2-left, text(size: 0.8em, weight: "bold")[0])

      rect(
        (s2-right.at(0) - 0.3, s2-right.at(1) - 0.3),
        (s2-right.at(0) + 0.3, s2-right.at(1) + 0.3),
        fill: colors.success.lighten(70%),
        stroke: colors.success + 2pt,
        radius: 0.1,
      )
      content(s2-right, text(size: 0.8em, weight: "bold")[1])

      content(
        (stage2-x, top-y - 3.2),
        text(fill: colors.success, size: 0.75em, style: "italic")[7 nodes → 3 nodes],
        anchor: "north",
      )
    })
  ]

  We first observe that both $y$ nodes produce identical results regardless of input.
  Then we apply the elimination rule: since the $y$ node's output doesn't actually depend on $y$ (both branches lead to the same terminals), we can eliminate it entirely.
  The final ROBDD has just 3 nodes instead of 7!
]

== Canonicity: The Magic Property

#theorem(title: "ROBDD Canonicity")[
  Given a fixed variable ordering, every Boolean function has a unique ROBDD representation.

  This means: $f = g$ if and only if their ROBDDs are identical (same graph structure).
]

*Why this matters:*
- Equality checking is $O(1)$: just compare pointers
- No need to reason about logical equivalence
- Hash consing prevents duplicate nodes

This is _enormous_ for verification.
Checking if two complex formulas are equivalent is normally expensive (co-NP-complete).
With ROBDDs, it's free.

#insight-box[
  *Canonicity is the killer feature.*
  Most data structures for Boolean functions have multiple representations for the same function.
  ROBDDs have exactly one.
  This makes many operations trivial.
]

== Variable Ordering: The Achilles Heel

ROBDDs are canonical _given a fixed variable ordering._
Different orderings produce different (but equivalent) BDDs.

#warning-box[
  *ROBDD size is extremely sensitive to variable ordering.*
  Bad ordering: exponential size.
  Good ordering: polynomial or even linear size.
]

#example-box(number: "3.2", title: "Ordering Matters")[
  Consider the formula $f(x_1, x_2, x_3, x_4) = (x_1 and x_2) or (x_3 and x_4)$.

  #figure(
    caption: [Variable ordering impact on BDD size. Good ordering ($x_1 < x_2 < x_3 < x_4$) groups related variables, producing a compact 6-node BDD. Bad ordering ($x_1 < x_3 < x_2 < x_4$) forces alternation, resulting in a much larger BDD.],

    cetz.canvas(length: 1cm, {
      import cetz.draw: *

      // Two BDDs side by side: good vs bad ordering
      let good-x = -4
      let bad-x = 4
      let top-y = 4 // Good ordering: x1 < x2 < x3 < x4
      content((good-x, top-y + 0.8), text(fill: colors.success, size: 0.85em, weight: "bold")[Good: $x_1 < x_2 < x_3 < x_4$], anchor: "north")

      let g-x1 = (good-x, top-y)
      let g-x2 = (good-x, top-y - 1.5)
      let g-x3 = (good-x, top-y - 3)
      let g-x4 = (good-x, top-y - 4.5)
      let g-0 = (good-x - 0.8, top-y - 6)
      let g-1 = (good-x + 0.8, top-y - 6)

      // Good BDD structure (simplified)
      circle(g-x1, radius: 0.3, fill: white, stroke: colors.success + 1.5pt)
      content(g-x1, text(size: 0.7em)[$x_1$])
      circle(g-x2, radius: 0.3, fill: white, stroke: colors.success + 1.5pt)
      content(g-x2, text(size: 0.7em)[$x_2$])
      circle(g-x3, radius: 0.3, fill: white, stroke: colors.success + 1.5pt)
      content(g-x3, text(size: 0.7em)[$x_3$])
      circle(g-x4, radius: 0.3, fill: white, stroke: colors.success + 1.5pt)
      content(g-x4, text(size: 0.7em)[$x_4$])

      rect((g-0.at(0) - 0.25, g-0.at(1) - 0.25), (g-0.at(0) + 0.25, g-0.at(1) + 0.25), fill: colors.error.lighten(70%), stroke: colors.error + 1.5pt, radius: 0.08)
      content(g-0, text(size: 0.7em)[0])

      rect((g-1.at(0) - 0.25, g-1.at(1) - 0.25), (g-1.at(0) + 0.25, g-1.at(1) + 0.25), fill: colors.success.lighten(70%), stroke: colors.success + 1.5pt, radius: 0.08)
      content(g-1, text(size: 0.7em)[1])

      // Edges (simplified structure)
      line(g-x1, g-x3, stroke: (dash: "dashed", paint: colors.text-light))
      line(g-x1, g-x2, stroke: colors.text-light)
      line(g-x2, g-0, stroke: (dash: "dashed", paint: colors.text-light))
      line(g-x2, g-x3, stroke: colors.text-light)
      line(g-x3, g-0, stroke: (dash: "dashed", paint: colors.text-light))
      line(g-x3, g-x4, stroke: colors.text-light)
      line(g-x4, g-0, stroke: (dash: "dashed", paint: colors.text-light))
      line(g-x4, g-1, stroke: colors.text-light)

      content((good-x, top-y - 6.8), text(fill: colors.success, size: 0.75em)[6 nodes], anchor: "north")

      // Bad ordering: x1 < x3 < x2 < x4
      content((bad-x, top-y + 0.8), text(fill: colors.error, size: 0.85em, weight: "bold")[Bad: $x_1 < x_3 < x_2 < x_4$], anchor: "north")

      // Show larger, more complex structure
      let b-nodes = (
        (bad-x, top-y),
        (bad-x - 0.7, top-y - 1.2),
        (bad-x + 0.7, top-y - 1.2),
        (bad-x - 1.2, top-y - 2.4),
        (bad-x - 0.2, top-y - 2.4),
        (bad-x + 0.2, top-y - 2.4),
        (bad-x + 1.2, top-y - 2.4),
        (bad-x - 0.8, top-y - 3.6),
        (bad-x + 0.8, top-y - 3.6),
      )

      for node in b-nodes { circle(node, radius: 0.2, fill: white, stroke: colors.error + 1pt) }

      let b-0 = (bad-x - 0.8, top-y - 5)
      let b-1 = (bad-x + 0.8, top-y - 5)

      rect((b-0.at(0) - 0.25, b-0.at(1) - 0.25), (b-0.at(0) + 0.25, b-0.at(1) + 0.25), fill: colors.error.lighten(70%), stroke: colors.error + 1.5pt, radius: 0.08)
      content(b-0, text(size: 0.7em)[0])

      rect((b-1.at(0) - 0.25, b-1.at(1) - 0.25), (b-1.at(0) + 0.25, b-1.at(1) + 0.25), fill: colors.success.lighten(70%), stroke: colors.success + 1.5pt, radius: 0.08)
      content(b-1, text(size: 0.7em)[1])

      // Many edges (just show complexity)
      for i in range(0, b-nodes.len() - 1) {
        if i < 2 {
          line(b-nodes.at(i), b-nodes.at(2 * i + 1), stroke: (dash: "dashed", paint: colors.text-light, thickness: 0.8pt))
          line(b-nodes.at(i), b-nodes.at(2 * i + 2), stroke: (paint: colors.text-light, thickness: 0.8pt))
        }
      }
      line(b-nodes.at(7), b-0, stroke: colors.text-light)
      line(b-nodes.at(8), b-1, stroke: colors.text-light)

      content((bad-x, top-y - 5.8), text(fill: colors.error, size: 0.75em)[12+ nodes], anchor: "north")

      // Central comparison arrow
      content((0, top-y - 2.5), text(fill: colors.accent, size: 0.8em, style: "italic")[ordering matters!], anchor: "center")
    }),
  ) <fig:variable-ordering>

  With the ordering $x_1 < x_2 < x_3 < x_4$, the BDD can test the pair $x_1, x_2$ together, then test $x_3, x_4$ together.
  This natural grouping produces a small BDD with around 6-8 nodes.

  But with the interleaved ordering $x_1 < x_3 < x_2 < x_4$, the BDD must alternate between testing the two subformulas.
  This forces more complex structure, resulting in a larger BDD with around 10-12 nodes.

  For extreme cases like integer comparison, bad ordering creates exponential blowup rather than just a constant factor increase.
]Famous example: integer comparison.

Consider testing if two $n$-bit integers are equal: $f = (x_1 = y_1) and dots.h.c and (x_n = y_n)$.

Good ordering: $x_1 < y_1 < x_2 < y_2 < dots.h.c < x_n < y_n$
- ROBDD size: $O(n)$ nodes

Bad ordering: $x_1 < x_2 < dots.h.c < x_n < y_1 < y_2 < dots.h.c < y_n$
- ROBDD size: $O(2^n)$ nodes (exponential!)

Finding optimal ordering is NP-complete.
In practice:
- Use heuristics (group related variables)
- Dynamic reordering for iterative improvement
- Accept that some functions are inherently hard

#info-box(title: "Variable Ordering in Practice")[
  For program analysis:
  - Group variables from the same statement
  - Order program counters before data variables
  - Use domain knowledge about structure

  The `bdd-rs` library doesn't yet support dynamic reordering, so choose wisely upfront.
]

== BDD Operations

The power of BDDs comes from efficient operations.

=== Basic Operations

*Apply:* Combine two BDDs with a binary operator (∧, ∨, ⊕, etc.)

```rust
let f = bdd.mk_var(1);  // Variable x₁
let g = bdd.mk_var(2);  // Variable x₂
let h = bdd.apply_and(f, g);  // x₁ ∧ x₂
```

*Not:* Complement a BDD

```rust
let not_f = bdd.apply_not(f);  // ¬x₁
```

*If-Then-Else (ITE):* $"ITE"(f, g, h) = (f and g) or (not f and h)$

This is the universal operator; all other operations can be expressed via ITE.

```rust
// AND: f ∧ g = ITE(f, g, 0)
// OR:  f ∨ g = ITE(f, 1, g)
// XOR: f ⊕ g = ITE(f, ¬g, g)
```

=== Complexity

With memoization (caching intermediate results):

- *Apply:* $O(|f| dot.op |g|)$ where $|f|$ is number of nodes
- *Not:* $O(1)$ (flip terminal labels or use complement edges)
- *ITE:* $O(|f| dot.op |g| dot.op |h|)$

In practice, these are much faster due to sharing and caching.

#info-box(title: "Memoization is Critical")[
  Without caching:
  - Each operation might recompute the same subproblems
  - Complexity becomes exponential

  With caching:
  - Each unique subproblem computed once
  - Polynomial complexity in BDD size

  The `bdd-rs` library uses hash-based memoization internally.
]

=== Quantification

*Existential quantification:* $exists x . f$

"Is there any value of $x$ that makes $f$ true?"

Computed as: $f[x <- 0] or f[x <- 1]$

```rust
let f = bdd.mk_and(x, y);  // x ∧ y
let exists_x = bdd.exists(f, 1);  // ∃x. (x ∧ y) = y
```

*Universal quantification:* $forall x . f$

"Does $f$ hold for all values of $x$?"

Computed as: $f[x <- 0] and f[x <- 1]$

```rust
let forall_x = bdd.forall(f, 1);  // ∀x. (x ∧ y) = 0
```

Quantification is crucial for symbolic model checking.

== Why BDDs Work for Program Analysis

BDDs compress structured Boolean functions.
Program path conditions have structure:

1. *Locality:* Conditions often involve few variables
2. *Repetition:* Same conditions appear on many paths
3. *Hierarchy:* Outer conditions constrain inner ones

Example from Chapter 2:

```rust
if mode == Mode::Off {
    return Action::Off;  // Condition: mode=Off
}

if temp < TEMP_MIN {
    if time > EMERGENCY_TIME {
        return Action::EmergencyHeat;  // Condition: mode≠Off ∧ temp<MIN ∧ time>EMERG
    }
    return Action::HeatOn;  // Condition: mode≠Off ∧ temp<MIN ∧ time≤EMERG
}
```

All paths except the first share `mode≠Off`.
Paths 2-3 share `mode≠Off ∧ temp<MIN`.

BDD exploits this sharing:
- `mode≠Off` appears once in the BDD
- Paths branch only where they differ

[BDD diagram showing path condition sharing would go here]

Result: 6 explicit paths represented with far fewer BDD nodes.

#example-box(number: "3.3", title: "Real-World Compression")[
  Bryant's original paper (1986) showed:
  - Combinational circuit verification with 100+ gates
  - Explicit truth table: $2^(100)$ rows (impossible)
  - BDD representation: ~10,000 nodes (feasible)

  In symbolic model checking:
  - State spaces with $10^(20)$ states
  - BDD representation: millions of nodes (manageable)
]

== Historical Context

#historical-note(
  person: "Randal Bryant",
  year: "1986",
  title: "Graph-Based Algorithms for Boolean Function Manipulation",
)[
  Bryant introduced ROBDDs and proved canonicity.
  This foundational work enabled efficient symbolic manipulation of Boolean functions.

  Key contributions:
  - Reduction rules ensuring canonical form
  - Algorithms for apply and ITE operations
  - Demonstration of practical efficiency
]

#historical-note(
  person: "Burch et al.",
  year: "1990",
  title: "Symbolic Model Checking: $10^(20)$ States and Beyond",
)[
  Applied BDDs to model checking hardware systems.
  Showed that BDDs could represent state spaces with $10^(20)$ states using only millions of nodes.

  This work launched the field of _symbolic model checking_ and revolutionized hardware verification.
]

== BDDs in the Wild

BDDs are used in:

*Hardware verification:* Checking circuits for correctness
- Intel, AMD, IBM use BDD-based tools
- Critical for processor design

*Formal verification:* Model checkers like NuSMV, SPIN
- Verify concurrent systems
- Protocol verification

*Software analysis:* Static analysis tools
- Data flow analysis
- Security vulnerability detection

*SAT solving:* Some SAT solvers use BDD techniques
- Hybrid approaches combining BDDs and CDCL

*Program synthesis:* Generating programs from specifications
- BDDs encode constraints

== When BDDs Fail

Not all Boolean functions compress well.

#warning-box[
  *Functions with exponential BDD size (for any ordering):*
  - Integer multiplication (proven exponential)
  - Some cryptographic functions
  - Random Boolean functions (no structure)
]

For these, BDDs are impractical.
Alternative approaches:
- SAT solvers (work on formula directly)
- And-Inverter Graphs (AIGs)
- Specialized data structures

But for _structured_ problems (like program control flow), BDDs excel.

== Summary

BDDs are a canonical representation for Boolean functions.
They achieve compression by sharing common substructures.
Operations (∧, ∨, ¬, quantification) are efficient.

Key insights:
- Canonicity enables $O(1)$ equality checking
- Variable ordering critically affects size
- Memoization makes operations polynomial in BDD size
- Structure in problems (like program paths) leads to compression

BDDs transform intractable path-sensitive analysis into a practical technique.

In the next chapter, we see how to use the `bdd-rs` library to build BDDs and manipulate them programmatically.

#chapter-summary(
  [
    *Boolean functions map ${0,1}^n -> {0,1}$.*
    With $n$ inputs, there are $2^(2^n)$ possible functions. Representing them efficiently is crucial.
  ],
  [
    *Decision trees evaluate functions but have exponential size.*
    Each path from root to leaf is one input combination. No sharing between paths.
  ],
  [
    *BDDs are DAGs with shared structure.*
    Reduction rules (merge identical nodes, eliminate redundant tests) compress trees into DAGs.
  ],
  [
    *ROBDDs are canonical.*
    Given fixed variable ordering, each function has exactly one ROBDD. Equality checking is $O(1)$.
  ],
  [
    *Variable ordering critically affects BDD size.*
    Good ordering: polynomial size. Bad ordering: exponential size. Finding optimal ordering is NP-complete.
  ],
  [
    *BDD operations are efficient with memoization.*
    Apply, ITE, quantification run in polynomial time in BDD size when cached.
  ],
  [
    *BDDs excel on structured problems.*
    Program path conditions exhibit locality, repetition, hierarchy. BDDs exploit this structure.
  ],
  [
    *Not all functions compress.*
    Integer multiplication, random functions have exponential BDD size for any ordering.
  ],
  [
    *Main insight:*
    BDDs provide canonical, compact representations for structured Boolean functions, enabling efficient manipulation critical for symbolic program analysis.
  ],
)

#v(2em)
