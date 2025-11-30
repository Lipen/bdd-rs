#import "../../theme.typ": *

= BDD Variants <ch-bdd-variants>

Standard ROBDDs are just one point in a rich design space.
By tweaking the reduction rules, terminal values, or structural constraints, we get different data structures --- each optimized for different problem domains.

This chapter surveys the most important variants: ZDDs for sparse combinatorics, ADDs for numeric computations, and others that have found their niche.

== Beyond Binary Decisions

ROBDDs represent functions $f : BB^n -> BB$ --- Boolean inputs, Boolean output.
But many real problems involve:
- *Sparse sets*: Most elements absent (SAT solving, graph algorithms)
- *Numeric values*: Probabilities, costs, timing constraints
- *Multi-valued logic*: More than two truth values

Different BDD variants address each of these needs.

#figure(
  cetz.canvas(length: 1cm, {
    import cetz.draw: *

    content((6, 7), text(weight: "bold", size: 1em)[BDD Variant Landscape])

    // Standard BDD
    rect((0.5, 4), (3.5, 6.5), fill: colors.box-definition.lighten(40%), stroke: 1pt + colors.primary, radius: 6pt)
    content((2, 6), text(weight: "semibold", size: 0.9em)[ROBDD])
    content((2, 5.5), text(size: 0.7em, fill: colors.text-muted)[$f : BB^n -> BB$])
    content((2, 4.8), text(size: 0.7em)[Boolean functions])
    content((2, 4.3), text(size: 0.7em)[Verification, synthesis])

    // ZDD
    rect(
      (4, 4),
      (7, 6.5),
      fill: colors.box-example.lighten(40%),
      stroke: 1pt + colors.success.lighten(20%),
      radius: 6pt,
    )
    content((5.5, 6), text(weight: "semibold", size: 0.9em)[ZDD])
    content((5.5, 5.5), text(size: 0.7em, fill: colors.text-muted)[Set families])
    content((5.5, 4.8), text(size: 0.7em)[Sparse sets])
    content((5.5, 4.3), text(size: 0.7em)[Combinatorics, SAT])

    // ADD/MTBDD
    rect(
      (7.5, 4),
      (10.5, 6.5),
      fill: colors.box-warning.lighten(40%),
      stroke: 1pt + colors.warning.lighten(20%),
      radius: 6pt,
    )
    content((9, 6), text(weight: "semibold", size: 0.9em)[ADD/MTBDD])
    content((9, 5.5), text(size: 0.7em, fill: colors.text-muted)[$f : BB^n -> RR$])
    content((9, 4.8), text(size: 0.7em)[Numeric functions])
    content((9, 4.3), text(size: 0.7em)[Probability, costs])

    // Arrows showing relationships
    line((3.5, 5.25), (4, 5.25), stroke: 1pt + colors.text-muted, mark: (end: ">"))
    line((7, 5.25), (7.5, 5.25), stroke: 1pt + colors.text-muted, mark: (end: ">"))

    // Common base
    rect((3, 1.5), (8, 3), fill: colors.bg-code, stroke: 1pt + colors.line, radius: 4pt)
    content((5.5, 2.6), text(size: 0.8em, weight: "semibold")[Shared Foundation])
    content((5.5, 2.1), text(size: 0.7em)[DAG structure, memoization, canonicity])

    line((2, 4), (4.5, 3), stroke: 1pt + colors.text-muted)
    line((5.5, 4), (5.5, 3), stroke: 1pt + colors.text-muted)
    line((9, 4), (6.5, 3), stroke: 1pt + colors.text-muted)
  }),
  caption: [BDD variants share core ideas but differ in reduction rules and terminal values.],
)

== Zero-Suppressed BDDs (ZDDs)

ZDDs, introduced by Minato in 1993, are optimized for *sparse set families* --- collections where most elements are absent from most sets.

#definition(title: "Zero-Suppressed Decision Diagram")[
  A *ZDD* uses a different reduction rule than BDDs:
  - *BDD rule*: Delete node if low = high
  - *ZDD rule*: Delete node if high = 0 (redirect to low)

  This makes ZDDs compact when sets are sparse.
]

The key insight: in a family of sparse sets, most elements are *absent* from most sets.
The ZDD rule lets us skip mentioning absent elements entirely.

#figure(
  cetz.canvas(length: 1cm, {
    import cetz.draw: *

    // BDD vs ZDD comparison
    content((3.5, 7), text(weight: "bold")[BDD Representation])
    content((9.5, 7), text(weight: "bold")[ZDD Representation])

    // BDD: showing set {a} from universe {a,b,c}
    bdd-decision-node((3.5, 5.5), "a", name: "a-bdd")
    bdd-decision-node((2, 4), "b", name: "b-bdd-l")
    bdd-decision-node((5, 4), "b", name: "b-bdd-r")
    bdd-decision-node((1, 2.5), "c", name: "c-bdd-ll")
    bdd-decision-node((3, 2.5), "c", name: "c-bdd-lr")
    bdd-decision-node((4, 2.5), "c", name: "c-bdd-rl")
    bdd-decision-node((6, 2.5), "c", name: "c-bdd-rr")

    // Only path a=1,b=0,c=0 leads to 1
    bdd-terminal-node((2, 1), "0", name: "zero-bdd")
    bdd-terminal-node((5, 1), "1", name: "one-bdd")

    // Simplified edges
    line((3.2, 5.1), (2.3, 4.4), stroke: (dash: "dashed", paint: colors.line, thickness: 1pt))
    line((3.8, 5.1), (4.7, 4.4), stroke: 1pt + colors.line)

    content((3.5, 0.3), text(size: 0.7em, fill: colors.text-muted)[Many nodes for sparse set])

    // ZDD: same set, much simpler
    bdd-decision-node((9.5, 5.5), "a", name: "a-zdd")
    bdd-terminal-node((8, 4), "0", name: "zero-zdd-l")
    bdd-terminal-node((11, 4), "1", name: "one-zdd")

    bdd-low-edge("a-zdd", "zero-zdd-l")
    bdd-high-edge("a-zdd", "one-zdd")

    content((9.5, 0.3), text(size: 0.7em, fill: colors.success)[Nodes for b,c suppressed!])

    // Arrow showing the same set
    content((6.5, 3.5), align(center)[
      #set text(size: 0.8em)
      Same set:\
      ${{a}}$
    ])
  }),
  caption: [For the set family ${{a}}$ over universe ${a,b,c}$: BDD needs nodes for all variables; ZDD only needs one.],
)

=== When to Use ZDDs

#comparison-table(
  [*Use Case*],
  [*BDD*],
  [*ZDD*],
  [Dense Boolean functions],
  [Excellent],
  [Poor],
  [Sparse set families],
  [Poor],
  [Excellent],
  [Combinatorial enumeration],
  [Moderate],
  [Excellent],
  [Graph problems (cliques, paths)],
  [Moderate],
  [Excellent],
  [Circuit verification],
  [Excellent],
  [Moderate],
)

#insight-box[
  ZDDs shine in problems where you're enumerating *sets of things* --- solutions to combinatorial problems, satisfying assignments, graph substructures.
  Knuth dedicated an entire section of TAOCP Volume 4B to ZDDs.
]

== Algebraic Decision Diagrams (ADDs)

ADDs (also called MTBDDs --- Multi-Terminal BDDs) generalize BDDs to functions with arbitrary terminal values.

#definition(title: "Algebraic Decision Diagram")[
  An *ADD* represents functions $f : BB^n -> D$ where $D$ is any set.
  Common choices:
  - $D = RR$ (real numbers) for probabilities, costs
  - $D = ZZ$ (integers) for counts
  - $D = {0, 1, ..., k}$ for multi-valued logic
]

#figure(
  cetz.canvas(length: 1cm, {
    import cetz.draw: *

    content((6, 7), text(weight: "bold", size: 1em)[ADD Example: Probability Function])

    // ADD for P(rain|cloud, wind)
    bdd-decision-node((6, 5.5), "cloud", name: "cloud")

    bdd-decision-node((3.5, 4), "wind", name: "wind-l")
    bdd-decision-node((8.5, 4), "wind", name: "wind-r")

    // Multiple terminal values
    rect(
      (1.5, 2),
      (2.5, 2.8),
      fill: colors.box-warning.lighten(30%),
      stroke: 1pt + colors.warning.lighten(20%),
      radius: 3pt,
    )
    content((2, 2.4), text(size: 0.8em)[0.1])

    rect(
      (4, 2),
      (5, 2.8),
      fill: colors.box-warning.lighten(30%),
      stroke: 1pt + colors.warning.lighten(20%),
      radius: 3pt,
    )
    content((4.5, 2.4), text(size: 0.8em)[0.3])

    rect(
      (7, 2),
      (8, 2.8),
      fill: colors.box-warning.lighten(30%),
      stroke: 1pt + colors.warning.lighten(20%),
      radius: 3pt,
    )
    content((7.5, 2.4), text(size: 0.8em)[0.5])

    rect(
      (9.5, 2),
      (10.5, 2.8),
      fill: colors.box-warning.lighten(30%),
      stroke: 1pt + colors.warning.lighten(20%),
      radius: 3pt,
    )
    content((10, 2.4), text(size: 0.8em)[0.9])

    // Edges
    bdd-low-edge("cloud", "wind-l")
    bdd-high-edge("cloud", "wind-r")

    line((3.2, 3.6), (2.2, 2.8), stroke: (dash: "dashed", paint: colors.line, thickness: 1pt))
    line((3.8, 3.6), (4.3, 2.8), stroke: 1pt + colors.line)
    line((8.2, 3.6), (7.7, 2.8), stroke: (dash: "dashed", paint: colors.line, thickness: 1pt))
    line((8.8, 3.6), (9.8, 2.8), stroke: 1pt + colors.line)

    // Legend
    content((6, 1), align(center)[
      #set text(size: 0.8em)
      $P("rain" | "cloud", "wind")$: probability depends on weather conditions
    ])
  }),
  caption: [An ADD representing probability of rain given cloud cover and wind conditions.],
)

=== Applications of ADDs

- *Probabilistic model checking*: Represent transition probabilities
- *Cost functions*: Assign costs to state combinations
- *Reward structures*: Accumulate rewards over paths
- *Matrix operations*: Sparse matrix-vector multiplication

```rust
// Conceptual ADD operations
fn add_value(&self, f: AddRef, g: AddRef) -> AddRef {
    // Terminal case: add numeric values
    // Recursive case: like BDD Apply
}

fn max_value(&self, f: AddRef, g: AddRef) -> AddRef {
    // Take maximum at terminals
}
```

== Edge-Valued BDDs (EVBDDs)

EVBDDs put numeric values on *edges* rather than at terminals.
This can be more compact for certain functions.

#definition(title: "Edge-Valued BDD")[
  An *EVBDD* has:
  - A single terminal node (value 0)
  - Numeric weights on each edge
  - Function value = sum (or product) of edge weights on path

  This is particularly compact for linear arithmetic functions.
]

#figure(
  cetz.canvas(length: 1cm, {
    import cetz.draw: *

    content((6, 6.5), text(weight: "bold", size: 1em)[EVBDD for $f = 2x + 3y$])

    bdd-decision-node((6, 5), "x", name: "x-ev")
    bdd-decision-node((6, 3), "y", name: "y-ev")
    bdd-terminal-node((6, 1.2), "0", name: "zero-ev")

    // Edges with values
    line((5.6, 4.6), (5.6, 3.4), stroke: (dash: "dashed", paint: colors.line, thickness: 1.5pt))
    content((5, 4), text(size: 0.8em, fill: colors.primary)[+0])

    line((6.4, 4.6), (6.4, 3.4), stroke: 1.5pt + colors.line)
    content((7, 4), text(size: 0.8em, fill: colors.primary)[+2])

    line((5.6, 2.6), (5.6, 1.6), stroke: (dash: "dashed", paint: colors.line, thickness: 1.5pt))
    content((5, 2), text(size: 0.8em, fill: colors.primary)[+0])

    line((6.4, 2.6), (6.4, 1.6), stroke: 1.5pt + colors.line)
    content((7, 2), text(size: 0.8em, fill: colors.primary)[+3])

    // Example computation
    content((10, 4), align(left)[
      #set text(size: 0.8em)
      Example: $x=1, y=1$\
      Path: $+2 +3 = 5$ ✓\
      $(2 dot 1 + 3 dot 1 = 5)$
    ])
  }),
  caption: [EVBDD encodes $2x + 3y$ with edge weights; only one terminal needed.],
)

== Free BDDs (FBDDs)

Free BDDs relax the variable ordering constraint:

#definition(title: "Free BDD")[
  In an *FBDD* (Free BDD), each *path* can use a different variable ordering.
  The only constraint: each variable appears *at most once* per path.

  FBDDs are also called *read-once branching programs*.
]

#comparison-table(
  [*Property*],
  [*ROBDD*],
  [*FBDD*],
  [Ordering],
  [Global (same for all paths)],
  [Per-path (can vary)],
  [Canonicity],
  [Yes (given ordering)],
  [No],
  [Compactness],
  [Depends on ordering],
  [Always at least as good],
  [Operations],
  [Efficient (polynomial)],
  [Can be expensive],
  [Equivalence check],
  [$O(1)$],
  [coNP-complete],
)

#warning-box(title: "The Price of Freedom")[
  FBDDs can be exponentially smaller than any ROBDD, but:
  - They're *not canonical* --- equivalence checking is hard
  - Operations like AND can be expensive
  - Most BDD libraries don't support them

  FBDDs are mainly of theoretical interest and for specific one-shot computations.
]

== Choosing the Right Variant

#insight-box[
  The best variant depends on your problem:
  - *Verification/synthesis*: ROBDD (canonical, efficient operations)
  - *Combinatorial enumeration*: ZDD (sparse sets)
  - *Probabilistic reasoning*: ADD/MTBDD (numeric terminals)
  - *Arithmetic functions*: EVBDD (edge values)

  `bdd-rs` focuses on ROBDDs with complement edges --- the sweet spot for most verification tasks.
]
