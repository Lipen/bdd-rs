#import "../../theme.typ": *

= Algebraic Domain Combinations <ch-domain-combinations>

#reading-path(path: "advanced")

In the previous chapters, we explored individual abstract domains like Intervals and Signs.
However, real-world analysis often requires tracking multiple properties simultaneously or capturing relationships between them.
This chapter formalizes the algebra of *combining* abstract domains.

We will explore:
- *Direct Products*: Running multiple analyses in parallel.
- *Reduced Products*: Enabling domains to exchange information.
- *Trace Partitioning*: The theoretical foundation for path sensitivity.
- *Relational Domains*: Tracking correlations between variables.

== The Direct Product

The simplest way to combine two domains $A$ and $B$ is the *direct product*.
This corresponds to running two independent analyses and pairing their results.

#definition(title: "Direct Product Domain")[
  Given two abstract domains $A$ and $B$, their direct product $A times B$ is defined as:
  - *Elements*: Pairs $(a, b)$ where $a in A$ and $b in B$.
  - *Ordering*: $(a_1, b_1) lle (a_2, b_2) <==> a_1 lle_A a_2 and b_1 lle_B b_2$.
  - *Join*: $(a_1, b_1) ljoin (a_2, b_2) = (a_1 ljoin_A a_2, b_1 ljoin_B b_2)$.
  - *Meet*: $(a_1, b_1) lmeet (a_2, b_2) = (a_1 lmeet_A a_2, b_1 lmeet_B b_2)$.
  - *Concretization*: $gamma((a, b)) = gamma_A (a) inter gamma_B (b)$.
]

The direct product allows us to answer questions that neither domain could answer alone, but it does not allow the domains to *help* each other.

#example-box(title: "Loss of Precision in Direct Product")[
  Consider the product of *Signs* and *Parity* domains.
  Let $x$ be "Positive" in Signs and "Even" in Parity.
  State: $(+, "Even")$.

  Now, assume we execute `x = x / 2`.
  - Signs: Positive / 2 $->$ Positive.
  - Parity: Even / 2 $->$ Top (could be even or odd).
  - Result: $(+, top)$.

  We lost the information that $x$ was even!
  If we knew $x=6$, then $x/2=3$ (odd).
  The domains operated independently and failed to refine the result.
]

== The Reduced Product

The *reduced product* improves upon the direct product by allowing information exchange (reduction) between domains.

#definition(title: "Reduction Operator")[
  A reduction operator $rho: A times B -> A times B$ transforms a pair $(a, b)$ into a more precise pair $(a', b')$ such that:
  + $gamma(a', b') = gamma(a, b)$ (Soundness: no concrete states lost).
  + $(a', b') lle (a, b)$ (Improvement: result is smaller or equal).
]

The goal of reduction is to propagate constraints discovered by one domain to the other.

#example-box(title: "Reduction Example")[
  *Intervals* $times$ *Congruence*.

  State: $x in [10, 12]$ AND $x equiv 0 mod 5$.

  - Intervals alone: $10, 11, 12$.
  - Congruence alone: $..., 5, 10, 15, ...$.
  - Intersection: ${10}$.

  *Reduction*: The congruence domain tells the interval domain: "The only valid value in $[10, 12]$ is $10$."
  Refined Interval: $[10, 10]$.

  The interval domain tells the congruence domain: "The value is exactly 10."
  Refined Congruence: $x equiv 0 mod 10$ (if supported).
]

#figure(
  caption: [Direct vs. Reduced Product: Intervals $times$ Congruence],
  cetz.canvas({
    import cetz.draw: *

    // --- Styles & Helpers ---
    let style-box = (fill: colors.bg-code, stroke: colors.primary + 1pt, radius: 0.2)
    let style-arrow = (mark: (end: ">"), stroke: colors.text-light + 0.8pt)

    let draw-state(pos, name, body, fill: colors.bg-code, width: 4, height: 1.2) = {
      let (x, y) = pos
      let w = width / 2
      let h = height / 2
      rect((x - w, y - h), (x + w, y + h), name: name, fill: fill, stroke: colors.primary + 1pt, radius: 0.2)
      content(pos, body)
    }

    let draw-arrow(from, to, label: none) = {
      line(from, to, ..style-arrow, name: "arrow")
      if label != none {
        content("arrow.mid", anchor: "west", padding: 0.1, label)
      }
    }

    // --- Layout Constants ---
    let x-left = -4
    let x-right = 4
    let y-top = 3
    let y-bot = 0

    // --- Direct Product ---
    content((x-left, y-top + 1.5), text(weight: "bold")[Direct Product])

    // Initial State
    draw-state((x-left, y-top), "d_init", [${[10, 12], 0 thick (mod 5)}$])

    // Result (Independent)
    draw-state(
      (x-left, y-bot),
      "d_res",
      text(0.8em)[Interval: $10, 11, 12$ \ Congruence: $..., 5, 10, 15, ...$],
      fill: colors.warning.lighten(80%),
      height: 1.5,
    )

    // Operation
    draw-arrow("d_init.south", "d_res.north", label: text(size: 0.8em)[Interpret])

    content((x-left, y-bot - 1.2), text(size: 0.8em, fill: colors.error)[No refinement!])

    // --- Reduced Product ---
    content((x-right, y-top + 1.5), text(weight: "bold")[Reduced Product])

    // Initial State
    draw-state((x-right, y-top), "r_init", [${[10, 12], 0 thick (mod 5)}$])

    // Result (Refined)
    draw-state(
      (x-right, y-bot),
      "r_res",
      [${[10, 10], 0 thick (mod 10)}$],
      fill: colors.success.lighten(80%),
      height: 1.5,
    )

    // Reduction Step
    draw-arrow("r_init.south", "r_res.north", label: text(size: 0.8em, fill: colors.accent)[Reduce $rho$])

    content((x-right, y-bot - 1.2), text(size: 0.8em, fill: colors.success)[Precision gained!])

    // Explanation arrow
    line(
      "r_res.west",
      "d_res.east",
      stroke: (paint: colors.text-light, dash: "dashed"),
      mark: (start: ">", end: ">", stroke: (dash: "solid")),
    )
    content((0, y-bot + 0.5), text(size: 0.8em)[$10 in [10, 12]$ is $0 thick (mod 5)$])
  }),
)

In practice, computing the *optimal* reduction (the Granger-Cousot reduction) can be expensive.
Most analyzers use *local iterations* or specific reduction heuristics (e.g., "Signs refines Intervals").

== Trace Partitioning

*Trace partitioning* is a powerful technique to gain precision by distinguishing execution paths.
Instead of merging control flows immediately, we maintain separate abstract states for different history traces.

#definition(title: "Trace Partitioning Domain")[
  Given a set of trace tokens $T$ (representing control paths) and a domain $A$, the trace partitioning domain is the function space:
  $ A_T = T -> A $

  An element $f in A_T$ maps each trace $t in T$ to an abstract state $f(t)$.
  The concrete meaning is the union of states over all traces:
  $ gamma(f) = union.big_(t in T) gamma_A (f(t)) $
]

This is the theoretical foundation for *path-sensitive analysis*.
If $T$ represents the "current basic block" or "last branch taken", we get standard path sensitivity.
If $T$ represents "call stack", we get context sensitivity (interprocedural analysis).

#figure(
  caption: [Trace partitioning splits abstract states by path],

  cetz.canvas({
    import cetz.draw: *

    // --- Styles & Helpers ---
    let style-box = (fill: colors.bg-code, stroke: colors.primary + 1pt, radius: 0.2)
    let style-arrow = (mark: (end: ">", stroke: (dash: "solid")), stroke: colors.text-light + 0.8pt)

    let draw-state(pos, name, body, fill: colors.bg-code, stroke: colors.primary + 1pt, width: 2.5, height: 1) = {
      let (x, y) = pos
      let w = width / 2
      let h = height / 2
      rect((x - w, y - h), (x + w, y + h), name: name, fill: fill, stroke: stroke, radius: 0.2)
      content(pos, body)
    }

    // --- Layout Constants ---
    let y-split = 4
    let y-branch = 2
    let y-merge = 0
    let x-sep = 2

    // Control flow split
    circle((0, y-split), radius: 0.3, name: "split", fill: colors.bg-code, stroke: colors.primary + 1pt)
    content("split", [?])

    // Branches
    draw-state((-x-sep, y-branch), "s1", [$x in [0, 5]$], fill: colors.success.lighten(70%))
    draw-state((x-sep, y-branch), "s2", [$x in [6, 10]$], fill: colors.warning.lighten(70%))

    // Edges to branches
    line("split", "s1", ..style-arrow, name: "split-s1")
    content("split-s1", text(size: 8pt, fill: colors.success)[True], anchor: "south-east", padding: 0.2)

    line("split", "s2", ..style-arrow, name: "split-s2")
    content("split-s2", text(size: 8pt, fill: colors.warning)[False], anchor: "south-west", padding: 0.2)

    // Merge point (Partitioned)
    draw-state((0, y-merge), "merge", [${("T", [0, 5]), ("F", [6, 10])}$], width: 5)
    content((0, y-merge - 1), text(size: 9pt, fill: colors.text-light)[Kept separate!])

    // Edges to merge
    line("s1", "merge", ..style-arrow)
    line("s2", "merge", ..style-arrow)

    // Comparison with Merge
    let x-std = 6
    content((x-std, y-branch), text(weight: "bold")[Standard Merge:])
    draw-state((x-std, y-merge), "std", [$[0, 10]$], fill: colors.error.lighten(70%), stroke: colors.error + 1pt)
    content((x-std, y-merge - 1), text(size: 9pt, fill: colors.error)[Precision lost])

    // Arrow for standard merge comparison (conceptual)
    line((x-std, y-branch - 0.5), "std.north", ..style-arrow, stroke: (dash: "dashed"))
  }),
)

#info-box(title: "Partitioning vs. Disjunctive Completion")[
  Trace partitioning is a practical approximation of *disjunctive completion* (the power set domain $P(A)$).

  - $P(A)$ allows *arbitrary* disjunctions: $(x=1) or (x=5)$.
  - Trace partitioning allows disjunctions *aligned with control flow*: $("path"_1 and x=1) or ("path"_2 and x=5)$.

  This structure makes trace partitioning much more efficient than full disjunctive completion.
]

== Relational Domains

So far, we have discussed *non-relational* domains (like Intervals), which track properties of variables independently ($x in [a, b]$).
*Relational domains* track relationships *between* variables.

Common relational domains:
- *Octagons*: Constraints of the form $plus.minus x plus.minus y lle c$.
  Efficient ($O(n^3)$), good for array bounds checking ($i < n$).
- *Polyhedra*: Linear inequalities $sum a_i x_i lle c$.
  Very precise, but exponential complexity.
- *Equalities*: $x = y + c$.

#example-box(title: "Real-World Example: Consistency Check")[
  Consider a security check for user roles:

  ```rust
  // User is admin?
  if user_id == admin_id {
      // Must have admin role
      if role != "Admin" {
          error();
      }
  }
  ```

  - *Intervals*: Tracks range of `user_id` and `role` independently.
    Cannot capture the correlation "if user is admin, role must be Admin".
  - *Relational*: Tracks `user_id == admin_id => role == "Admin"`.
    Can prove that the `error()` is unreachable for consistent states.
]

== Widening in Product Domains

When combining domains, the widening operator must also be combined.
For a product $A times B$, the standard widening is component-wise:
$ (a_1, b_1) widen (a_2, b_2) = (a_1 widen_A a_2, b_1 widen_B b_2) $

However, this can be too aggressive.
*Delayed widening* or *widening with thresholds* is often necessary to prevent precision loss in one domain from destabilizing the other.

== Chapter Summary

- *Direct Product*: Combines domains independently.
- *Reduced Product*: Adds communication between domains to recover precision.
- *Trace Partitioning*: Distinguishes abstract states based on execution history (control flow).
- *Relational Domains*: Track correlations between variables ($x < y$).

In the next chapter, we will implement a powerful instance of these concepts: a *Reduced Product of BDDs (Trace Partitioning) and Abstract Domains*.
This "Killer Feature" uses BDDs to efficiently manage the trace partition $T$, enabling scalable path-sensitive analysis.
