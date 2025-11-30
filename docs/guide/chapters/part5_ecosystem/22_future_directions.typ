#import "../../theme.typ": *

= Future Directions <ch-future-directions>

BDDs have been around for four decades, yet the field is far from stagnant.
Researchers continue to push boundaries: scaling to larger problems, exploiting modern hardware, and finding unexpected applications in machine learning and quantum computing.

This chapter surveys the frontier --- where BDD research is headed and what new capabilities may emerge.

== Parallelism and Distribution

Modern CPUs have dozens of cores; servers have hundreds.
Can BDDs exploit this parallelism, or are they inherently sequential?

#figure(
  cetz.canvas(length: 1cm, {
    import cetz.draw: *

    content((6, 7), text(weight: "bold", size: 1em)[Parallel BDD Challenges])

    // Shared state problem
    rect(
      (0.5, 3.5),
      (5, 6.5),
      fill: colors.box-warning.lighten(40%),
      stroke: 1pt + colors.warning.lighten(20%),
      radius: 4pt,
    )
    content((2.75, 6), text(size: 0.8em, weight: "semibold")[Shared State Challenge])

    rect((1, 4), (4.5, 5.5), fill: colors.bg-code, stroke: 0.5pt + colors.line, radius: 2pt, name: "ut")
    content((2.75, 5.1), text(size: 0.7em)[Unique Table])
    content((2.75, 4.5), text(size: 0.7em, fill: colors.text-muted)[All threads access])

    // Threads pointing to unique table
    for i in range(3) {
      let x = 1.5 + i * 1.2
      content((x, 3.2), text(size: 0.7em)[T#str(i + 1)])
      line((x, 3.5), (2.75, 3.9), stroke: 0.5pt + colors.line)
    }

    // Solutions
    rect(
      (6, 3.5),
      (11, 6.5),
      fill: colors.box-example.lighten(40%),
      stroke: 1pt + colors.success.lighten(20%),
      radius: 4pt,
    )
    content((8.5, 6), text(size: 0.8em, weight: "semibold")[Approaches])

    content((8.5, 5.2), text(size: 0.8em)[• Lock-free hash tables (Sylvan)])
    content((8.5, 4.6), text(size: 0.8em)[• Work-stealing schedulers])
    content((8.5, 4), text(size: 0.8em)[• Distributed memory (MPI)])
  }),
  caption: [Parallel BDD operations must coordinate access to shared data structures.],
)

#info-box(title: "Parallelism Research Frontiers")[
  - *GPU acceleration*: BDD traversal is irregular, challenging for GPUs
  - *FPGA implementation*: Custom hardware for Apply operations
  - *Distributed BDDs*: Partitioning across cluster nodes
  - *Speculative execution*: Compute both branches, discard unused
]

== Integration with Machine Learning

BDDs meet neural networks in surprising ways:

#example-box(title: "BDDs for Explainable AI")[
  A neural network classifies images, but *why* did it decide "cat"?

  Approach: Compile the (simplified) decision boundary into a BDD.
  The BDD reveals:
  - Which input features matter
  - What combinations trigger each output
  - Minimal explanations for decisions
]

#figure(
  cetz.canvas(length: 1cm, {
    import cetz.draw: *

    content((6, 7), text(weight: "bold", size: 1em)[Neural Network → BDD Extraction])

    // Neural network
    rect((0.5, 3), (3.5, 6.5), fill: colors.box-insight.lighten(30%), stroke: 1pt + colors.info, radius: 4pt)
    content((2, 6), text(size: 0.8em, weight: "semibold")[Neural Net])

    // Layers (simplified)
    for i in range(3) {
      for j in range(3) {
        circle((1.2 + i * 0.8, 3.7 + j * 0.7), radius: 0.15, fill: colors.bg-code, stroke: 0.5pt + colors.line)
      }
    }

    // Arrow
    content((5, 4.75), text(size: 1.5em)[→])
    content((5, 4), text(size: 0.7em, fill: colors.text-muted)[extract])

    // BDD
    rect(
      (6.5, 3),
      (10.5, 6.5),
      fill: colors.box-example.lighten(40%),
      stroke: 1pt + colors.success.lighten(20%),
      radius: 4pt,
    )
    content((8.5, 6), text(size: 0.8em, weight: "semibold")[BDD Explanation])

    // Simple BDD structure
    circle((8.5, 5), radius: 0.3, fill: colors.box-definition.lighten(40%), stroke: 1pt + colors.primary.lighten(20%))
    content((8.5, 5), text(size: 0.7em)[$x_1$])

    circle((7.5, 4), radius: 0.3, fill: colors.box-definition.lighten(40%), stroke: 1pt + colors.primary.lighten(20%))
    content((7.5, 4), text(size: 0.7em)[$x_3$])

    rect((9.2, 3.3), (9.8, 3.7), fill: colors.success.lighten(60%), stroke: 0.5pt + colors.success)
    content((9.5, 3.5), text(size: 0.7em)[1])

    rect((7.8, 3.3), (8.4, 3.7), fill: colors.error.lighten(60%), stroke: 0.5pt + colors.error)
    content((8.1, 3.5), text(size: 0.7em)[0])

    line((8.3, 4.75), (7.7, 4.25), stroke: 1pt + colors.text-muted)
    line((8.7, 4.75), (9.3, 4.25), stroke: 1pt + colors.line)
    line((7.3, 3.75), (8, 3.75), stroke: 1pt + colors.text-muted)
    line((7.7, 3.75), (9.3, 3.5), stroke: 1pt + colors.line)
  }),
  caption: [BDDs can explain neural network decisions by extracting symbolic decision rules.],
)

== Modern Hardware Considerations

Today's CPUs are complex — cache hierarchies, NUMA, branch prediction.
BDD libraries must adapt:

#comparison-table(
  [Hardware Feature],
  [BDD Impact],
  [Optimization],
  [L1/L2/L3 caches],
  [Node access patterns],
  [Cache-oblivious algorithms],
  [NUMA (multi-socket)],
  [Memory locality],
  [Per-socket unique tables],
  [Branch prediction],
  [If-then-else traversal],
  [Branchless operations],
  [Prefetching],
  [BDD traversal],
  [Explicit prefetch hints],
  [Persistent memory],
  [Large BDDs],
  [Memory-mapped structures],
)

#insight-box[
  A cache-aware BDD library can be 2-10× faster than a naive implementation on the same algorithm, purely from better memory access patterns.
]

== BDDs in Quantum Computing

Quantum computing introduces new uses for decision diagrams:

#figure(
  cetz.canvas(length: 1cm, {
    import cetz.draw: *

    content((6, 6.5), text(weight: "bold", size: 1em)[Decision Diagrams for Quantum])

    // Classical BDD
    rect(
      (0.5, 2),
      (4, 6),
      fill: colors.box-definition.lighten(40%),
      stroke: 1pt + colors.primary.lighten(20%),
      radius: 4pt,
    )
    content((2.25, 5.5), text(size: 0.8em, weight: "semibold")[Classical BDD])
    content((2.25, 4.8), text(size: 0.8em)[Terminals: 0, 1])
    content((2.25, 4.2), text(size: 0.8em)[Edges: Boolean])
    content((2.25, 3.5), text(size: 0.7em, fill: colors.text-muted)[Represents: $f: {0,1}^n -> {0,1}$])
    content((2.25, 2.5), text(size: 0.7em, fill: colors.primary)[Applications:])
    content((2.25, 2.1), text(size: 0.7em, fill: colors.text-muted)[Circuit synthesis])

    // Quantum DD
    rect((5, 2), (10.5, 6), fill: colors.box-insight.lighten(30%), stroke: 1pt + colors.info, radius: 4pt)
    content((7.75, 5.5), text(size: 0.8em, weight: "semibold")[Quantum DD])
    content((7.75, 4.8), text(size: 0.8em)[Terminals: complex])
    content((7.75, 4.2), text(size: 0.8em)[Edges: amplitudes])
    content((7.75, 3.5), text(size: 0.7em, fill: colors.text-muted)[Represents: $|psi〉 in CC^(2^n)$])
    content((7.75, 2.5), text(size: 0.7em, fill: colors.info)[Applications:])
    content((7.75, 2.1), text(size: 0.7em, fill: colors.text-muted)[Quantum simulation])
  }),
  caption: [Quantum decision diagrams extend BDDs to represent quantum states.],
)

#example-box(title: "Quantum Circuit Synthesis")[
  Given a quantum operation as a unitary matrix, find a circuit implementing it.

  BDD-based approaches:
  + Encode the transformation symbolically
  + Search for gate sequences using BDD operations
  + Verify equivalence with quantum decision diagrams

  This connects classical BDD techniques to quantum compilation.
]

== Incremental and Online Algorithms

What if the BDD changes continuously?

#algorithm(title: "Incremental BDD Update")[
  ```
  Traditional:
    constraints = [c1, c2, c3, ..., cn]
    bdd = AND(c1, c2, ..., cn)  // Build from scratch

  Incremental:
    bdd = c1
    bdd = AND(bdd, c2)  // Add constraint
    bdd = AND(bdd, c3)
    ...
    // Later: remove c2
    // Challenge: Can we "subtract" c2 efficiently?
  ```
]

#warning-box(title: "The Subtraction Problem")[
  BDD conjunction is irreversible — you can't efficiently "remove" a constraint.
  Workarounds:
  - Keep constraint BDDs separate, reconstruct on removal
  - Use "soft" constraints with indicator variables
  - Maintain incremental history for rollback
]

== Domain-Specific Extensions

BDDs have spawned many specialized variants:

#comparison-table(
  [Variant],
  [Extension],
  [Application],
  [ZBDD],
  [Zero-suppressed rules],
  [Combinatorics, SAT],
  [ADD],
  [Arbitrary terminal values],
  [Probabilistic inference],
  [EVBDD],
  [Edge-valued],
  [Arithmetic, probability],
  [MTBDD],
  [Multi-terminal],
  [Multi-valued logic],
  [SDD],
  [Sentential DD],
  [Knowledge compilation],
)

#insight-box[
  The BDD concept generalizes to *Decision Diagrams* — any data structure that:
  + Uses a fixed variable ordering
  + Applies reduction rules for canonicity
  + Enables efficient operations via dynamic programming
]

== The Enduring Role of BDDs

After 40 years, why do BDDs persist?

#figure(
  cetz.canvas(length: 1cm, {
    import cetz.draw: *

    content((6, 7), text(weight: "bold", size: 1em)[Why BDDs Endure])

    // Core properties
    rect(
      (1, 3),
      (5, 6.5),
      fill: colors.box-definition.lighten(40%),
      stroke: 2pt + colors.primary.lighten(20%),
      radius: 4pt,
    )
    content((3, 6), text(size: 0.9em, weight: "semibold", fill: colors.primary)[Unique Properties])

    content((3, 5.2), text(size: 0.8em)[✓ Canonicity])
    content((3, 4.6), text(size: 0.8em)[✓ Polynomial equality check])
    content((3, 4), text(size: 0.8em)[✓ Efficient operations])
    content((3, 3.4), text(size: 0.8em)[✓ Compact for structure])

    // Integration
    rect(
      (6, 3),
      (11, 6.5),
      fill: colors.box-example.lighten(40%),
      stroke: 1pt + colors.success.lighten(20%),
      radius: 4pt,
    )
    content((8.5, 6), text(size: 0.9em, weight: "semibold", fill: colors.success)[Modern Integration])

    content((8.5, 5.2), text(size: 0.8em)[• SAT solver preprocessing])
    content((8.5, 4.6), text(size: 0.8em)[• SMT theory solving])
    content((8.5, 4), text(size: 0.8em)[• Hardware synthesis])
    content((8.5, 3.4), text(size: 0.8em)[• ML interpretability])
  }),
  caption: [BDDs offer unique properties that complement modern techniques.],
)

#info-box(title: "The Future: Integration, Not Replacement")[
  BDDs won't replace SAT solvers or neural networks.
  But they fill a unique niche:

  - *SAT* finds one solution — *BDDs* represent all solutions
  - *Neural nets* approximate — *BDDs* are exact
  - *SMT* reasons about theories — *BDDs* provide Boolean backbone

  The future is *hybrid* systems combining the strengths of each approach.
]

#insight-box[
  *For the practitioner*: BDDs are a power tool.
  Like a good compiler or database, they solve a class of problems so well that reinventing them is rarely worthwhile.

  *For the researcher*: BDDs are a living field.
  Parallelism, quantum, ML integration — there's still much to discover.

  *For the student*: BDDs teach fundamentals.
  Canonical forms, dynamic programming, memory management — skills that transfer everywhere.
]
