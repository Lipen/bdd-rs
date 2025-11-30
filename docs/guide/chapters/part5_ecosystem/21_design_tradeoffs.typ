#import "../../theme.typ": *

= Design Trade-offs <ch-design-tradeoffs>

Building a BDD library is an exercise in trade-offs.
Every decision --- how to store nodes, when to garbage collect, whether to cache --- trades off between competing concerns: speed vs. memory, simplicity vs. features, safety vs. flexibility.

This chapter dissects the key engineering choices, explaining why reasonable libraries make radically different decisions.

== Memory vs. Time

The fundamental trade-off: *cache more* to avoid recomputation, or *compute more* to save memory.

#figure(
  cetz.canvas(length: 1cm, {
    import cetz.draw: *

    content((6, 7), text(weight: "bold", size: 1em)[Memory-Time Trade-off])

    // Axes
    line((1.5, 1.5), (1.5, 6), stroke: 1pt + colors.line, mark: (end: ">"))
    line((1.5, 1.5), (10.5, 1.5), stroke: 1pt + colors.line, mark: (end: ">"))
    content((0.8, 6), text(size: 0.8em)[Time])
    content((10.5, 1), text(size: 0.8em)[Memory])

    // Curve
    bezier((2, 5.5), (5, 2.2), (3, 2.5), stroke: 2pt + colors.primary)
    bezier((5, 2.2), (10, 2), (7, 2), stroke: 2pt + colors.primary)

    // Points
    circle((2.5, 4), radius: 0.15, fill: colors.warning, stroke: 1pt + colors.warning.darken(20%))
    content((2.5, 4.7), text(size: 0.7em, fill: colors.warning)[Small cache])

    circle((5, 2.2), radius: 0.15, fill: colors.success, stroke: 1pt + colors.success.darken(20%))
    content((5, 1.5), text(size: 0.7em, fill: colors.success)[Sweet spot])

    circle((8, 2.1), radius: 0.15, fill: colors.info, stroke: 1pt + colors.info.darken(20%))
    content((8.5, 2.7), text(size: 0.7em, fill: colors.info)[Diminishing returns])

    // Annotations
    content((6.5, 5), align(left)[
      #set text(size: 0.7em)
      More cache →\
      Fewer recomputations\
      But: Memory pressure
    ])
  }),
  caption: [Increasing cache size improves performance up to a point, then provides diminishing returns.],
)

#insight-box[
  The "sweet spot" depends on:
  - *Working set*: How many operations are repeated?
  - *Available memory*: How much can you afford?
  - *Access patterns*: Temporal locality matters

  Most libraries default to generous caching --- memory is cheaper than time.
]

== Node Representation Choices

How do you store BDD nodes in memory?
This low-level decision affects every operation.

#comparison-table(
  [Approach],
  [Pros],
  [Cons],
  [Pointer-based],
  [Direct access, familiar],
  [64-bit overhead, GC complexity],
  [Index-based],
  [Compact (32-bit)],
  [Extra indirection],
  [Array-of-structs],
  [Cache-friendly traversal],
  [Fragmentation on deletion],
  [Struct-of-arrays],
  [SIMD potential],
  [Scattered access patterns],
)

#figure(
  cetz.canvas(length: 1cm, {
    import cetz.draw: *

    content((6, 7), text(weight: "bold", size: 1em)[Node Layout Strategies])

    // Array of Structs
    content((3, 6), text(size: 0.8em, weight: "semibold")[Array of Structs])

    for i in range(3) {
      let x = 1 + i * 2
      rect(
        (x, 4),
        (x + 1.8, 5.5),
        fill: colors.box-definition.lighten(40%),
        stroke: 1pt + colors.primary.lighten(20%),
        radius: 2pt,
      )
      content((x + 0.9, 5.1), text(size: 0.7em)[var])
      content((x + 0.9, 4.7), text(size: 0.7em)[lo])
      content((x + 0.9, 4.3), text(size: 0.7em)[hi])
    }

    // Struct of Arrays
    content((9, 6), text(size: 0.8em, weight: "semibold")[Struct of Arrays])

    rect(
      (7.5, 5),
      (10.5, 5.5),
      fill: colors.box-example.lighten(40%),
      stroke: 1pt + colors.success.lighten(20%),
      radius: 2pt,
    )
    content((9, 5.25), text(size: 0.7em)[vars: 1, 2, 3, ...])

    rect((7.5, 4.3), (10.5, 4.8), fill: colors.box-insight.lighten(30%), stroke: 1pt + colors.info, radius: 2pt)
    content((9, 4.55), text(size: 0.7em)[lows: 4, 0, 2, ...])

    rect(
      (7.5, 3.6),
      (10.5, 4.1),
      fill: colors.box-warning.lighten(40%),
      stroke: 1pt + colors.warning.lighten(20%),
      radius: 2pt,
    )
    content((9, 3.85), text(size: 0.7em)[highs: 5, 3, 6, ...])

    // bdd-rs choice
    rect((3.5, 1.5), (8.5, 3), fill: colors.bg-code.lighten(20%), stroke: 1.5pt + colors.primary, radius: 4pt)
    content((6, 2.6), text(size: 0.8em, weight: "semibold")[bdd-rs: Array of Structs])
    content((6, 2), text(size: 0.7em, fill: colors.text-muted)[Simple, cache-friendly, index-based])
  }),
  caption: [Different memory layouts trade locality for flexibility.],
)

== Complement Edge Trade-offs

Complement edges provide significant benefits but add complexity:

#comparison-table(
  [Aspect],
  [Without Complements],
  [With Complements],
  [Node count],
  [Baseline],
  [Up to 50% fewer],
  [Negation],
  [$O(n)$ copy],
  [$O(1)$ flip bit],
  [Canonicity],
  [Simple],
  [Normalization rules required],
  [Algorithm complexity],
  [Straightforward],
  [Extra edge-case handling],
  [Memory per node],
  [Baseline],
  [Same or less total],
)

#example-box(title: "The Complement Edge Payoff")[
  For symmetric functions like XOR, complement edges can reduce node count dramatically.
  The XOR of 10 variables:
  - Without complements: ~2000 nodes
  - With complements: ~10 nodes

  The normalization complexity is worth it for the space savings.
]

== Unique Table Design

The unique table is the heart of any BDD library --- every node lookup goes through it.

#figure(
  cetz.canvas(length: 1cm, {
    import cetz.draw: *

    content((6, 7.5), text(weight: "bold", size: 1em)[Unique Table Approaches])

    // Global table
    rect(
      (0.5, 4),
      (4.5, 7),
      fill: colors.box-definition.lighten(40%),
      stroke: 1pt + colors.primary.lighten(20%),
      radius: 4pt,
    )
    content((2.5, 6.5), text(size: 0.8em, weight: "semibold")[Global Table])

    rect((1, 4.5), (4, 6), fill: colors.bg-code, stroke: 0.5pt + colors.line, radius: 2pt)
    content((2.5, 5.5), text(size: 0.7em)[All nodes mixed])
    content((2.5, 5), text(size: 0.7em)[One hash table])

    content((2.5, 3.3), align(center)[
      #set text(size: 0.7em)
      + Simple\
      − Hot during GC
    ])

    // Per-level tables
    rect((6, 4), (11, 7), fill: colors.box-example.lighten(40%), stroke: 1pt + colors.success.lighten(20%), radius: 4pt)
    content((8.5, 6.5), text(size: 0.8em, weight: "semibold")[Per-Level Tables])

    for i in range(3) {
      let x = 6.5 + i * 1.5
      rect((x, 4.5), (x + 1.2, 6), fill: colors.bg-code, stroke: 0.5pt + colors.line, radius: 2pt)
      content((x + 0.6, 5.5), text(size: 0.7em)[L#str(i + 1)])
    }

    content((8.5, 3.3), align(center)[
      #set text(size: 0.7em)
      + Reordering friendly\
      + Level-local GC
    ])

    // bdd-rs indicator
    line((8.5, 3.9), (8.5, 2.5), stroke: 1.5pt + colors.primary, mark: (end: ">"))
    content((8.5, 2), text(size: 0.8em, fill: colors.primary, weight: "semibold")[bdd-rs choice])
  }),
  caption: [Per-level tables enable efficient variable reordering.],
)

#insight-box[
  Per-level (subtable) design enables:
  - *Local operations*: Only touch affected levels during reordering
  - *Incremental GC*: Collect one level at a time
  - *Better locality*: Nodes at same level accessed together
]

== Cache Strategies

Operation caches trade memory for avoiding recomputation:

#algorithm(title: "Cache Design Decisions")[
  ```
  Key decisions:
  1. Single cache vs. per-operation caches
     - Single: simpler, possible conflicts
     - Multiple: more memory, fewer conflicts

  2. Cache associativity
     - Direct-mapped: simple, high conflict rate
     - Set-associative: balance
     - Fully-associative: complex, lowest conflicts

  3. Eviction policy
     - Random: simple, works well in practice
     - LRU: optimal but expensive
     - FIFO: simple, reasonable

  4. Persistence across GC
     - Clear cache: safe but lose warmth
     - Update cache: complex, preserves work
  ```
]

== Garbage Collection Approaches

BDD libraries must reclaim memory from dead nodes:

#comparison-table(
  [Approach],
  [Pros],
  [Cons],
  [Manual (user calls)],
  [Predictable, explicit control],
  [Burden on user],
  [Reference counting],
  [Immediate reclamation],
  [Cycle issues, overhead per op],
  [Mark-and-sweep],
  [No per-op overhead],
  [Pause time, needs root tracking],
  [Incremental/concurrent],
  [Low latency],
  [Complex implementation],
)

#figure(
  cetz.canvas(length: 1cm, {
    import cetz.draw: *

    content((6, 6.5), text(weight: "bold", size: 1em)[GC Strategy Comparison])

    // Reference counting
    rect(
      (0.5, 3),
      (4, 6),
      fill: colors.box-warning.lighten(40%),
      stroke: 1pt + colors.warning.lighten(20%),
      radius: 4pt,
    )
    content((2.25, 5.5), text(size: 0.8em, weight: "semibold")[Ref Counting])
    content((2.25, 4.8), text(size: 0.7em)[CUDD, BuDDy])
    content((2.25, 4.1), text(size: 0.7em, fill: colors.text-muted)[Increment/decrement])
    content((2.25, 3.5), text(size: 0.7em, fill: colors.text-muted)[on every operation])

    // Mark and sweep
    rect(
      (5, 3),
      (8.5, 6),
      fill: colors.box-example.lighten(40%),
      stroke: 1pt + colors.success.lighten(20%),
      radius: 4pt,
    )
    content((6.75, 5.5), text(size: 0.8em, weight: "semibold")[Mark-Sweep])
    content((6.75, 4.8), text(size: 0.7em)[bdd-rs])
    content((6.75, 4.1), text(size: 0.7em, fill: colors.text-muted)[No per-op overhead])
    content((6.75, 3.5), text(size: 0.7em, fill: colors.text-muted)[Periodic pause])

    // Lock-free
    rect((9.5, 3), (11.5, 6), fill: colors.box-insight.lighten(30%), stroke: 1pt + colors.info, radius: 4pt)
    content((10.5, 5.5), text(size: 0.8em, weight: "semibold")[Lock-free])
    content((10.5, 4.8), text(size: 0.7em)[Sylvan])
    content((10.5, 4.1), text(size: 0.7em, fill: colors.text-muted)[Parallel-])
    content((10.5, 3.5), text(size: 0.7em, fill: colors.text-muted)[safe])
  }),
  caption: [Different GC strategies suit different use cases.],
)

== API Design Philosophy

The public API shapes how users interact with your library:

#comparison-table(
  [Philosophy],
  [Example],
  [Trade-off],
  [Maximize safety],
  [Rust's `Ref` type],
  [May limit advanced use],
  [Maximize flexibility],
  [CUDD's raw pointers],
  [User can shoot themselves],
  [Hide internals],
  [Opaque handles],
  [Limits optimization opportunities],
  [Expose internals],
  [Public node structure],
  [Hard to change later],
)

#example-box(title: "bdd-rs API Philosophy")[
  ```rust
  // Safe: Ref is Copy, no manual memory management
  let f = bdd.and(x, y);  // Returns Ref, not raw pointer

  // Explicit: GC is manual, user controls timing
  bdd.gc();  // User decides when

  // Transparent: Can inspect internals if needed
  let node = bdd.get_node(f);  // Access node data
  ```

  The goal: *safe by default*, *powerful when needed*.
]

== The Unifying Theme

Every design decision involves trade-offs.
The "right" choice depends on your priorities:

#info-box(title: "Design Priority Matrix")[
  - *Performance-critical applications*: Optimize for speed, accept complexity
  - *Research prototypes*: Optimize for simplicity, accept slower speed
  - *Production systems*: Optimize for reliability, accept some inefficiency
  - *Learning/teaching*: Optimize for clarity, accept naive implementations

  `bdd-rs` prioritizes *safety* and *clarity*, making it ideal for learning and correct-by-construction implementations.
]
