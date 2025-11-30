#import "../../theme.typ": *

= Library Comparison <ch-library-comparison>

The BDD library ecosystem spans three decades of research and engineering.
From CUDD's 1996 release --- still the gold standard --- to modern parallel implementations, each library embodies different design philosophies.

Understanding this landscape helps you choose the right tool for your problem and appreciate where `bdd-rs` fits in the lineage.

== Landscape of BDD Libraries

#figure(
  cetz.canvas(length: 1cm, {
    import cetz.draw: *

    content((6, 8), text(weight: "bold", size: 1em)[BDD Library Evolution])

    // Timeline
    line((1, 1), (11, 1), stroke: 1.5pt + colors.line, mark: (end: ">"))
    content((11.5, 1), text(size: 0.7em)[Time])

    // Era markers
    for (x, label) in ((2, "1990s"), (5, "2000s"), (8, "2010s"), (10.5, "2020s")) {
      line((x, 0.8), (x, 1.2), stroke: 1pt + colors.line)
      content((x, 0.4), text(size: 0.7em, fill: colors.text-muted)[#label])
    }

    // Libraries
    // CUDD
    rect(
      (1.5, 2.5),
      (3.5, 4),
      fill: colors.box-definition.lighten(40%),
      stroke: 1.5pt + colors.primary.lighten(20%),
      radius: 4pt,
    )
    content((2.5, 3.5), text(size: 0.8em, weight: "semibold")[CUDD])
    content((2.5, 2.9), text(size: 0.7em, fill: colors.text-muted)[C · 1996])
    line((2.5, 2.4), (2.5, 1.3), stroke: 1pt + colors.primary.lighten(30%))

    // BuDDy
    rect(
      (3.5, 4.5),
      (5.5, 6),
      fill: colors.box-example.lighten(40%),
      stroke: 1pt + colors.success.lighten(20%),
      radius: 4pt,
    )
    content((4.5, 5.5), text(size: 0.8em, weight: "semibold")[BuDDy])
    content((4.5, 4.9), text(size: 0.7em, fill: colors.text-muted)[C++ · 1999])
    line((4.5, 4.4), (4.5, 1.3), stroke: 1pt + colors.success.lighten(30%))

    // JavaBDD
    rect(
      (5, 2.5),
      (7, 4),
      fill: colors.box-warning.lighten(40%),
      stroke: 1pt + colors.warning.lighten(20%),
      radius: 4pt,
    )
    content((6, 3.5), text(size: 0.8em, weight: "semibold")[JavaBDD])
    content((6, 2.9), text(size: 0.7em, fill: colors.text-muted)[Java · 2003])
    line((6, 2.4), (6, 1.3), stroke: 1pt + colors.warning.lighten(30%))

    // Sylvan
    rect((7.5, 4.5), (9.5, 6), fill: colors.box-insight.lighten(30%), stroke: 1pt + colors.info, radius: 4pt)
    content((8.5, 5.5), text(size: 0.8em, weight: "semibold")[Sylvan])
    content((8.5, 4.9), text(size: 0.7em, fill: colors.text-muted)[C · 2015])
    line((8.5, 4.4), (8.5, 1.3), stroke: 1pt + colors.info.lighten(30%))

    // bdd-rs
    rect((9, 2.5), (11, 4), fill: colors.box-algorithm.lighten(30%), stroke: 2pt + colors.primary, radius: 4pt)
    content((10, 3.5), text(size: 0.8em, weight: "semibold")[bdd-rs])
    content((10, 2.9), text(size: 0.7em, fill: colors.text-muted)[Rust · 2024])
    line((10, 2.4), (10, 1.3), stroke: 1pt + colors.primary)
  }),
  caption: [Major BDD libraries across three decades of development.],
)

== CUDD (Colorado University Decision Diagram)

CUDD is the *reference implementation* --- the library against which all others are measured.
Developed at the University of Colorado, Boulder, it has powered countless research projects and industrial tools.

#info-box(title: "CUDD at a Glance")[
  - *Language*: C (with C++ wrapper)
  - *Features*: BDDs, ZDDs, ADDs (Algebraic Decision Diagrams)
  - *Reordering*: Sifting, window permutation, simulated annealing
  - *Memory*: Reference counting with periodic garbage collection
  - *Status*: Mature, stable, widely used
]

=== Strengths

+ *Comprehensive*: Supports BDDs, ZDDs, and ADDs in one library
+ *Battle-tested*: Decades of use in research and industry
+ *Excellent reordering*: Dynamic variable reordering is well-tuned
+ *Rich API*: Every conceivable operation is available

=== Limitations

+ *C-style API*: Manual memory management, no type safety
+ *Single-threaded*: No built-in parallelism
+ *Complex setup*: Configuration can be tricky
+ *Documentation*: Comprehensive but dense

```c
// CUDD usage example
DdManager *manager = Cudd_Init(0, 0, CUDD_UNIQUE_SLOTS, CUDD_CACHE_SLOTS, 0);
DdNode *x = Cudd_bddIthVar(manager, 0);
DdNode *y = Cudd_bddIthVar(manager, 1);
DdNode *f = Cudd_bddAnd(manager, x, y);
Cudd_Ref(f);  // Must manually reference!
```

== BuDDy

BuDDy is the workhorse of many academic tools --- simpler than CUDD but still powerful.

#example-box(title: "BuDDy Philosophy")[
  BuDDy prioritizes *simplicity* and *ease of use*.
  The API is cleaner than CUDD's, with better C++ integration.
  It's the library of choice when you want something that "just works."
]

```cpp
// BuDDy usage example
bdd_init(1000000, 100000);  // nodes, cache
bdd_setvarnum(10);

bdd x = bdd_ithvar(0);
bdd y = bdd_ithvar(1);
bdd f = x & y;  // Operator overloading!
// Automatic reference counting
```

== Sylvan

Sylvan brings *parallelism* to BDD operations, exploiting multi-core processors.

#figure(
  cetz.canvas(length: 1cm, {
    import cetz.draw: *

    content((6, 6.5), text(weight: "bold", size: 1em)[Sylvan: Parallel BDD Operations])

    // Single-threaded
    rect(
      (0.5, 3),
      (4, 5.5),
      fill: colors.box-warning.lighten(50%),
      stroke: 1pt + colors.warning.lighten(20%),
      radius: 4pt,
    )
    content((2.25, 5), text(size: 0.8em, weight: "semibold")[Single-threaded])
    // Single-threaded
    rect(
      (0.5, 3),
      (4, 5.5),
      fill: colors.box-warning.lighten(50%),
      stroke: 1pt + colors.warning.lighten(20%),
      radius: 4pt,
    )
    content((2.25, 5), text(size: 0.8em, weight: "semibold")[Single-threaded])
    rect((1, 3.5), (3.5, 4.5), fill: colors.bg-code, stroke: 0.5pt + colors.line, radius: 2pt)
    content((2.25, 4), text(size: 0.8em)[Thread 1])

    // Sylvan parallel
    rect(
      (5.5, 2),
      (11, 5.5),
      fill: colors.box-example.lighten(40%),
      stroke: 1pt + colors.success.lighten(20%),
      radius: 4pt,
    )
    content((8.25, 5), text(size: 0.8em, weight: "semibold")[Sylvan (parallel)])

    for i in range(4) {
      let x = 6 + i * 1.2
      rect((x, 2.5), (x + 1, 4.5), fill: colors.box-insight.lighten(30%), stroke: 0.5pt + colors.info, radius: 2pt)
      content((x + 0.5, 3.5), text(size: 0.7em)[T#str(i + 1)])
    }

    // Speedup annotation
    content((8.25, 1.3), text(size: 0.8em, fill: colors.success)[Up to 4× speedup on 4 cores])
  }),
  caption: [Sylvan distributes BDD operations across multiple threads.],
)

#insight-box[
  Sylvan uses *work-stealing* parallelism: threads that finish early steal work from busy threads.
  The unique table and operation cache use lock-free data structures for thread safety.
]

#warning-box(title: "When Parallelism Helps")[
  Parallel BDD operations help most when:
  - BDDs are large (millions of nodes)
  - Operations are compute-bound (complex Apply)
  - Multiple cores are available

  For small BDDs, single-threaded libraries may actually be faster due to lower overhead.
]

== Comprehensive Comparison

#comparison-table(
  cols: 5,
  [Feature],
  [CUDD],
  [BuDDy],
  [Sylvan],
  [bdd-rs],
  [Language],
  [C],
  [C++],
  [C],
  [Rust],
  [Reordering],
  [#YES],
  [#YES],
  [#YES],
  [#PARTIAL],
  [Complement Edges],
  [#YES],
  [#YES],
  [#YES],
  [#YES],
  [Parallel],
  [#NO],
  [#NO],
  [#YES],
  [#NO],
  [ZDD Support],
  [#YES],
  [#NO],
  [#YES],
  [#NO],
  [ADD Support],
  [#YES],
  [#NO],
  [#NO],
  [#NO],
  [Memory Safety],
  [#NO],
  [#NO],
  [#NO],
  [#YES],
  [Reference Counting],
  [Manual],
  [Auto],
  [Lock-free],
  [Mark-sweep],
)

== bdd-rs: Rust-Native Design

`bdd-rs` takes a different approach: *memory safety first*, enabled by Rust's ownership model.

#example-box(title: "bdd-rs Philosophy")[
  - *Safe by default*: No undefined behavior, no memory leaks
  - *Ergonomic API*: Rust idioms, not C idioms
  - *Modern design*: Complement edges, level-based ordering
  - *Transparent*: Simple implementation you can understand
]

```rust
// bdd-rs usage
let bdd = Bdd::new();
let x = bdd.variable(1);
let y = bdd.variable(2);
let f = bdd.and(x, y);  // No manual reference counting!
// Drop automatically cleans up
```

=== What bdd-rs Does Well

+ *Memory safety*: Rust's type system prevents common bugs
+ *Clean API*: `Ref` handles are lightweight and copyable
+ *Explicit management*: Control when garbage collection happens
+ *Readable source*: Learn BDD internals by reading the code

=== Current Limitations

+ *No dynamic reordering* (yet): Manual ordering only
+ *Single-threaded*: No parallelism
+ *Fewer features*: No ZDDs, no ADDs
+ *Younger project*: Less battle-tested than CUDD

== Choosing a Library

#figure(
  cetz.canvas(length: 1cm, {
    import cetz.draw: *

    content((6, 7.5), text(weight: "bold", size: 1em)[Decision Guide: Which Library?])

    // Decision tree
    content((6, 6.5), text(size: 0.8em)[Need ZDDs/ADDs?], name: "q1")

    content((3, 5), text(size: 0.7em, fill: colors.success)[Yes], name: "y1")
    content((9, 5), text(size: 0.7em, fill: colors.warning)[No], name: "n1")

    line((6, 6.2), (3.5, 5.3), stroke: 1pt + colors.line)
    line((6, 6.2), (8.5, 5.3), stroke: 1pt + colors.line)

    rect(
      (1.5, 3.5),
      (4.5, 4.8),
      fill: colors.box-definition.lighten(40%),
      stroke: 1pt + colors.primary.lighten(20%),
      radius: 4pt,
    )
    content((3, 4.4), text(size: 0.8em, weight: "semibold")[CUDD])
    content((3, 3.8), text(size: 0.7em, fill: colors.text-muted)[Full-featured])

    content((9, 4.5), text(size: 0.8em)[Need parallelism?], name: "q2")

    content((7, 3), text(size: 0.7em, fill: colors.success)[Yes], name: "y2")
    content((11, 3), text(size: 0.7em, fill: colors.warning)[No], name: "n2")

    line((9, 4.2), (7.5, 3.3), stroke: 1pt + colors.line)
    line((9, 4.2), (10.5, 3.3), stroke: 1pt + colors.line)

    rect((5.5, 1.5), (8.5, 2.8), fill: colors.box-insight.lighten(30%), stroke: 1pt + colors.info, radius: 4pt)
    content((7, 2.4), text(size: 0.8em, weight: "semibold")[Sylvan])
    content((7, 1.8), text(size: 0.7em, fill: colors.text-muted)[Multi-core])

    content((11, 2), text(size: 0.8em)[Need safety?], name: "q3")

    line((11, 1.7), (10, 0.8), stroke: 1pt + colors.line)
    line((11, 1.7), (12, 0.8), stroke: 1pt + colors.line)

    content((10, 0.5), text(size: 0.7em)[bdd-rs])
    content((12, 0.5), text(size: 0.7em)[BuDDy])
  }),
  caption: [Choosing a BDD library based on your requirements.],
)

#info-box(title: "Recommendation Summary")[
  - *Research prototyping*: `bdd-rs` (safe, readable) or BuDDy (simple)
  - *Production systems*: CUDD (proven) or Sylvan (if parallel)
  - *Learning BDDs*: `bdd-rs` (clean implementation to study)
  - *Java projects*: JavaBDD (JNI wrapper around CUDD)
]
