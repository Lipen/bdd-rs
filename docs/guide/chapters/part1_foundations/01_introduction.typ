#import "../../theme.typ": *

= Introduction <ch-introduction>

Imagine you could represent any Boolean formula --- no matter how complex --- as a compact diagram where checking if two formulas are equivalent takes a single pointer comparison.
Where determining satisfiability requires examining just one node.
Where counting all solutions is a single traversal.

This is the promise of Binary Decision Diagrams.

Since their refinement in the 1980s, BDDs have become one of computer science's most elegant success stories.
They enabled Intel to verify microprocessors before fabrication, catching bugs that would have cost billions.
They power configuration tools that validate millions of product combinations in milliseconds.
They form the foundation of symbolic model checking --- a technique so impactful that it earned its inventors the Turing Award.

This chapter takes you on a journey from the fundamental challenge of Boolean reasoning to the elegant solution that BDDs provide.

== The Challenge of Boolean Reasoning

Boolean functions hide in plain sight.
Every `if` statement in your code.
Every logic gate in a processor.
Every constraint in a configuration system.
Every rule in a firewall policy.

The ubiquity of Boolean logic makes reasoning about it essential --- and surprisingly difficult.

=== A Deceptively Simple Question

Consider this innocent-looking question:

#example-box(title: "The Equivalence Puzzle")[
  Are these two formulas the same function?
  $ f = (a and b) or (a and c) or (b and c) $
  $ g = (a or b) and (a or c) and (b or c) $

  _Take a moment to think about it._

  With just three variables, you could check all $2^3 = 8$ input combinations.
  But what if there were 100 variables?
  A million?
]

The brute-force approach hits a wall.
With $n$ variables, you face $2^n$ possible inputs --- more than atoms in the universe for $n > 260$.

This exponential blowup is not a failure of imagination.
Boolean satisfiability (SAT) is NP-complete.
Equivalence checking is co-NP-complete.
Unless P = NP, no shortcut exists for the general case.

And yet, engineers verify circuits with thousands of variables every day.
How?

=== The Power of Representation

The secret lies in choosing the right *representation*.

Think of Roman numerals versus decimal notation.
Both can represent any number, but try multiplying MCMXCIV by CDXLVII.
The representation matters enormously.

For Boolean functions, most representations have crippling weaknesses:

- *Truth tables* are canonical (unique) but exponentially large
- *CNF formulas* are compact but checking equivalence is co-NP-complete
- *Circuits* are efficient to build but hard to analyze

BDDs hit a sweet spot: they are often compact *and* canonical *and* support efficient operations.
When they work, they work spectacularly well.

== What is a BDD?

A *Binary Decision Diagram* is a way of drawing a Boolean function as a flowchart.

#figure(
  cetz.canvas(length: 1cm, {
    import cetz.draw: *

    // BDD for x AND y with ordering x < y
    let x-pos = (2, 4)
    let y-pos = (2, 2.5)
    let zero-pos = (1, 0.8)
    let one-pos = (3, 0.8)

    // Draw terminals first (so edges appear on top)
    bdd-terminal-node(zero-pos, 0, name: "zero")
    bdd-terminal-node(one-pos, 1, name: "one")

    // Draw decision nodes
    bdd-decision-node(x-pos, $x$, name: "x")
    bdd-decision-node(y-pos, $y$, name: "y")

    // Draw edges
    // x: low -> 0, high -> y
    bdd-low-edge((x-pos.at(0) - 0.3, x-pos.at(1) - 0.4), (zero-pos.at(0) + 0.1, zero-pos.at(1) + 0.35))
    bdd-high-edge((x-pos.at(0) + 0.3, x-pos.at(1) - 0.4), (y-pos.at(0) + 0.35, y-pos.at(1) + 0.35))

    // y: low -> 0, high -> 1
    bdd-low-edge((y-pos.at(0) - 0.3, y-pos.at(1) - 0.4), (zero-pos.at(0) + 0.25, zero-pos.at(1) + 0.35))
    bdd-high-edge((y-pos.at(0) + 0.3, y-pos.at(1) - 0.4), (one-pos.at(0) - 0.25, one-pos.at(1) + 0.35))

    // Legend
    content(
      (5.5, 3.5),
      align(left)[
        #set text(size: 0.8em)
        *Reading the BDD:*\
        Start at $x$ (root)\
        If $x = 0$: follow dashed line $->$ *0*\
        If $x = 1$: go to $y$\
        #h(1em) If $y = 0$: follow dashed $->$ *0*\
        #h(1em) If $y = 1$: follow solid $->$ *1*
      ],
      anchor: "west",
    )
  }),
  caption: [BDD for $x and y$: the function outputs 1 only when both inputs are 1.],
)

Here is how to read a BDD:

+ *Start at the root* --- the topmost circle
+ *Check the variable* --- is it true (1) or false (0)?
+ *Follow the edge* --- solid for true, dashed for false
+ *Repeat* until you reach a square terminal
+ *The terminal's value* is your answer

The magic happens when you have *structure sharing*.
Consider the function $(x and y) or z$:

#figure(
  cetz.canvas(length: 1cm, {
    import cetz.draw: *

    // BDD for (x AND y) OR z with ordering x < y < z
    let x-pos = (1, 5)
    let y-pos = (2, 3.5)
    let z1-pos = (1, 2)
    let z2-pos = (3, 2)
    let zero-pos = (1, 0.5)
    let one-pos = (3, 0.5)

    // Draw terminals
    bdd-terminal-node(zero-pos, 0, name: "zero")
    bdd-terminal-node(one-pos, 1, name: "one")

    // Draw decision nodes
    bdd-decision-node(x-pos, $x$, name: "x")
    bdd-decision-node(y-pos, $y$, name: "y")
    bdd-decision-node(z1-pos, $z$, name: "z1")
    bdd-decision-node(z2-pos, $z$, name: "z2")

    // Edges from x
    bdd-low-edge((x-pos.at(0) - 0.35, x-pos.at(1) - 0.35), (z1-pos.at(0) - 0.25, z1-pos.at(1) + 0.4))
    bdd-high-edge((x-pos.at(0) + 0.35, x-pos.at(1) - 0.35), (y-pos.at(0) - 0.2, y-pos.at(1) + 0.4))

    // Edges from y
    bdd-low-edge((y-pos.at(0) - 0.35, y-pos.at(1) - 0.35), (z1-pos.at(0) + 0.35, z1-pos.at(1) + 0.35))
    bdd-high-edge((y-pos.at(0) + 0.35, y-pos.at(1) - 0.35), (z2-pos.at(0) - 0.2, z2-pos.at(1) + 0.4))

    // Edges from z1
    bdd-low-edge((z1-pos.at(0) - 0.25, z1-pos.at(1) - 0.4), (zero-pos.at(0) - 0.1, zero-pos.at(1) + 0.35))
    bdd-high-edge((z1-pos.at(0) + 0.35, z1-pos.at(1) - 0.35), (one-pos.at(0) - 0.35, one-pos.at(1) + 0.35))

    // Edges from z2
    bdd-low-edge((z2-pos.at(0) - 0.35, z2-pos.at(1) - 0.35), (one-pos.at(0) - 0.1, one-pos.at(1) + 0.35))
    bdd-high-edge((z2-pos.at(0) + 0.35, z2-pos.at(1) - 0.35), (one-pos.at(0) + 0.2, one-pos.at(1) + 0.35))

    // Note
    content(
      (6, 3),
      align(left)[
        #set text(size: 0.8em)
        Notice: both $z$ nodes\
        _share_ the same terminals.\
        \
        This sharing is the key to\
        BDD efficiency.
      ],
      anchor: "west",
    )
  }),
  caption: [BDD for $(x and y) or z$ showing structure sharing.],
)

Without sharing, a decision tree for $n$ variables needs up to $2^n$ leaves.
With sharing, a BDD often needs far fewer nodes --- sometimes polynomially many, sometimes even constant.

== A Brief History

The story of BDDs is one of incremental insight building to breakthrough.

=== The Early Days (1959--1978)

In 1959, *C. Y. Lee* described "binary decision programs" for representing switching circuits --- essentially, BDDs before the name existed.
His insight was that any Boolean function could be represented as a binary tree of if-then-else decisions.

In 1978, *S. B. Akers* formalized the structure and coined the term "Binary Decision Diagram."
But these early BDDs had a problem: the same function could be drawn in many different ways.
Checking if two BDDs represented the same function required expensive graph isomorphism tests.

=== The Bryant Revolution (1986)

The transformation came from *Randal Bryant*, then at Carnegie Mellon.
His 1986 paper introduced two deceptively simple restrictions:

+ *Order the variables* --- every path from root to terminal encounters variables in the same sequence
+ *Reduce the diagram* --- merge identical subgraphs and eliminate redundant nodes

These constraints create *Reduced Ordered Binary Decision Diagrams* (ROBDDs), with a stunning property:

#insight-box[
  For a fixed variable ordering, every Boolean function has *exactly one* ROBDD.

  This means: two functions are identical if and only if their BDDs are pointer-equal.
  Equivalence checking becomes a single comparison.
]

Bryant also provided efficient algorithms for combining BDDs.
Computing $f and g$ or $f or g$ takes time proportional to $|f| times |g|$ --- the product of their sizes, not exponential in variables.

=== The Verification Revolution (1987--1995)

The impact was immediate and profound.

In 1987, a team including *Edmund Clarke* (later a Turing Award recipient) demonstrated *symbolic model checking*.
They verified systems with $10^{20}$ states --- astronomically beyond what explicit enumeration could handle.

Hardware companies took notice.
Intel began using BDD-based tools to verify processor designs.
The infamous Pentium FDIV bug of 1994 --- which cost Intel \$475 million --- accelerated adoption of formal verification.
BDDs became essential infrastructure.

=== Maturity and Beyond (1995--Present)

By the mid-1990s, BDDs were a standard tool, but their limitations were better understood:

- Some functions (like integer multiplication) have exponentially large BDDs *regardless* of variable ordering
- Finding the best variable ordering is itself NP-hard
- Memory usage can be unpredictable

These limitations spurred alternatives:

- *SAT solvers* excel at finding single solutions quickly
- *BDD variants* like ZDDs handle sparse sets efficiently
- *Hybrid methods* combine the strengths of multiple approaches

Today, BDDs remain essential for problems requiring canonicity, counting, or symbolic state-space exploration.

== What Makes BDDs Special?

Three properties distinguish BDDs from other Boolean function representations:

=== Canonicity

For a fixed variable ordering, every Boolean function has exactly one reduced ordered BDD.
This property is powerful:

- *Equivalence checking*: Two BDDs represent the same function if and only if they are identical.
  With hash consing, this reduces to pointer comparison: $O(1)$.

- *Satisfiability*: A function is unsatisfiable if and only if its BDD is the $0$-terminal.
  This is also $O(1)$ after construction.

- *Tautology checking*: A function is a tautology if and only if its BDD is the $1$-terminal.

No other compact representation offers these constant-time queries.
Truth tables are canonical but exponentially large.
CNF and DNF are compact but non-canonical.

=== Efficient Operations

BDD operations have polynomial complexity in the sizes of the input BDDs:

#table(
  columns: (auto, auto),
  align: (left, center),
  table.header([*Operation*], [*Complexity*]),
  [Negation (with complement edges)], [$O(1)$],
  [AND, OR, XOR, etc.], [$O(|f| dot |g|)$],
  [Equivalence check], [$O(1)$],
  [Satisfiability check], [$O(1)$],
  [Model counting], [$O(|f|)$],
)

The $O(|f| dot |g|)$ bound for binary operations comes from memoization: each pair of nodes from the two BDDs is processed at most once.

=== Sharing

BDDs naturally share common subfunctions.
When building $f and g$ and $f or g$, the subgraph for $f$ is constructed once and reused.
This sharing arises automatically from *hash consing*: before creating a node, we check if an identical node already exists.

In a manager-centric implementation like `bdd-rs`, all BDDs share a single node pool.
Memory is proportional to the total number of distinct subfunctions, not the total number of BDDs.

== When BDDs Work Well

BDDs excel when the Boolean function has structure that permits compact representation:

*Sequential circuits and finite-state machines.*
Transition relations of digital circuits often have small BDDs because related bits are tested together.
State reachability can be computed symbolically, avoiding enumeration of individual states.

*Configuration constraints.*
Feature models and product line constraints typically yield manageable BDDs.
The hierarchical structure of features often suggests good variable orderings.

*Symmetric and threshold functions.*
Functions like "at least $k$ of $n$ variables are true" have polynomial-size BDDs.
Many constraints arising in combinatorial problems have this form.

*Problems requiring counting or enumeration.*
When you need to count satisfying assignments or enumerate all solutions, BDDs shine.
SAT solvers can find *one* solution quickly but struggle with *all* solutions.

== When BDDs Struggle

BDDs have well-known limitations:

*Integer multiplication.*
The function "output bits of $n$-bit multiplier" requires exponential BDD size regardless of variable ordering.
This is not a limitation of the algorithm but a fundamental property of the function.

*Large unstructured problems.*
Random Boolean functions or problems without exploitable structure tend to produce large BDDs.

*Dynamic problems.*
If the optimal variable ordering changes as constraints are added, maintaining good BDD size requires expensive reordering operations.

*Memory consumption.*
BDD operations can create many intermediate nodes.
Without garbage collection, memory can grow rapidly.

#warning-box(title: "No Silver Bullet")[
  BDDs are not universally superior to SAT solvers or other techniques.
  The choice depends on the problem structure and the queries needed.
  For single satisfiability queries on large formulas, modern SAT solvers often win.
  For repeated queries, counting, or symbolic state-space exploration, BDDs often win.
]

== The bdd-rs Library

This guide accompanies `bdd-rs`, a BDD library written in Rust.
Its design reflects lessons from decades of BDD research:

```rust
use bdd_rs::bdd::Bdd;

// Create a BDD manager
let bdd = Bdd::default();

// Variables are 1-indexed
let x = bdd.mk_var(1);
let y = bdd.mk_var(2);
let z = bdd.mk_var(3);

// Build a formula: (x ∧ y) ∨ z
let f = bdd.apply_or(bdd.apply_and(x, y), z);

// Constant-time queries
assert!(!bdd.is_zero(f));  // satisfiable?
assert!(!bdd.is_one(f));   // tautology?

// Count solutions (8 total assignments, how many satisfy f?)
let count = bdd.sat_count(f, 3);
println!("Solutions: {}", count);  // 5
```

Key design choices in `bdd-rs`:

- *Manager-centric architecture*: All operations go through the `Bdd` manager, ensuring hash consing and canonical form.
- *Complement edges*: Negation is $O(1)$, implemented as a single bit flip.
- *Type-safe handles*: `Ref` is a 32-bit handle; accidental misuse is caught at compile time.
- *Rust's safety guarantees*: Memory safety without garbage collector overhead.

== Guide Overview

The remainder of this guide is organized as follows:

*Part I (Chapters 2--5)* establishes the theoretical foundations: Boolean functions, Shannon expansion, the formal BDD definition, the canonicity theorem, and core algorithms.

*Part II (Chapters 6--11)* covers implementation: manager architecture, node representation, unique tables, the Apply algorithm, caching, and complement edges.

*Part III (Chapters 12--15)* explores advanced topics: variable ordering, garbage collection, quantification, and BDD variants.

*Part IV (Chapters 16--19)* demonstrates applications: model checking, combinatorial problems, symbolic execution, and configuration management.

*Part V (Chapters 20--22)* surveys the ecosystem: library comparisons, design trade-offs, and future directions.

Each chapter builds on previous ones, but readers with specific interests can skip ahead using the cross-references provided.
