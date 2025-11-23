#import "../../theme.typ": *
#import "@preview/cetz:0.4.2": canvas, draw

= Implementing the Engine: The `AnalysisManager` <ch-bdd-programming>

We have the theory: BDDs represent sets of program states.
Now we build the engine.

Our first task is to implement the *`AnalysisManager`*.
This component translates the language of our program conditions (strings like "`x > 0`") into the language of BDDs (variables like 1, 2, 3).

== Setting Up the Project

First, let's create a new Rust project for our IMP Analyzer.

```bash
cargo new imp-analyzer
cd imp-analyzer
# If using the local workspace:
# cargo add --path ../../bdd-rs
# If using crates.io (once published):
cargo add bdd-rs
```

We will use `bdd-rs` for all Boolean manipulation.
This library is designed to be safe, fast, and easy to use, but it requires following a specific *manager-centric* design pattern.

== The `bdd-rs` Crash Course

Before we build the manager, let's understand the tools we have.
The `bdd-rs` library operates on a strict principle: *The Manager is King*.

#info-box(title: "Why a Manager?")[
  In a BDD, nodes are shared.
  If you have the condition `x > 0 AND y < 5` in two different parts of the program, they point to the *exact same memory address*.

  To make this work, we need a central authority --- the `Bdd` manager --- to:
  + *Deduplicate*: Check if a node already exists before creating a new one (Hash Consing).
  + *Cache*: Remember the results of operations like `AND` and `OR` to avoid re-computing them (Computed Table).
]

#figure(
  canvas(length: 1cm, {
    import draw: *

    // Manager boundary
    rect((0, -1.4), (5, 4), fill: colors.bg-subtle, stroke: (paint: colors.primary, dash: "dashed"), radius: 0.2)
    content((2.5, 3.5), text(fill: colors.primary, weight: "bold")[BDD Manager])

    // Internal Nodes (The Truth)
    circle((2, 2.5), radius: 0.4, name: "node1", fill: colors.node-bg, stroke: colors.node-border)
    content("node1", [$x > 0$])

    circle((3.5, 1), radius: 0.4, name: "node2", fill: colors.node-bg, stroke: colors.node-border)
    content("node2", [$y < 5$])

    // Terminals
    rect((1.5, -1), (2.5, -0.4), name: "zero", fill: colors.error.lighten(80%), stroke: colors.error)
    content("zero", [False])

    rect((3, -1), (4, -0.4), name: "one", fill: colors.success.lighten(80%), stroke: colors.success)
    content("one", [True])

    // Edges (Internal structure)
    line("node1", "node2", mark: (end: ">", fill: colors.primary))
    line("node1", "zero", mark: (end: ">", fill: colors.primary, stroke: (dash: "solid")), stroke: (dash: "dashed"))
    line("node2", "one", mark: (end: ">", fill: colors.primary))
    line("node2", "zero", mark: (end: ">", fill: colors.primary, stroke: (dash: "solid")), stroke: (dash: "dashed"))

    // User Space (Refs)
    content((-3, 2.5), [*Ref $f$*], name: "ref_f")
    content((-3, 1), [*Ref $g$*], name: "ref_g")

    // Pointers (Handles)
    line(
      (rel: (0.2, 0), to: "ref_f.east"),
      "node1",
      stroke: 1.5pt + colors.secondary,
      mark: (end: ">", fill: colors.secondary),
    )
    line(
      (rel: (0.2, 0), to: "ref_g.east"),
      "node2",
      stroke: 1.5pt + colors.secondary,
      mark: (end: ">", fill: colors.secondary),
    )

    content((-1.5 + 0.2, 3), text(fill: colors.secondary, style: "italic")[Handle = ID])
  }),
  caption: [The Manager-Centric Model. The user holds `Ref` handles (integers), while the Manager stores the actual graph nodes. Multiple Refs can point to the same node.],
)

Here is how you use it correctly:

```rust
use bdd_rs::bdd::Bdd; // Import the manager

fn main() {
    // 1. Initialize the manager
    let bdd = Bdd::default();

    // 2. Create variables (must be 1-indexed!)
    // Variable 0 is reserved for internal use.
    let x_gt_0 = bdd.mk_var(1);
    let y_lt_5 = bdd.mk_var(2);

    // 3. Combine them using the manager
    let both_true = bdd.apply_and(x_gt_0, y_lt_5); // (x > 0) AND (y < 5)
    let either_true = bdd.apply_or(x_gt_0, y_lt_5);  // (x > 0) OR (y < 5)

    // 4. Check results
    println!("Both True: {:?}", both_true);
}
```

#warning-box[
  *Important Invariant:*
  You never operate on `Ref` directly (e.g., `x.and(y)` is wrong).
  You always ask the manager to do it: `bdd.apply_and(x, y)`.
  The `Ref` is just a lightweight handle (a number); the Manager holds the actual graph.
  `Ref` implements `Copy`, so you can pass it around freely without worrying about ownership.
]

Understanding why this manager-centric design is essential requires looking at the internal mechanisms of hash consing and computed caches.
The following example provides a deep dive into the manager's architecture:

#example-reference(
  "bdd_fundamentals",
  "manager_demo.rs",
  "bdd_manager",
  [
    Deep dive into BDD manager architecture: hash consing, computed cache, and why all operations must go through the manager.
    Essential for understanding the performance characteristics of BDDs.
  ],
)

== Defining the Input Language

To build a verifier, we first need a language to verify.
Let's define a minimal Abstract Syntax Tree (AST) for our IMP language conditions.
This allows us to represent statements like `x > 0` or `y == 10` as data structures.

```rust
// src/ast.rs

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Var {
    X, Y, Z, // Simplified for example
    // In real code: Named(String)
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Op {
    Eq, // ==
    Gt, // >
    Lt, // <
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Condition {
    pub var: Var,
    pub op: Op,
    pub val: i32,
}
```

== Designing the `AnalysisManager`

Now, let's build our bridge.
The BDD engine doesn't understand variables or integers.
It only understands boolean variables $1, 2, 3, dots$.
We need a component that maps our rich AST conditions (like `x > 0`) to these simple BDD variables.

We need a struct that holds:
+ The `Bdd` manager itself.
+ A mapping from `Condition` (our AST node) to BDD variable IDs.
+ A counter to assign new IDs.

```rust
use std::collections::HashMap;
use bdd_rs::bdd::Bdd;
use bdd_rs::reference::Ref;
// Assuming Condition is defined as in Chapter 1
use crate::ast::Condition;

pub struct AnalysisManager {
    bdd: Bdd,
    mapping: HashMap<Condition, usize>,
    next_var_id: usize,
}

impl AnalysisManager {
    pub fn new() -> Self {
        Self {
            bdd: Bdd::default(), // Use default configuration
            mapping: HashMap::new(),
            next_var_id: 1, // Start at 1! 0 is reserved.
        }
    }
}
```

== Allocating Conditions

`get_condition_var` takes a `Condition` and returns a BDD `Ref`.
If we've seen this condition before, return the existing variable.
Otherwise, allocate a new one.

```rust
impl AnalysisManager {
    pub fn get_condition_var(&mut self, c: &Condition) -> Ref {
        if let Some(&id) = self.mapping.get(c) {
            // We've seen this condition before.
            // Return the BDD variable for it.
            return self.bdd.mk_var(id as u32);
        }

        // New condition!
        let id = self.next_var_id;
        self.next_var_id += 1;

        self.mapping.insert(c.clone(), id);
        self.bdd.mk_var(id as u32)
    }
}
```

#warning-box(title: "The Boolean Abstraction Gap")[
  Our simple manager treats each `Condition` as an independent boolean variable.

  If we encounter `x > 0` and `x > 5`, they get separate variables $1$ and $2$.
  The BDD allows $1 and 2$ (fine), $1 and not 2$ (fine), but also $not 1 and 2$ (impossible: `x > 5` implies `x > 0`).

  This is *Boolean Abstraction*: we lose semantic relationships between arithmetic constraints.
  Fixing this requires SMT integration or domain refinement, but we accept this precision loss for now.
]

This guarantees `x > 0` always maps to the same BDD variable, ensuring consistency.
Mismapping it to `1` in one place and `2` elsewhere would create independent facts.

== Exposing BDD Operations

We expose AND, OR, NOT so the rest of the engine can use them without touching the raw `Bdd` field.
This encapsulates the BDD logic.

```rust
impl AnalysisManager {
    pub fn and(&self, a: Ref, b: Ref) -> Ref {
        self.bdd.apply_and(a, b)
    }

    pub fn or(&self, a: Ref, b: Ref) -> Ref {
        self.bdd.apply_or(a, b)
    }

    pub fn not(&self, a: Ref) -> Ref {
        self.bdd.apply_not(a)
    }

    pub fn true_ref(&self) -> Ref {
        self.bdd.mk_true()
    }

    pub fn false_ref(&self) -> Ref {
        self.bdd.mk_false()
    }

    // Helper to visualize the BDD (for debugging)
    pub fn to_dot(&self, r: Ref) -> String {
        bdd_rs::dot::to_dot(&self.bdd, r)
    }
}
```

== Debugging with Graphviz

BDDs are graphs --- visualize them to debug.
We exposed a `to_dot` method in our manager:

```rust
// Inside main()
let dot_graph = mgr.to_dot(state);
println!("{}", dot_graph);
```

You can save this output to a `.dot` file and render it using Graphviz:

```bash
dot -Tpng output.dot -o output.png
```

#insight-box[
  Visualizing the BDD is the fastest way to spot if your variable ordering is inefficient or if your logic is incorrect.
  If the graph looks like a tangled mess for a simple program, check your variable ordering!
]

== Putting It Together

Test our manager with a simple scenario using the `Var`, `Op`, and `Condition` types:

```rust
// Make sure to include the AST definition from above!
// mod ast; use ast::{Var, Op, Condition};

fn main() {
    let mut mgr = AnalysisManager::new();

    // Encounter "x > 0"
    let x_gt_0 = Condition { var: Var::X, op: Op::Gt, val: 0 };
    let c1 = mgr.get_condition_var(&x_gt_0);

    // Encounter "y < 5"
    let y_lt_5 = Condition { var: Var::Y, op: Op::Lt, val: 5 };
    let c2 = mgr.get_condition_var(&y_lt_5);

    // State: x > 0 AND y < 5
    let state = mgr.and(c1, c2);

    // Encounter "x > 0" again!
    // The manager should return the SAME variable ID.
    let c3 = mgr.get_condition_var(&x_gt_0);

    // Should be the same variable
    assert_eq!(c1, c3);

    println!("State BDD: {:?}", state);
}
```

`AnalysisManager` is the foundation of our symbolic execution engine.
Next chapter, we use it to "execute" IMP programs and build BDDs automatically.

#info-box(title: "Advanced BDD Topics")[
  For production BDD engines, two advanced topics are critical:

  - *Quantification* (∃, ∀): Projecting out variables (e.g., checking if *any* input causes an error).
    - See #inline-example("bdd_advanced", "quantification.rs", "bdd_quantification")
  - *Variable Ordering*: The \#1 factor affecting BDD size.
    - See #inline-example("bdd_advanced", "variable_ordering.rs", "bdd_variable_ordering")

  Variable ordering can make the difference between tractable (linear nodes) and intractable (exponential nodes) for the same formula!
]

#exercise-box(number: 1, difficulty: "Medium")[
  *Derived Operations*:
  + Implement `implies(&self, a: Ref, b: Ref) -> Ref` using `apply_not` and `apply_or`.
    Use this to check for *Redundant Checks* (if $"Check"_A => "Check"_B$, then $"Check"_B$ might be redundant).
  + Implement `are_mutually_exclusive(&self, a: Ref, b: Ref) -> bool`.
    Use this to check for *Unreachable Code* (if path condition $P$ and branch condition $C$ are mutually exclusive, the branch is dead).
]

== Manager Internals Deep Dive <sec-manager-internals>

The `Bdd` manager maintains three critical components:

+ *Unique Table*: Hash map keyed by `(var, low, high)` ensuring canonical node reuse.
+ *Computed Cache*: Memoization table keyed by `(op, left, right)` returning previously computed results.
+ *Variable Metadata*: Ordering array plus auxiliary stats (usage counts, last reorder timestamp).

#implementation-box[
  Use a fixed capacity hash table with load factor monitoring to trigger resizing.
  Instrument node insertions to gather a histogram of variable distribution.
]

#pitfall-box[
  *Hash Explosion Risk*.
  Poor hashing of `(var, low, high)` triples can degrade performance by increasing collisions.
  Always combine fields with a stable mixing function.
]

=== Apply Operation Workflow <sec-apply-workflow>

Every binary boolean operation follows a recursive pattern.
Given `(f, g)` and operator `op`, the algorithm returns a canonical `Ref` through six steps:

#[
  #set enum(numbering: it => [*Step #it:*])
  + Check trivial cases (identity, annihilators, complements).
  + Consult computed cache.
  + Align top variables according to global ordering.
  + Recurse on cofactors producing provisional children.
  + Reduce by eliminating redundant tests.
  + Insert or reuse via unique table.
]

#algorithm(title: "Generic Apply")[
  *Input:* BDD nodes $f$, $g$; operator $"op"$.

  *Output:* BDD node representing $f "op" g$.

  + *if* $"trivial"(f, g, "op")$ *then*
    + *return* $"simplify"(f, g, "op")$
  + *if* $"cache"."contains"("op", f, g)$ *then*
    + *return* $"cache"."get"("op", f, g)$
  + $v <- "select_top_var"(f, g)$ $quad slash.double$ Choose root variable.
  + $(f_0, f_1) <- "cofactor"(f, v)$ $quad slash.double$ Split on low/high.
  + $(g_0, g_1) <- "cofactor"(g, v)$
  + $"low" <- "apply"("op", f_0, g_0)$ $quad slash.double$ Recursive calls.
  + $"high" <- "apply"("op", f_1, g_1)$
  + *if* $"low" = "high"$ *then*
    + *return* $"low"$ $quad slash.double$ Redundant test elimination.
  + $"node" <- "unique_table"."intern"(v, "low", "high")$ $quad slash.double$ Insert.
  + $"cache"."put"("op", f, g, "node")$ $quad slash.double$ Memoize.
  + *return* $"node"$
]

=== Instrumentation and Metrics <sec-instrumentation>

Add lightweight counters to monitor performance.
Suggested metrics:

- *Node Creations*: Count of unique table insertions.
- *Cache Hits / Misses*: Ratio guiding apply optimization.
- *Reductions Applied*: Number of redundant test eliminations.
- *Peak Node Count*: High water mark tracking memory pressure.

#implementation-box[
  Expose a `struct BddStats` to hold these counters:
  ```rust
  struct BddStats {
    node_creations: u64,
    cache_hits: u64,
    cache_misses: u64,
    reductions: u64,
    peak_nodes: u64,
  }
  ```
  Update statistics at key points in the apply algorithm.
]

#exercise-box(number: 2, difficulty: "Medium")[
  Add `BddStats` to your local fork and print a summary after constructing random conjunctions of 100 variables.
  Compare cache hit ratio before and after enabling complement edge optimization.
]

=== Concurrency and Thread Safety <sec-concurrency>

BDD managers rely on global uniqueness, complicating multi-threaded usage.
Parallel apply operations can race during node creation, violating canonicity.

Safe strategies:

- *Sharding*: Partition variable sets and build partial BDDs, then combine sequentially.
- *Task Queues*: Serialize unique table insertions while allowing parallel cofactor recursion.
- *Read-Mostly Locking*: Use an `RwLock` for unique table with short write locks on insertion.

#warning-box[
  *Do Not Clone Managers Freely*.
  Cloning without deep copy of tables breaks pointer equality assumptions across instances.
]

#exercise-box(number: 3, difficulty: "Hard")[
  Sketch a design for parallel apply using a work stealing deque for recursion tasks and a centralized insertion channel.
  Analyze potential contention points.
]

=== Advanced Quantification Example <sec-advanced-quantification>

Existential quantification removes variables by abstracting over both branches.
The formula is:

$ exists x. f(x) = f_(x=0) or f_(x=1) $

Implementation merges cofactors then reduces.

#example-reference(
  "bdd_advanced",
  "quantification.rs",
  "bdd_quantification",
  [Hands on quantification implementation illustrating Shannon expansion reduction integration.],
)

#exercise-box(number: 4, difficulty: "Medium")[
  Implement universal quantification $forall x. f(x) = f_(x=0) and f_(x=1)$ and measure node count changes on structured vs random formulas.
]

=== Research Spotlight: Incremental Reordering <sec-incremental-reorder>

Incremental reordering seeks to relocate only a small subset of variables whose local neighborhoods grew disproportionately.

The approach consists of:

+ *Detect Hot Spots*: Variables with large subtree size growth since last snapshot.
+ *Local Sift Window*: Attempt swaps within a bounded index range.
+ *Rollback*: Revert if node count fails to improve beyond threshold.

Emerging work couples ML models predicting beneficial swap candidates using feature vectors (subtree size, fanout, clustering coefficient).

#historical-note(person: "P. C. McGeer", year: 1993, title: "Dynamic Variable Reordering")[
  Early work formalized sifting heuristics establishing practical viability of dynamic ordering in industrial circuits.
]

#exercise-box(number: 5, difficulty: "Hard")[
  Prototype a hot spot detector recording relative growth percentages per variable after each batch of 100 apply calls.
  Trigger a local reorder when any variable exceeds 20% growth.
]

== Summary

- Set up Rust project with `bdd-rs` dependency.
- Implemented `AnalysisManager` to map `Condition` AST nodes to BDD variables.
- Ensured identical conditions map to identical variables (canonicalization).
- Exposed basic Boolean operations.

Next: *Symbolic Execution*.
We write the code that walks IMP programs and builds BDDs automatically.
