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

The core method is `get_condition_var`.
It takes a `Condition` and returns a BDD `Ref`.

If we've seen this condition before, return the existing variable.
If not, create a new one.

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
  Our simple manager treats every distinct `Condition` as a completely independent boolean variable.

  For example, if we encounter `x > 0` and `x > 5`, they will be assigned two different variables, say $1$ and $2$.
  The BDD will allow both to be true simultaneously ($1 and 2$), which is fine.
  However, it also allows $1 and not 2$ (x > 0 but not x > 5), which is also fine.
  But it allows $not 1 and 2$ (not x > 0 but x > 5), which is logically impossible!

  This is known as *Boolean Abstraction*.
  We lose the semantic relationships between arithmetic constraints.
  Fixing this requires a more sophisticated mapping strategy (e.g., SMT integration or domain refinement), but for now, we accept this precision loss.
]

This simple logic guarantees that `x > 0` always maps to the same BDD variable, ensuring consistency across the entire analysis.
This is crucial: if we mapped `x > 0` to variable `1` in one place and variable `2` in another, the BDD would treat them as independent facts!

== Exposing BDD Operations

We also need to expose the BDD operations (AND, OR, NOT) so the rest of the engine can use them without touching the raw `Bdd` field directly.
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

BDDs are graphs, so the best way to debug them is to look at them!
We exposed a `to_dot` method in our manager.
Here is how to use it:

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

Let's test our manager with a simple scenario.
We will use the `Var`, `Op`, and `Condition` types we defined earlier.

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

This `AnalysisManager` is the foundation of our symbolic execution engine.
In the next chapter, we will use it to "execute" our IMP programs and build these BDDs automatically.

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

== Summary

- We set up a Rust project with `bdd-rs` dependency.
- We implemented `AnalysisManager` to map `Condition` AST nodes to BDD variables.
- We ensured that identical conditions map to identical variables (canonicalization).
- We exposed basic Boolean operations.

Next: *Symbolic Execution*.
We will write the code that walks the IMP programs and builds these BDDs automatically.
