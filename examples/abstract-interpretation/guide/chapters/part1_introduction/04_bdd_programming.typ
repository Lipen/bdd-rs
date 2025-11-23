#import "../../theme.typ": *
#import "@preview/cetz:0.4.2": canvas, draw

= Implementing the Engine: The `FilterManager` <ch-bdd-programming>

We have the theory: BDDs represent sets of packets.
Now we build the engine.

Our first task is to implement the *`FilterManager`*.
This component translates the language of our firewall rules (strings like "`tcp.dst_port == 80`") into the language of BDDs (variables like 1, 2, 3).

== Setting Up the Project

First, let's create a new Rust project for our Firewall Checker.

```bash
cargo new firewall-checker
cd firewall-checker
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
  If you have the rule `tcp AND port_80` in two different chains, they point to the *exact same memory address*.

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
    content("node1", [tcp])

    circle((3.5, 1), radius: 0.4, name: "node2", fill: colors.node-bg, stroke: colors.node-border)
    content("node2", [ssh])

    // Terminals
    rect((1.5, -1), (2.5, -0.4), name: "zero", fill: colors.error.lighten(80%), stroke: colors.error)
    content("zero", [Drop])

    rect((3, -1), (4, -0.4), name: "one", fill: colors.success.lighten(80%), stroke: colors.success)
    content("one", [Accept])

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
    let is_tcp = bdd.mk_var(1);
    let is_ssh = bdd.mk_var(2);

    // 3. Combine them using the manager
    let ssh_traffic = bdd.apply_and(is_tcp, is_ssh); // TCP AND SSH
    let any_traffic = bdd.apply_or(is_tcp, is_ssh);  // TCP OR SSH

    // 4. Check results
    println!("SSH Traffic: {:?}", ssh_traffic);
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
Let's define a minimal Abstract Syntax Tree (AST) for packet headers and match rules.
This allows us to represent statements like `ip.src == 10.0.0.1` or `tcp.port == 22` as data structures.

```rust
// src/ast.rs

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum HeaderField {
    SrcIp,
    DstIp,
    Proto,
    DstPort,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Match {
    Exact(HeaderField, u32), // e.g., Proto == 6 (TCP)
    Range(HeaderField, u32, u32), // e.g., Port in [0, 1024]
    // ... other variants
}
```

== Designing the `FilterManager`

Now, let's build our bridge.
The BDD engine doesn't understand IP addresses or ports.
It only understands boolean variables $1, 2, 3, dots$.
We need a component that maps our rich AST matches (like `DstPort == 22`) to these simple BDD variables.

We need a struct that holds:
+ The `Bdd` manager itself.
+ A mapping from `Match` (our AST node) to BDD variable IDs.
+ A counter to assign new IDs.

```rust
use std::collections::HashMap;
use bdd_rs::bdd::Bdd;
use bdd_rs::reference::Ref;
// Assuming Match is defined as in Chapter 1
use crate::ast::Match;

pub struct FilterManager {
    bdd: Bdd,
    mapping: HashMap<Match, usize>,
    next_var_id: usize,
}

impl FilterManager {
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

The core method is `get_match_var`.
It takes a `Match` and returns a BDD `Ref`.

If we've seen this match rule before, return the existing variable.
If not, create a new one.

```rust
impl FilterManager {
    pub fn get_match_var(&mut self, m: &Match) -> Ref {
        if let Some(&id) = self.mapping.get(m) {
            // We've seen this rule before.
            // Return the BDD variable for it.
            return self.bdd.mk_var(id as u32);
        }

        // New rule!
        let id = self.next_var_id;
        self.next_var_id += 1;

        self.mapping.insert(m.clone(), id);
        self.bdd.mk_var(id as u32)
    }
}
```

#warning-box(title: "The Boolean Abstraction Gap")[
  Our simple manager treats every distinct `Match` as a completely independent boolean variable.

  For example, if we encounter `src_ip == 10.0.0.1` and `src_ip == 192.168.1.1`, they will be assigned two different variables, say $1$ and $2$.
  The BDD will allow both to be true simultaneously ($1 and 2$), even though a packet cannot have two different source IPs at once!

  This is known as *Boolean Abstraction*.
  We lose the semantic relationships between header fields.
  Fixing this requires a more sophisticated mapping strategy (e.g., One-Hot Encoding or SMT integration), but for now, we accept this precision loss.
]

This simple logic guarantees that `DstPort == 22` always maps to the same BDD variable, ensuring consistency across the entire analysis.
This is crucial: if we mapped `DstPort == 22` to variable `1` in one place and variable `2` in another, the BDD would treat them as independent facts!

== Exposing BDD Operations

We also need to expose the BDD operations (AND, OR, NOT) so the rest of the engine can use them without touching the raw `Bdd` field directly.
This encapsulates the BDD logic.

```rust
impl FilterManager {
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
let dot_graph = mgr.to_dot(policy);
println!("{}", dot_graph);
```

You can save this output to a `.dot` file and render it using Graphviz:

```bash
dot -Tpng output.dot -o output.png
```

#insight-box[
  Visualizing the BDD is the fastest way to spot if your variable ordering is inefficient or if your logic is incorrect.
  If the graph looks like a tangled mess for a simple policy, check your variable ordering!
]

== Putting It Together

Let's test our manager with a simple scenario.
We will use the `HeaderField` and `Match` types we defined earlier.

```rust
// Make sure to include the AST definition from above!
// mod ast; use ast::{HeaderField, Match};

fn main() {
    let mut mgr = FilterManager::new();

    // Encounter "proto == TCP" (6)
    let is_tcp = Match::Exact(HeaderField::Proto, 6);
    let c1 = mgr.get_match_var(&is_tcp);

    // Encounter "dst_port == 22" (SSH)
    let is_ssh = Match::Exact(HeaderField::DstPort, 22);
    let c2 = mgr.get_match_var(&is_ssh);

    // Policy: TCP AND SSH
    let policy = mgr.and(c1, c2);

    // Encounter "proto == TCP" again!
    // The manager should return the SAME variable ID.
    let c3 = mgr.get_match_var(&is_tcp);

    // Should be the same variable
    assert_eq!(c1, c3);

    println!("Policy BDD: {:?}", policy);
}
```

This `FilterManager` is the foundation of our symbolic execution engine.
In the next chapter, we will use it to "execute" our Firewall Chains and build these BDDs automatically.

#info-box(title: "Advanced BDD Topics")[
  For production BDD engines, two advanced topics are critical:

  - *Quantification* (∃, ∀): Projecting out variables (e.g., checking if *any* port allows access).
    - See #inline-example("bdd_advanced", "quantification.rs", "bdd_quantification")
  - *Variable Ordering*: The \#1 factor affecting BDD size.
    - See #inline-example("bdd_advanced", "variable_ordering.rs", "bdd_variable_ordering")

  Variable ordering can make the difference between tractable (linear nodes) and intractable (exponential nodes) for the same formula!
]

#exercise-box(number: 1, difficulty: "Medium")[
  *Derived Operations*:
  + Implement `implies(&self, a: Ref, b: Ref) -> Ref` using `apply_not` and `apply_or`.
    Use this to check for *Redundant Rules* (if $"Rule"_A => "Rule"_B$, then $"Rule"_B$ might be redundant).
  + Implement `are_mutually_exclusive(&self, a: Ref, b: Ref) -> bool`.
    Use this to check for *Shadowing* (if a high-priority rule matches a superset of a low-priority rule).
]

== Summary

- We set up a Rust project with `bdd-rs` dependency.
- We implemented `FilterManager` to map `Match` AST nodes to BDD variables.
- We ensured that identical matches map to identical variables (canonicalization).
- We exposed basic Boolean operations.

Next: *Symbolic Execution*.
We will write the code that walks the Firewall Chains and builds these BDDs automatically.
