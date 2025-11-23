#import "../../theme.typ": *

= Binary Decision Diagrams <ch-bdds>

In @ch-control-flow, we saw that tracking every execution path individually leads to the *path explosion problem*.

To build a scalable verifier, we need a mechanism to represent *sets* of paths efficiently.

This chapter introduces the *Binary Decision Diagram (BDD)*, the core data structure powering our MiniVerifier.

Instead of enumerating paths as a list, we represent them as a *Boolean function*.

== From Sets to Functions

A fundamental insight in symbolic execution is the correspondence between sets and functions.

We can represent any subset $S$ of a universe $U$ using a *characteristic function* $f_S : U -> {0, 1}$:

$ f_S (x) = cases(1 &"if" x in S, 0 &"if" x in.not S) $

If we can represent $f_S$ compactly, we effectively represent the set $S$ compactly.

=== Paths as Boolean Formulas

In a Control Flow Graph, a path is determined by the sequence of decisions made at branching points.

By assigning a Boolean variable to each decision, we can encode paths as logical formulas.

Consider the following code snippet:

```rust
if x > 0 {  // Decision A
    y = 1;
} else {
    y = 2;
}
if y < 5 {  // Decision B
    z = 3;
}
```

Let $A$ represent the condition `x > 0` and $B$ represent `y < 5`.

Each path corresponds to a conjunction of these variables:

- *Path 1* (True, True): $A and B$
- *Path 2* (True, False): $A and not B$
- *Path 3* (False, True): $not A and B$
- *Path 4* (False, False): $not A and not B$

The set of *all* valid paths is the disjunction of these formulas.

To represent the set of paths where `z = 3` (i.e., where decision $B$ is true), we write:
$ (A and B) or (not A and B) $

Using Boolean algebra, this simplifies to just $B$.

#info-box(title: "Key Insight")[
  Set operations on paths correspond directly to Boolean operations on formulas:
  - *Union* ($union$) $->$ Logical OR ($or$)
  - *Intersection* ($inter$) $->$ Logical AND ($and$)
  - *Empty Set* ($emptyset$) $->$ False ($0$)
  - *Universal Set* ($U$) $->$ True ($1$)
]

== Formal Definition of BDDs

A *Binary Decision Diagram (BDD)* is a graph-based data structure representing a Boolean function $f: {0, 1}^n -> {0, 1}$.

Its construction relies on the *Shannon Expansion*.

#definition(title: "Shannon Expansion")[
  Any Boolean function $f(x_1, ..., x_n)$ can be decomposed with respect to a variable $x_i$:
  $ f = (x_i and f_(x_i=1)) or (not x_i and f_(x_i=0)) $
  where:
  - $f_(x_i=1)$ is the function $f$ with $x_i$ set to True (Positive Cofactor).
  - $f_(x_i=0)$ is the function $f$ with $x_i$ set to False (Negative Cofactor).
]

Recursively applying this expansion yields a *Decision Tree*.

Since trees grow exponentially with the number of variables ($2^n$ leaves), we transform the tree into a *Directed Acyclic Graph (DAG)* to achieve compactness.

=== Ordered Binary Decision Diagrams (OBDD)

A BDD is *Ordered* (OBDD) if the variables appear in the same fixed order on all paths from the root to the terminals.

For instance, given the natural ordering $A < B < C$, every path tests $A$ before $B$, and $B$ before $C$.

#pitfall-box[
  *Variable Ordering Matters!*
  The size of a BDD depends heavily on the variable order.
  A good order keeps related variables close together.
  A bad order can cause exponential blowup.
  For example, for the function $(a_1 and b_1) or (a_2 and b_2) or ...$, the order $a_1, b_1, a_2, b_2...$ is linear, while $a_1, a_2, ..., b_1, b_2...$ is exponential.
]

=== Reduced BDDs

A BDD is *Reduced* (ROBDD) if it contains no redundant information.

We achieve this by repeatedly applying two reduction rules until the graph is minimal:

+ *Merge Isomorphic Nodes*:
  If two nodes $u$ and $v$ represent the same variable and have identical high and low children, they are equivalent.

  We keep one and redirect all edges pointing to the other.
+ *Eliminate Redundant Tests*:
  If a node $u$ has identical high and low children ($"high"(u) = "low"(u)$), the decision at $u$ does not affect the outcome.

  We remove $u$ and redirect incoming edges directly to its child.

#info-box(title: "Canonicity Property")[
  For a fixed variable ordering, the reduced OBDD for any Boolean function is *unique*.

  This property is crucial for verification: checking the equivalence of two functions $f equiv g$ reduces to checking if their BDD root nodes are identical (pointer equality), which is an $O(1)$ operation.
]

Before diving deeper into BDD theory, it's worth getting hands-on experience with basic BDD operations.

The following example demonstrates variable creation, boolean operations, and the canonicity property in action:

#example-reference(
  "bdd_fundamentals",
  "basics.rs",
  "bdd_basics",
  [
    Hands-on introduction to BDD operations: creating variables, applying boolean operations (AND, OR, NOT, XOR), and observing canonicity.
    Perfect starting point for understanding BDDs practically.
  ],
)

== Visualizing Reduction

To illustrate these concepts, let us visualize the reduction of the decision tree for the function $(A and B) or C$, using the variable ordering $A < B < C$.

#figure(
  caption: [Comparison: Full Decision Tree vs. Reduced BDD for $(A and B) or C$],
  cetz.canvas({
    import cetz.draw: *

    let style-node = (fill: white, stroke: colors.primary + 1.5pt)
    let style-term-0 = (fill: colors.error.lighten(80%), stroke: colors.error + 1.5pt)
    let style-term-1 = (fill: colors.success.lighten(80%), stroke: colors.success + 1.5pt)

    let draw-node(pos, label, name) = {
      circle(pos, radius: 0.35, name: name, ..style-node)
      content(pos, text(weight: "bold")[#label])
    }

    let draw-term(pos, label, name) = {
      let s = if label == "0" { style-term-0 } else { style-term-1 }
      let (x, y) = pos
      let r = 0.3
      rect((x - r, y - r), (x + r, y + r), name: name, ..s, radius: 0.1)
      content(pos, text(weight: "bold")[#label])
    }

    let draw-edge(from, to, type) = {
      let s = if type == "high" {
        (paint: colors.primary)
      } else {
        (paint: colors.secondary, dash: "dashed")
      }
      line(from, to, stroke: s, mark: (end: ">", size: 0.15, stroke: (dash: "solid"), fill: s.paint))
    }

    // --- LEFT: Full Decision Tree ---
    let x-left = -5
    content((x-left, 4), text(weight: "bold")[Full Decision Tree])

    // Level 0: A
    draw-node((x-left, 3), [A], "t_root")

    // Level 1: B
    draw-node((x-left - 2, 1.5), [B], "t_b0")
    draw-node((x-left + 2, 1.5), [B], "t_b1")

    draw-edge("t_root", "t_b0", "low")
    draw-edge("t_root", "t_b1", "high")

    // Level 2: C
    draw-node((x-left - 3, 0), [C], "t_c00")
    draw-node((x-left - 1, 0), [C], "t_c01")
    draw-node((x-left + 1, 0), [C], "t_c10")
    draw-node((x-left + 3, 0), [C], "t_c11")

    draw-edge("t_b0", "t_c00", "low")
    draw-edge("t_b0", "t_c01", "high")
    draw-edge("t_b1", "t_c10", "low")
    draw-edge("t_b1", "t_c11", "high")

    // Level 3: Terminals
    let terminals = (0, 1, 0, 1, 0, 1, 1, 1)
    let x-start = x-left - 3.5
    for (i, val) in terminals.enumerate() {
      let name = "tt" + str(i)
      let x-pos = x-start + i * 1.0
      draw-term((x-pos, -1.5), str(val), name)

      // Connect to parent
      let parent-idx = int(i / 2)
      let parent-name = "t_c" + str(int(parent-idx / 2)) + str(int(calc.rem(parent-idx, 2)))
      let type = if calc.rem(i, 2) == 0 { "low" } else { "high" }
      draw-edge(parent-name, name, type)
    }

    content((x-left, -2.5), text(size: 0.8em, style: "italic")[Exponential growth: $2^n$ paths])

    // --- RIGHT: Reduced BDD ---
    let x-right = 4
    content((x-right, 4), text(weight: "bold")[Reduced BDD])

    draw-node((x-right, 3), [A], "r_a")
    draw-node((x-right + 1.5, 1.5), [B], "r_b")
    draw-node((x-right, 0), [C], "r_c")

    draw-term((x-right - 1.5, -1.5), "0", "r_0")
    draw-term((x-right + 1.5, -1.5), "1", "r_1")

    // Edges for Reduced
    // A low -> C
    draw-edge("r_a", "r_c", "low")
    // A high -> B
    draw-edge("r_a", "r_b", "high")

    // B low -> C (Sharing!)
    draw-edge("r_b", "r_c", "low")
    // B high -> 1
    draw-edge("r_b", "r_1", "high")

    // C low -> 0
    draw-edge("r_c", "r_0", "low")
    // C high -> 1
    draw-edge("r_c", "r_1", "high")

    content((x-right, -2.5), text(size: 0.8em, style: "italic")[Shared nodes C and 1])
  }),
) <fig:bdd-comparison>

@fig:bdd-comparison demonstrates the dramatic difference between the tree and graph representations:

- *Left (Decision Tree)*: The tree explicitly enumerates all 8 paths.
  Note the redundancy: the subtrees for $C$ are repeated multiple times.
- *Right (Reduced BDD)*: The graph is significantly more compact due to reduction:
  - *Isomorphism*: The node $C$ is shared by both branches of $B$.
  - *Redundant Test Elimination*: Notice the edge from $A$ (low) directly to $C$.
    If $A$ is false, the expression $(A and B) or C$ simplifies to $(0 and B) or C$, which equals $C$.
    This means the value of $B$ is irrelevant.
    The redundant $B$ node is removed, and $A$ connects directly to $C$.

== The `ConditionManager`

In our MiniVerifier, we must bridge the gap between the "semantic" world of the program (AST nodes like `x > 0`) and the "numeric" world of the BDD library (integer variables like 1, 2, 3).

We implement a `ConditionManager` to handle this translation and ensure consistency.

#info-box(title: "Design Pattern")[
  The `ConditionManager` acts as a facade over the raw BDD manager.
  It~maintains a `HashMap<Cond, Ref>` to ensure that identical AST conditions always map to the same BDD variable.
]

The structure is defined as follows:

```rust
// Ensure Cond derives Hash and Eq!
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Cond {
    // ... variants ...
}

pub struct ConditionManager {
    bdd: Bdd,
    mapping: HashMap<Cond, usize>, // Maps AST conditions to BDD variable IDs
    next_var_id: usize,
}

impl ConditionManager {
    /// Get or create the BDD variable for a condition
    pub fn get_condition(&mut self, cond: &Cond) -> Ref {
        if let Some(&id) = self.mapping.get(cond) {
            return self.bdd.mk_var(id as u32);
        }

        let id = self.next_var_id;
        self.next_var_id += 1;
        self.mapping.insert(cond.clone(), id);
        self.bdd.mk_var(id as u32)
    }
}
```

#intuition-box[
  *What is a `Ref`?*
  A `Ref` is just a lightweight integer handle (like a pointer or an ID).
  It has no meaning on its own.
  You must always pass it back to the `Bdd` manager to perform operations.
  Think of it like a "file descriptor" --- you need the OS (Manager) to read the file.
]

The workflow is:
+ When the analyzer encounters a condition (e.g., `x > 0`) for the first time, the manager allocates a new BDD variable (e.g., index 1) and stores the mapping.
+ When the same condition is encountered later, the manager retrieves the existing mapping and returns the same BDD variable.

This guarantees that the *same* logical condition is always represented by the *same* BDD variable, preserving the logical consistency of the analysis.

== Why BDDs Solve Path Explosion

As discussed in @ch-control-flow, a sequence of $N$ branches can create $2^N$ paths.

BDDs mitigate this explosion by exploiting structure and independence.

If paths do not interact (e.g., independent branches), the BDD size grows *linearly* with the number of variables, rather than exponentially.

For example, consider 100 independent `if` statements:
- *Explicit Paths*: $2^100$ paths (computationally intractable).
- *BDD Nodes*: $2 times 100 = 200$ nodes (trivial to store).

The BDD automatically "factors out" the independence.

Explosion typically occurs only when variables are heavily correlated in complex ways (e.g., cryptographic functions or multipliers), which is less common in typical control flow logic.

== Summary

- *Sets of paths* are represented as *Boolean functions*.
- *BDDs* provide a compact, canonical graph representation of these functions.
- *Reduction rules* (Isomorphism and Redundant Tests) compress the representation by sharing common sub-structures.
- The *`ConditionManager`* maps program conditions to BDD variables, ensuring consistency.

#info-box(title: "Explore BDD Operations")[
  To see boolean operations in action, run #run-example("bdd_boolean_ops") which demonstrates AND, OR, XOR, and their algebraic properties like De Morgan's laws and absorption.
]

In the next chapter, we will implement the `ConditionManager` and the core BDD interface in Rust.
