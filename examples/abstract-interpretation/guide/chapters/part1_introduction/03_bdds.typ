#import "../../theme.typ": *

= Binary Decision Diagrams <ch-bdds>

In @ch-control-flow, we saw that tracking every path individually leads to the *path explosion problem*.
To build a scalable verifier, we need a way to represent *sets* of paths efficiently.

This chapter introduces the *Binary Decision Diagram (BDD)*, the data structure that powers our MiniVerifier.
Instead of storing a list of paths, we will store a *function* that describes them.

== From Sets to Functions

How do we represent a set of items without listing them all?
We use a *characteristic function*.

For a universe of elements $U$, a subset $S subset U$ can be defined by a function $f_S : U -> {0, 1}$:
$ f_S(x) = cases(1 &"if" x in S, 0 &"if" x in.not S) $

If we can represent $f_S$ compactly, we can represent $S$ compactly.

=== Paths as Boolean Formulas

In our Control Flow Graph, a path is defined by the decisions made at branching points.
Let's assign a Boolean variable to each decision.

Consider this code:
```rust
if x > 0 {      // Decision A
    y = 1;
} else {
    y = 2;
}
if y < 5 {      // Decision B
    z = 3;
}
```

We have two decisions:
- $A$: is `x > 0`?
- $B$: is `y < 5`?

A path can be described as a conjunction of these variables:
- Path 1 (True, True): $A and B$
- Path 2 (True, False): $A and not B$
- Path 3 (False, True): $not A and B$
- Path 4 (False, False): $not A and not B$

The set of *all* valid paths is the disjunction of these formulas.
If we want to represent "all paths where `z = 3`", that corresponds to the set of paths where decision $B$ was true:
$ (A and B) or (not A and B) $
Simplifying this boolean formula gives us just $B$.

This is the key insight: *Set operations on paths become Boolean operations on formulas.*
- Union of path sets $->$ Logical OR ($or$)
- Intersection of path sets $->$ Logical AND ($and$)
- Empty set $->$ False ($0$)
- All paths $->$ True ($1$)

== Enter the BDD

A *Binary Decision Diagram* is a graph-based data structure that represents a Boolean function.
It is a Directed Acyclic Graph (DAG) with special properties that make it *canonical* and *compact*.

=== The Structure

A BDD consists of:
- *Decision Nodes*: Labeled with a variable (e.g., $A$, $B$). Each node has two outgoing edges:
  - *High Edge (solid)*: Taken if the variable is true.
  - *Low Edge (dashed)*: Taken if the variable is false.
- *Terminal Nodes*: The results, $0$ (False) and $1$ (True).

To evaluate the function for a given assignment of variables, we start at the root and follow the edges.

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
    // Values for (A and B) or C:
    // 000 -> 0
    // 001 -> 1
    // 010 -> 0
    // 011 -> 1
    // 100 -> 0
    // 101 -> 1
    // 110 -> 1
    // 111 -> 1
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

=== Reduction and Sharing

The "Diagram" part is easy. The "Decision" part is standard. The magic is in the *Reduction*.
A BDD is *reduced* by applying two rules until no more changes can be made:

+ *Merge Isomorphic Nodes*: If two nodes have the same variable, same high child, and same low child, they are the same node.
+ *Eliminate Redundant Tests*: If a node's high and low edges point to the same child, the node is useless (the result is the same regardless of the variable's value). Remove it.

This reduction means that common sub-expressions are shared.
If multiple paths share the same tail (suffix), they share the same BDD nodes.

== The `ConditionManager`

In our MiniVerifier, we need to bridge the gap between the "semantic" world of our program (strings like "`x > 0`") and the "numeric" world of the BDD library (variables like 1, 2, 3).

We will implement a `ConditionManager` to handle this.

#info-box(title: "Design Pattern")[
  The `ConditionManager` is a wrapper around the raw BDD manager.
  It maintains a mapping: `HashMap<Cond, Ref>`.
]

Here is a draft of the structure we will build:

```rust
pub struct ConditionManager {
    bdd: Bdd,
    mapping: HashMap<Cond, usize>, // Maps AST conditions to BDD variable IDs
    next_var_id: usize,
}

impl ConditionManager {
    /// Get or create the BDD variable for a condition
    pub fn get_condition(&mut self, cond: &Cond) -> Ref {
        if let Some(&id) = self.mapping.get(cond) {
            return self.bdd.mk_var(id);
        }

        let id = self.next_var_id;
        self.next_var_id += 1;
        self.mapping.insert(cond.clone(), id);
        self.bdd.mk_var(id)
    }
}
```

When the analyzer encounters a condition `x > 0` for the first time:
+ It asks the `ConditionManager`: "Do you have a variable for `x > 0`?"
+ The manager says "No", allocates a new BDD variable (e.g., index 1), and stores the mapping.
+ It returns a BDD representing that variable.

When it encounters `x > 0` again later:
+ The manager finds the existing mapping.
+ It returns the existing BDD variable.

This ensures that the *same* logical condition is always represented by the *same* BDD variable, which is crucial for the logic to work correctly.

== Why BDDs Solve Path Explosion

Recall the path explosion problem: a loop or sequence of branches creates $2^N$ paths.

With BDDs, we don't store $2^N$ separate objects.
If the paths don't interact (e.g., independent branches), the BDD size grows *linearly* with the number of variables, not exponentially.

For example, if we have 100 independent `if` statements:
- Explicit paths: $2^100$ (impossible to store).
- BDD nodes: $2 times 100 = 200$ nodes (trivial).

The BDD automatically "factors out" the independence.
It only grows large when variables are heavily correlated in complex ways (which does happen, but often not in typical control flow).

== Summary

- We represent *sets of paths* using *Boolean functions*.
- *BDDs* are a compact, canonical graph representation of these functions.
- *Reduction rules* (sharing and elimination) compress the representation.
- The *`ConditionManager`* maps program conditions to BDD variables.

In the next chapter, we will start implementing the `ConditionManager` and the core BDD interface in Rust.
