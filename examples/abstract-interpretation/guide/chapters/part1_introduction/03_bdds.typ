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
  caption: [A BDD representing the function $f = A and B$. To get to terminal 1, both A and B must be true.],
  cetz.canvas({
    import cetz.draw: *

    let draw-bdd-node(pos, label) = {
      circle(pos, radius: 0.4, fill: white, stroke: colors.primary + 2pt)
      content(pos, text(fill: colors.primary, size: 0.9em, weight: "bold")[#label])
    }

    let draw-bdd-terminal(pos, value) = {
      let term-color = if value == "0" { colors.error } else { colors.success }
      rect(
        (pos.at(0) - 0.35, pos.at(1) - 0.35),
        (pos.at(0) + 0.35, pos.at(1) + 0.35),
        fill: term-color.lighten(70%),
        stroke: term-color + 2pt,
        radius: 0.1,
      )
      content(pos, text(fill: term-color, size: 0.9em, weight: "bold")[#value])
    }

    let draw-bdd-edge(from, to, is-high) = {
      let edge-style = if is-high {
        (paint: colors.primary, thickness: 1.5pt)
      } else {
        (paint: colors.secondary, thickness: 1.5pt, dash: "dashed")
      }
      line(from, to, stroke: edge-style)
    }

    let root = (0, 3)
    let node-b = (2, 1.5)
    let term-0 = (-1, 0)
    let term-1 = (3, 0)

    draw-bdd-edge(root, term-0, false)
    draw-bdd-edge(root, node-b, true)
    draw-bdd-edge(node-b, term-0, false)
    draw-bdd-edge(node-b, term-1, true)

    draw-bdd-node(root, "A")
    draw-bdd-node(node-b, "B")
    draw-bdd-terminal(term-0, "0")
    draw-bdd-terminal(term-1, "1")
  })
) <fig:bdd-and>

=== Reduction and Sharing

The "Diagram" part is easy. The "Decision" part is standard. The magic is in the *Reduction*.
A BDD is *reduced* by applying two rules until no more changes can be made:

1.  *Merge Isomorphic Nodes*: If two nodes have the same variable, same high child, and same low child, they are the same node.
2.  *Eliminate Redundant Tests*: If a node's high and low edges point to the same child, the node is useless (the result is the same regardless of the variable's value). Remove it.

This reduction means that common sub-expressions are shared.
If multiple paths share the same tail (suffix), they share the same BDD nodes.

== The `ConditionManager`

In our MiniVerifier, we need to bridge the gap between the "semantic" world of our program (strings like "x > 0") and the "numeric" world of the BDD library (variables like 1, 2, 3).

We will implement a `ConditionManager` to handle this.

#info-box(title: "Design Pattern")[
  The `ConditionManager` is a wrapper around the raw BDD manager.
  It maintains a mapping: `HashMap<String, BddVariable>`.
]

When the analyzer encounters a condition `x > 0` for the first time:
1.  It asks the `ConditionManager`: "Do you have a variable for 'x > 0'?"
2.  The manager says "No", allocates a new BDD variable (e.g., index 1), and stores the mapping.
3.  It returns a BDD representing that variable.

When it encounters `x > 0` again later:
1.  The manager finds the existing mapping.
2.  It returns the existing BDD variable.

This ensures that the *same* logical condition is always represented by the *same* BDD variable, which is crucial for the logic to work correctly.

== Why BDDs Solve Path Explosion

Recall the path explosion problem: a loop or sequence of branches creates $2^N$ paths.

With BDDs, we don't store $2^N$ separate objects.
If the paths don't interact (e.g., independent branches), the BDD size grows *linearly* with the number of variables, not exponentially.

For example, if we have 100 independent `if` statements:
- Explicit paths: $2^{100}$ (impossible to store).
- BDD nodes: $2 times 100 = 200$ nodes (trivial).

The BDD automatically "factors out" the independence. It only grows large when variables are heavily correlated in complex ways (which does happen, but often not in typical control flow).

== Summary

- We represent *sets of paths* using *Boolean functions*.
- *BDDs* are a compact, canonical graph representation of these functions.
- *Reduction rules* (sharing and elimination) compress the representation.
- The *`ConditionManager`* maps program conditions to BDD variables.

In the next chapter, we will start implementing the `ConditionManager` and the core BDD interface in Rust.
