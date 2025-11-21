// Chapter 2: Control Flow and the CFG

#import "../../theme.typ": *

= Control Flow and the CFG <ch-control-flow>

In the previous chapter, we defined the syntax of IMP using an Abstract Syntax Tree (AST).
While ASTs are great for parsing, they are awkward for analysis.
To analyze how a program executes, we need a *Control Flow Graph* (CFG).

== From AST to CFG

An AST is hierarchical (a tree). Execution is sequential and sometimes cyclic (loops).
A CFG flattens the hierarchy into a graph where:
- *Nodes* represent program locations (program counters).
- *Edges* represent steps of execution (assignments or checks).

=== The MiniVerifier CFG

In our Rust implementation, we don't put statements *inside* nodes.
Instead, nodes are just indices (`usize`), and edges contain the actions.
This is often called an *edge-labeled* CFG.

```rust
type Location = usize;

#[derive(Clone, Debug)]
pub enum Action {
    Assign(String, Expr),  // x = e
    Condition(Cond),       // assume(c)
    Skip,                  // no-op
}

#[derive(Clone, Debug)]
pub struct Edge {
    pub src: Location,
    pub dst: Location,
    pub action: Action,
}

pub struct ControlFlowGraph {
    pub edges: Vec<Edge>,
    pub start: Location,
    pub end: Location,
}
```

=== Translating IMP to CFG

Let's see how we translate IMP statements into this graph.

*1. Assignment (`x = e`)*
Creates a single edge from start to end with the `Assign` action.

*2. Sequence (`s1; s2`)*
We compile `s1`, then `s2`.
The *end* of `s1` becomes the *start* of `s2`.

*3. Conditional (`if c { t } else { e }`)*
This creates a fork.
- One edge assumes `c` is true and goes to `t`.
- One edge assumes `c` is false (or `!c`) and goes to `e`.
Both branches eventually merge at a common exit point.

*4. Loop (`while c { body }`)*
This creates a cycle.
- Entry edge checks `c` and goes to `body`.
- Exit edge checks `!c` and skips the loop.
- The end of `body` loops back to the start.

#figure(
  caption: [CFG for a simple loop `while x < 10 { x = x + 1 }`. Nodes are locations, edges carry actions. The condition `x < 10` guards the loop entry, while `!(x < 10)` guards the exit.],

  cetz.canvas({
    import cetz.draw: *

    // Helper functions
    let draw-loc(pos, label, is-start: false, is-end: false) = {
      let color = if is-start { colors.accent } else if is-end { colors.success } else { colors.primary }
      circle(pos, radius: 0.3, fill: white, stroke: color + 1.5pt)
      content(pos, text(size: 0.8em, weight: "bold")[#label])
    }

    // Layout
    let l0 = (0, 4) // Start
    let l1 = (3, 4) // Inside loop
    let l2 = (0, 1) // Exit

    draw-loc(l0, "0", is-start: true)
    draw-loc(l1, "1")
    draw-loc(l2, "2", is-end: true)

    // Edges
    // 0 -> 1: assume(x < 10)
    line(l0, l1, stroke: colors.text-light + 1pt, mark: (end: ">"))
    content((1.5, 4.2), text(size: 0.7em)[$x < 10$])

    // 0 -> 2: assume(!(x < 10))
    line(l0, l2, stroke: colors.text-light + 1pt, mark: (end: ">"))
    content((-0.8, 2.5), text(size: 0.7em)[$not (x < 10)$])

    // 1 -> 0: x = x + 1 (Back edge)
    // Drawing a curved back edge
    let back-start = (3, 3.7)
    let back-mid = (1.5, 2.5)
    let back-end = (0.3, 3.8)

    line(back-start, back-mid, back-end, stroke: colors.text-light + 1pt, mark: (end: ">"))
    content((1.5, 2.8), text(size: 0.7em)[$x = x + 1$])
  }),
) <fig:cfg-loop>

== The Path Explosion Problem

Why is verification hard?
Because the number of paths through a CFG can be enormous.

Consider this sequence of conditions:

```rust
if x > 0 { x = x + 1 }
if y > 0 { y = y + 1 }
if z > 0 { z = z + 1 }
```

- 3 conditions
- $2^3 = 8$ possible paths.

For a program with $N$ conditions, we have $2^N$ paths.
If a loop runs $K$ times, it unfolds into a path of length $K$.
If the loop bound is unknown, the number of paths is infinite!

=== Path Sensitivity

We want our analysis to be *Path Sensitive*.
This means we want to know:
- "If we took the `x > 0` branch, then `x` is positive."
- "If we took the `else` branch, then `x` is non-positive."

If we simply merge all paths together (Path Insensitive), we lose this information.
But if we try to track every path individually, we explode exponentially.

== The Solution: Symbolic Representation

We need a way to track sets of paths without listing them one by one.
We need a data structure that can represent:
"The set of all paths where `x > 0` AND `y < 5`".

This is where *Binary Decision Diagrams (BDDs)* come in.
In the next chapter, we will see how BDDs allow us to handle this exponential complexity efficiently.

#chapter-summary(
  [
    *CFGs represent execution flow.*
    We translate the hierarchical AST into a flat graph of locations and edges.
  ],
  [
    *Edges carry actions.*
    Assignments update the state; Conditions filter the state (assumptions).
  ],
  [
    *Path explosion is the enemy.*
    The number of paths grows exponentially with branches and loops.
  ],
  [
    *We need a smart representation.*
    To achieve path sensitivity without explosion, we will use BDDs to represent path conditions symbolically.
  ],
)
