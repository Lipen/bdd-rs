// Chapter 2: Control Flow and the CFG

#import "../../theme.typ": *

= Control Flow and Program Structure <ch-control-flow>

In the previous chapter, we defined the syntax of our Toy Language (IMP) using an Abstract Syntax Tree (AST).
While ASTs are excellent for representing the *structure* of the code (how it is written), they are often awkward for analyzing its *behavior* (how it executes).

To analyze a program, we need to view it not as a hierarchy of rules, but as a network of possible execution paths.
This representation is called the *Control Flow Graph (CFG)*.

#insight-box[
  *Analogy:* Think of an AST as a *Rule Book* --- it lists regulations chapter by chapter.
  A CFG is like a *Traffic Map* --- it shows how execution actually moves through the intersections and roads.
]

== From AST to CFG

An AST is recursive and hierarchical.
Program execution, however, is sequential (instruction-by-instruction) and sometimes jumps between blocks.
A CFG "flattens" the recursive structure into a graph.

#definition(title: "Control Flow Graph")[
  A *Control Flow Graph* is a directed graph $G = (V, E, v_"entry")$ where:
  - $V$ is the set of *Basic Blocks* (nodes).
  - $E subset.eq V times V$ is the set of control flow transitions (edges).
  - $v_"entry" in V$ is the unique entry point of the program.
]

=== The Basic Block

The fundamental unit of a CFG is the *Basic Block*.

#definition(title: "Basic Block")[
  A *Basic Block* is a maximal sequence of instructions with:
  + *Single Entry*: Execution can only enter at the first instruction (the "leader").
  + *Single Exit*: Execution can only leave from the last instruction (the "terminator").
  + *Atomic Execution*: If the first instruction executes, all subsequent instructions in the block are guaranteed to execute (unless a crash occurs).
]

=== Implementing the CFG

In our Rust implementation, we represent the CFG as a collection of blocks, identified by unique integers (`BlockId`).

#info-box(title: "Why not analyze the AST directly?")[
  ASTs are trees, but control flow is a graph.
  Programs often have "jumps" (e.g., `goto`, `break`, `continue`).
  In an AST, the target is a separate subtree.
  In a CFG, it is just an edge to the target block.
  This "flattening" makes analysis much simpler, especially for loops.
]

```rust
type BlockId = usize;

#[derive(Clone, Debug)]
pub struct BasicBlock {
    pub id: BlockId,
    pub instructions: Vec<Instruction>, // The straight-line code
    pub terminator: Terminator,         // How we leave the block
}

#[derive(Clone, Debug)]
pub enum Terminator {
    // Unconditional jump to another block
    Jump(BlockId),
    // Conditional branch based on a condition
    Branch {
        condition: Match, // Uses the Match type from our AST
        true_target: BlockId,
        false_target: BlockId,
    },
    // Final verdict
    Return(Verdict),
}
```

#example-reference(
  "control_flow",
  "cfg_builder.rs",
  "cfg_builder",
  [
    Implementation of a CFG builder that transforms a linear sequence of instructions into a graph of basic blocks.
    Shows how to handle labels, jumps, and branches.
  ],
)

== Translating AST to CFG

The translation process involves breaking down complex AST nodes (like `if-else` trees) into simple blocks and edges.
Let's visualize how each structure is transformed.

=== Sequence (`s1; s2`)

Sequences are simply concatenated.
If `s1` is just a modification, `s2` is appended to it.
If~`s1` contains control flow, it will end the current block, and `s2` will start in a new block.

=== Branch (`if m { t } else { e }`)

A branch splits the execution flow into two paths that eventually merge.

#figure(
  caption: [Translation of `if m { t } else { e }` into CFG blocks.],
  cetz.canvas({
    import cetz.draw: *

    let style-block = (fill: colors.bg-subtle, stroke: colors.primary + 1pt)

    // Nodes
    rect((0, 0), (3, 1.5), ..style-block, name: "cond")
    content("cond", [*Header* \ `Branch(m)`])

    rect((-3.5, -3), (-0.5, -1.5), ..style-block, name: "then")
    content("then", [*True Path* \ `t`])

    rect((0, -3), (3, -1.5), ..style-block, name: "else")
    content("else", [*False Path* \ `e`])

    rect((0, -5.5), (3, -4), ..style-block, name: "join")
    content("join", [*Join Block* \ (next instruction)])

    // Edges
    line(
      "cond.west",
      ((), "-|", "then.north"),
      "then.north",
      mark: (end: ">"),
      name: "true-edge",
    )
    content("true-edge.25%", text(size: 0.8em, fill: colors.success)[True], anchor: "south", padding: 0.2)

    line("cond.south", "else.north", mark: (end: ">"), name: "false-edge")
    content("false-edge.mid", text(size: 0.8em, fill: colors.error)[False], anchor: "west", padding: 0.2)

    line(
      "then.south",
      ((), "|-", "join.west"),
      "join.west",
      mark: (end: ">"),
    )
    line("else.south", "join.north", mark: (end: ">"))
  }),
)

=== Loops

While our toy language PFL is loop-free, general programs have loops.
We need a "Header" block to evaluate the loop condition every time the execution loops.

#figure(
  caption: [Translation of a `while` loop into CFG blocks.],
  cetz.canvas({
    import cetz.draw: *

    let style-block = (fill: colors.bg-subtle, stroke: colors.primary + 1pt)

    // Nodes
    rect((0, -1), (3, 0.5), ..style-block, name: "header")
    content("header", [*Loop Header* \ `Condition`])

    rect((0, -4), (3, -2.5), ..style-block, name: "body")
    content("body", [*Loop Body* \ `Execute`])

    rect((4.5, -1), (7, 0.5), ..style-block, name: "exit")
    content("exit", [*Exit Block*])

    // Edges
    line((1.5, 1.5), "header.north", mark: (end: ">")) // Entry

    line("header.south", "body.north", mark: (end: ">"), name: "loop-edge")
    content("loop-edge.mid", text(size: 0.8em, fill: colors.success)[True], anchor: "west", padding: 0.2)

    line("header.east", "exit.west", mark: (end: ">"), name: "exit-edge")
    content("exit-edge.mid", text(size: 0.8em, fill: colors.error)[False], anchor: "south", padding: 0.2)

    // Back edge
    line(
      "body.west",
      (rel: (-1, 0)),
      ((), "|-", "header.west"),
      "header.west",
      stroke: (dash: "dashed"),
      mark: (end: ">", stroke: (dash: "solid")),
      name: "back-edge",
    )
    content("back-edge.mid", text(size: 0.8em, fill: colors.text-light)[Loop], anchor: "east", padding: 0.2)
  }),
)

== The Path Explosion Problem

Why do we go through all this trouble?
Why is program verification so hard?

The answer lies in the structure of the CFG.
Every time we encounter a branch, the number of possible execution paths multiplies.

Consider a sequence of just 3 independent checks in IMP:

```rust
if a > 0 { ... }
if b > 0 { ... }
if c > 0 { ... }
```

This creates $|Pi| = 2 times 2 times 2 = 8$ paths.
For a sequence of $N$ branches, the size of the path set $Pi$ grows exponentially:
$ |Pi| = 2^N $
This is *exponential growth*.

#figure(
  caption: [Visualizing Path Explosion. As execution branches, the number of distinct states we must track doubles at each step.],
  cetz.canvas({
    import cetz.draw: *

    // --- Styles & Constants ---
    let style-node = (fill: colors.primary, radius: 0.15)
    let dy = -1.5
    let dx-l1 = 2
    let dx-l2 = 1

    // --- Helper Functions ---
    let draw-state-node(pos, name, label, anchor) = {
      circle(pos, ..style-node, name: name)
      content(pos, text(size: 0.7em)[#label], anchor: anchor, padding: 0.2)
    }

    let draw-edge(from, to) = {
      line(from, to, stroke: 0.5pt + colors.text-light)
    }

    // --- Drawing ---

    // Level 0
    draw-state-node((0, 0), "n0", [State: $emptyset$], "south")

    // Level 1
    draw-state-node((-dx-l1, dy), "n1l", [${a > 0}$], "east")
    draw-state-node((dx-l1, dy), "n1r", [${a <= 0}$], "west")

    // Level 2
    draw-state-node((-dx-l1 - dx-l2, dy * 2), "n2ll", [${a > 0, b > 0}$], "north")
    draw-state-node((-dx-l1 + dx-l2, dy * 2), "n2lr", [${a > 0, b <= 0}$], "north")
    draw-state-node((dx-l1 - dx-l2, dy * 2), "n2rl", [${a <= 0, b > 0}$], "north")
    draw-state-node((dx-l1 + dx-l2, dy * 2), "n2rr", [${a <= 0, b <= 0}$], "north")

    // Edges
    draw-edge("n0", "n1l")
    draw-edge("n0", "n1r")

    draw-edge("n1l", "n2ll")
    draw-edge("n1l", "n2lr")
    draw-edge("n1r", "n2rl")
    draw-edge("n1r", "n2rr")

    // Ellipsis
    content((0, dy * 3), text(size: 1.2em, fill: colors.error)[$2^N$ Paths!])
  }),
)

If we analyze a loop by unrolling it (simulating each iteration), 100 iterations is conceptually similar to 100 nested `if` statements.
The number of paths becomes astronomical ($2^100$).

=== Path Sensitivity vs. Scalability

We want our analysis to be *Path Sensitive*.
This means distinguishing between different execution histories.

- *Path Insensitive*: "At this point, `x` could be anything." (Fast, but imprecise)
- *Path Sensitive*: "If we took the True branch, `x` is positive. If we took the False branch, `x`~is~negative." (Precise, but expensive)

#warning-box(title: "The Dilemma")[
  We want the precision of path sensitivity without the cost of enumerating exponential paths.
  Naive enumeration is impossible.
  Naive merging is imprecise.
]

== The Solution: Symbolic Representation

We need a "Third Way."
We need a data structure that can represent *sets of states* compactly, without listing them one by one.

#intuition-box[
  *Extensional vs. Intensional Definition*
  There are two ways to define a set $S$ within a universe $cal(U)$:

  - *Extensional:* Listing every member explicitly.
    $ S = {s_1, s_2, dots, s_n} $
    This is computationally infeasible when $|S|$ is large (e.g., $|cal(U)| approx 2^256$).

  - *Intensional:* Specifying a logical predicate $P$ that characterizes the set.
    $ S = {x in cal(U) mid(|) P(x)} $

  Symbolic execution relies on the *intensional* approach.
  A BDD encodes the *characteristic function* $chi_S: cal(U) -> {0, 1}$ defined as:
  $ chi_S(x) = cases(1 &"if" P(x) "is true", 0 &"otherwise") $
  This allows us to manipulate the *logic* of the set (the function $chi_S$) rather than enumerating its elements.
]

In this guide, we will use *Binary Decision Diagrams (BDDs)* as our symbolic representation.
BDDs will allow us to:
+ Encode the logic of the program.
+ Represent huge sets of program states efficiently.
+ Perform operations on these sets (like "join" or "intersection") mathematically.

In the next chapter, we will dive into BDDs and see how they work their magic.

#chapter-summary[
  - *CFGs capture behavior.*
    We transform the hierarchical AST into a flat graph of Basic Blocks to model execution.

  - *Basic Blocks are atomic.*
    They are sequences of instructions that always execute together.
    Branching only happens at the boundaries.

  - *Path Explosion is the bottleneck.*
    The number of execution paths grows exponentially with program size, making naive enumeration impossible.

  - *Symbolic Execution is the key.*
    We will use BDDs to represent and manipulate sets of states implicitly, avoiding the explosion problem.
]
