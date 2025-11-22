// Chapter 2: Control Flow and the CFG

#import "../../theme.typ": *

= Control Flow and the CFG <ch-control-flow>

In the previous chapter, we defined the syntax of IMP using an Abstract Syntax Tree (AST).
While ASTs are excellent for representing the *structure* of code (how it is written), they are often awkward for analyzing its *behavior* (how it executes).

To analyze a program, we need to view it not as a hierarchy of statements, but as a network of possible execution paths.
This representation is called the *Control Flow Graph* (CFG).

#insight-box[
  *Analogy:* Think of an AST as a *Table of Contents* for a book --- it shows the hierarchy of chapters and sections.
  A CFG is like a *Flowchart* or a *Road Map* --- it shows how you can navigate from one point to another.
]

== From AST to CFG

An AST is recursive and hierarchical.
Execution, however, is sequential (step-by-step) and sometimes cyclic (loops).
A CFG "flattens" the recursive structure into a graph.

#definition(title: "Control Flow Graph")[
  A *Control Flow Graph* $G = (V, E)$ consists of:
  - *Nodes* $V$: Basic Blocks (sequences of straight-line code).
  - *Edges* $E$: Control flow transitions (jumps, branches) between blocks.
]

=== The Basic Block

The fundamental unit of a CFG is the *Basic Block*.

#definition(title: "Basic Block")[
  A *Basic Block* is a maximal sequence of instructions with:
  + *Single Entry*: Control can only enter at the first instruction.
  + *Single Exit*: Control can only leave from the last instruction.
]

Inside a basic block, execution is simple: if the first instruction executes, the second one *must* execute next, and so on, until the end.
There are no jumps *into* the middle or *out* of the middle of a block.

=== The MiniVerifier CFG Structure

In our Rust implementation, we represent the CFG as a collection of blocks, identified by unique integers (`BlockId`).

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
    Goto(BlockId),
    // Conditional jump based on an expression
    Branch {
        condition: Expr,
        true_target: BlockId,
        false_target: BlockId,
    },
    // End of program execution
    Return,
}
```

== Translating IMP to CFG

The translation process involves breaking down complex AST nodes (like `if` and `while`) into simple blocks and edges.
Let's visualize how each control structure is transformed.

=== Sequence (`s1; s2`)

Sequences are simply concatenated.
If `s1` is just a list of assignments, `s2` is appended to it.
If~`s1` contains control flow (like an `if`), it will end the current block, and `s2` will start in a new block that the previous blocks jump to.

=== Conditional (`if c { t } else { e }`)

A conditional statement splits the control flow into two paths that eventually merge.

#figure(
  caption: [Translation of `if c { t } else { e }` into CFG blocks.],
  cetz.canvas({
    import cetz.draw: *

    let style-block = (fill: colors.bg-subtle, stroke: colors.primary + 1pt)

    // Nodes
    rect((0, 0), (3, 1.5), ..style-block, name: "cond")
    content("cond", [*Header* \ `Branch(c)`])

    rect((-3.5, -3), (-0.5, -1.5), ..style-block, name: "then")
    content("then", [*Then Block* \ `t`])

    rect((0, -3), (3, -1.5), ..style-block, name: "else")
    content("else", [*Else Block* \ `e`])

    rect((0, -5.5), (3, -4), ..style-block, name: "join")
    content("join", [*Join Block* \ (next stmt)])

    // Edges
    line(
      "cond.west",
      (horizontal: "then.north", vertical: "cond.west"),
      "then.north",
      mark: (end: ">"),
      name: "true-edge",
    )
    content("true-edge.25%", text(size: 0.8em, fill: colors.success)[True], anchor: "south", padding: 0.2)

    line("cond.south", "else.north", mark: (end: ">"), name: "false-edge")
    content("false-edge.mid", text(size: 0.8em, fill: colors.error)[False], anchor: "west", padding: 0.2)

    line(
      "then.south",
      (horizontal: "then.south", vertical: "join.west"),
      "join.west",
      mark: (end: ">"),
    )
    line("else.south", "join.north", mark: (end: ">"))
  }),
)

=== Loop (`while c { body }`)

Loops introduce cycles in the graph.
We need a "Header" block to evaluate the condition every time the loop repeats.

#figure(
  caption: [Translation of `while c { body }` into CFG blocks.],
  cetz.canvas({
    import cetz.draw: *

    let style-block = (fill: colors.bg-subtle, stroke: colors.primary + 1pt)

    // Nodes
    rect((0, 2), (3, 3.5), ..style-block, name: "pre")
    content("pre", [*Predecessor*])

    rect((0, -1), (3, 0.5), ..style-block, name: "header")
    content("header", [*Header* \ `Branch(c)`])

    rect((0, -4), (3, -2.5), ..style-block, name: "body")
    content("body", [*Body Block* \ `body`])

    rect((4.5, -1), (7, 0.5), ..style-block, name: "exit")
    content("exit", [*Exit Block*])

    // Edges
    line("pre.south", "header.north", mark: (end: ">"))

    line("header.south", "body.north", mark: (end: ">"), name: "loop-edge")
    content("loop-edge.mid", text(size: 0.8em, fill: colors.success)[True], anchor: "west", padding: 0.2)

    line("header.east", "exit.west", mark: (end: ">"), name: "exit-edge")
    content("exit-edge.mid", text(size: 0.8em, fill: colors.error)[False], anchor: "south", padding: 0.2)

    // Back edge
    line(
      "body.west",
      (rel: (-1, 0), to: "body.west"),
      (horizontal: (), vertical: "header.west"),
      "header.west",
      stroke: (dash: "dashed"),
      mark: (end: ">", stroke: (dash: "solid")),
      name: "back-edge",
    )
    content("back-edge.mid", text(size: 0.8em, fill: colors.text-light)[Back Edge], anchor: "east", padding: 0.2)
  }),
)

=== Concrete Example

Let's trace the translation of a simple program:

```rust
x = 0;
while x < 10 {
    x = x + 1;
}
return;
```

This program produces the following CFG:

#figure(
  caption: [CFG for the simple counting loop.],
  cetz.canvas({
    import cetz.draw: *

    let style-start = (fill: colors.box-example, stroke: colors.success + 1.5pt)
    let style-norm = (fill: white, stroke: colors.primary + 1.5pt)
    let style-end = (fill: colors.box-warning, stroke: colors.warning + 1.5pt)

    // Entry Block
    rect((0.5, 4), (2.5, 6), ..style-start, name: "b0")
    content("b0", [*Block 0* \ `x = 0` \ `goto B1`])

    // Header Block
    rect((-0.5, 0), (3.5, 2.5), ..style-norm, name: "b1")
    content("b1", [*Block 1 (Header)* \ `Branch(x < 10)` \ `True -> B2` \ `False -> B3`])

    // Body Block
    rect((-5.5, 0.25), (-2, 2.25), ..style-norm, name: "b2")
    content("b2", [*Block 2 (Body)* \ `x = x + 1` \ `goto B1`])

    // Exit Block
    rect((0, -3), (3, -1.5), ..style-end, name: "b3")
    content("b3", [*Block 3 (Exit)* \ `return`])

    // Edges
    line("b0.south", "b1.north", mark: (end: ">"))

    // Loop edges
    line("b1.west", "b2.east", mark: (end: ">"), name: "true-edge")
    content("true-edge.mid", text(size: 0.8em, fill: colors.success)[True], anchor: "south", padding: 0.2)

    line(
      "b2.north",
      (rel: (0, 1)),
      (
        horizontal: (rel: (-1, 0), to: "b1.north"),
        vertical: (rel: (0, 1), to: "b2.north"),
      ),
      (rel: (-1, 0), to: "b1.north"),
      mark: (end: ">"),
    )

    // Exit edge
    line("b1.south", "b3.north", mark: (end: ">"), name: "false-edge")
    content("false-edge.mid", text(size: 0.8em, fill: colors.error)[False], anchor: "east", padding: 0.2)
  }),
)

#example-reference(
  "control_flow",
  "cfg_builder.rs",
  "cfg_builder",
  [
    *Hands-on Implementation:*
    Explore the `CfgBuilder` struct to see exactly how AST nodes are recursively visited and wired into a graph.
    The code handles the "current block" state and generates fresh block IDs.
  ],
)

== The Path Explosion Problem

Why do we go through all this trouble?
Why is software verification so hard?

The answer lies in the structure of the CFG.
Every time we encounter a branch (like an `if` or a loop iteration), the number of possible execution paths multiplies.

Consider a sequence of just 3 independent conditions:

```rust
if c1 { ... }
if c2 { ... }
if c3 { ... }
```

This creates $2 times 2 times 2 = 8$ paths.
For $N$ conditions, we have $2^N$ paths.
This is *exponential growth*.

#figure(
  caption: [Visualizing Path Explosion. Just a few levels of branching create many paths.],
  cetz.canvas({
    import cetz.draw: *

    let style-node = (fill: colors.primary, radius: 0.15)

    // Level 0
    circle((0, 0), ..style-node, name: "n0")

    // Level 1
    circle((-2, -1.5), ..style-node, name: "n1l")
    circle((2, -1.5), ..style-node, name: "n1r")

    // Level 2
    circle((-3, -3), ..style-node, name: "n2ll")
    circle((-1, -3), ..style-node, name: "n2lr")
    circle((1, -3), ..style-node, name: "n2rl")
    circle((3, -3), ..style-node, name: "n2rr")

    // Edges
    line("n0", "n1l", stroke: 0.5pt + colors.text-light)
    line("n0", "n1r", stroke: 0.5pt + colors.text-light)

    line("n1l", "n2ll", stroke: 0.5pt + colors.text-light)
    line("n1l", "n2lr", stroke: 0.5pt + colors.text-light)
    line("n1r", "n2rl", stroke: 0.5pt + colors.text-light)
    line("n1r", "n2rr", stroke: 0.5pt + colors.text-light)

    // Ellipsis for further explosion
    content((0, -3.8), text(size: 1.5em)[$dots$])
  }),
)

If we have a loop that iterates 100 times, it is conceptually similar to 100 nested `if` statements.
The number of paths becomes astronomical.
If the loop bound is unknown (e.g., `while input > 0`), the number of paths is *infinite*.

=== Path Sensitivity vs. Scalability

We want our analysis to be *Path Sensitive*.
This means distinguishing between different execution histories.

- *Path Insensitive*: "At this point, `x` could be anything." (Fast, but imprecise)
- *Path Sensitive*: "If we came from the true branch, `x` is 5. If we came from false, `x`~is~0." (Precise, but expensive)

#warning-box(title: "The Dilemma")[
  We cannot simply enumerate all paths --- there are too many.
  But we cannot simply merge all paths --- we lose too much precision.
]

== The Solution: Symbolic Representation

We need a "Third Way."
We need a data structure that can represent *sets of paths* compactly, without listing them one by one.

Imagine representing the set of all even numbers.
You don't list them: ${2, 4, 6, dots}$.
You use a symbolic rule: ${x | x mod 2 = 0}$.

In this guide, we will use *Binary Decision Diagrams (BDDs)* as our symbolic representation.
BDDs will allow us to:
+ Encode the control flow logic of the program.
+ Represent huge sets of program states efficiently.
+ Perform operations on these sets (like "join" or "intersection") mathematically.

In the next chapter, we will dive into BDDs and see how they work their magic.

#chapter-summary(
  [
    *CFGs capture behavior.*
    We transform the hierarchical AST into a flat graph of Basic Blocks to model execution flow.
  ],
  [
    *Basic Blocks are atomic.*
    They are sequences of instructions that always execute together. Control flow only happens at the boundaries.
  ],
  [
    *Path Explosion is the bottleneck.*
    The number of execution paths grows exponentially with program size, making naive enumeration impossible.
  ],
  [
    *Symbolic Execution is the key.*
    We will use BDDs to represent and manipulate sets of paths implicitly, avoiding the explosion problem.
  ],
)
