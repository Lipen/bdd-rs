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
  + *Single Entry*: Control can only enter at the first instruction (the "leader").
  + *Single Exit*: Control can only leave from the last instruction (the "terminator").
  + *Atomic Execution*: If the first instruction executes, all subsequent instructions in the block are guaranteed to execute.
]

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
    // Conditional jump based on a condition
    Branch {
        condition: Cond, // Uses the Cond type from our AST
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

=== Loop (`while c { body }`)

Loops introduce cycles in the graph.
We need a "Header" block to evaluate the condition every time the loop repeats.

#figure(
  caption: [Translation of `while c { body }` into CFG blocks.],
  cetz.canvas({
    import cetz.draw: *

    let style-block = (fill: colors.bg-subtle, stroke: colors.primary + 1pt)

    // Nodes
    rect((0, -1), (3, 0.5), ..style-block, name: "header")
    content("header", [*Header* \ `Branch(c)`])

    rect((0, -4), (3, -2.5), ..style-block, name: "body")
    content("body", [*Body Block* \ `body`])

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
    content("back-edge.mid", text(size: 0.8em, fill: colors.text-light)[Back Edge], anchor: "east", padding: 0.2)
  }),
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
  caption: [Visualizing Path Explosion. As paths branch, the number of distinct program states we must track doubles at each step.],
  cetz.canvas({
    import cetz.draw: *

    let style-node = (fill: colors.primary, radius: 0.15)
    let style-state = (fill: colors.bg-code, stroke: colors.text-light + 0.5pt, radius: 0.1)

    // Level 0
    circle((0, 0), ..style-node, name: "n0")
    content((0, 0.5), text(size: 0.7em)[State: {}])

    // Level 1
    circle((-2, -1.5), ..style-node, name: "n1l")
    content((-2.5, -1.5), text(size: 0.7em)[{A}], anchor: "east")
    circle((2, -1.5), ..style-node, name: "n1r")
    content((2.5, -1.5), text(size: 0.7em)[{!A}], anchor: "west")

    // Level 2
    circle((-3, -3), ..style-node, name: "n2ll")
    content((-3, -3.5), text(size: 0.7em)[{A, B}])

    circle((-1, -3), ..style-node, name: "n2lr")
    content((-1, -3.5), text(size: 0.7em)[{A, !B}])

    circle((1, -3), ..style-node, name: "n2rl")
    content((1, -3.5), text(size: 0.7em)[{!A, B}])

    circle((3, -3), ..style-node, name: "n2rr")
    content((3, -3.5), text(size: 0.7em)[{!A, !B}])

    // Edges
    line("n0", "n1l", stroke: 0.5pt + colors.text-light)
    line("n0", "n1r", stroke: 0.5pt + colors.text-light)

    line("n1l", "n2ll", stroke: 0.5pt + colors.text-light)
    line("n1l", "n2lr", stroke: 0.5pt + colors.text-light)
    line("n1r", "n2rl", stroke: 0.5pt + colors.text-light)
    line("n1r", "n2rr", stroke: 0.5pt + colors.text-light)

    // Ellipsis for further explosion
    content((0, -4.5), text(size: 1.2em, fill: colors.error)[$2^N$ States!])
  }),
)

If we have a loop that iterates 100 times, it is conceptually similar to 100 nested `if` statements (if we unroll the loop).
The number of paths becomes astronomical.
If the loop bound is unknown (e.g., `while input > 0`), the number of paths is *infinite*.

=== Path Sensitivity vs. Scalability

We want our analysis to be *Path Sensitive*.
This means distinguishing between different execution histories.

- *Path Insensitive*: "At this point, `x` could be anything." (Fast, but imprecise)
- *Path Sensitive*: "If we came from the true branch, `x` is 5. If we came from false, `x`~is~0." (Precise, but expensive)

#warning-box(title: "The Dilemma")[
  We want the precision of path sensitivity without the cost of enumerating exponential paths.
  Naive enumeration is impossible.
  Naive merging is imprecise.
]

== The Solution: Symbolic Representation

We need a "Third Way."
We need a data structure that can represent *sets of paths* compactly, without listing them one by one.

#intuition-box[
  *Analogy: 20 Questions*
  Imagine trying to identify a number between 1 and 1,000,000.
  - *Enumeration:* "Is it 1? Is it 2? Is it 3? ..." (Takes 500,000 guesses on average).
  - *Symbolic (Binary Search):* "Is it greater than 500,000?" (Takes 20 guesses).

  BDDs work like the "20 Questions" game.
  Instead of listing every path, they ask a series of Yes/No questions (decisions) to efficiently narrow down the set of valid paths.
]

In this guide, we will use *Binary Decision Diagrams (BDDs)* as our symbolic representation.
BDDs will allow us to:
+ Encode the control flow logic of the program.
+ Represent huge sets of program states efficiently.
+ Perform operations on these sets (like "join" or "intersection") mathematically.

In the next chapter, we will dive into BDDs and see how they work their magic.

#chapter-summary[
  - *CFGs capture behavior.*
    We transform the hierarchical AST into a flat graph of Basic Blocks to model execution flow.

  - *Basic Blocks are atomic.*
    They are sequences of instructions that always execute together.
    Control flow only happens at the boundaries.

  - *Path Explosion is the bottleneck.*
    The number of execution paths grows exponentially with program size, making naive enumeration impossible.

  - *Symbolic Execution is the key.*
    We will use BDDs to represent and manipulate sets of paths implicitly, avoiding the explosion problem.
]
