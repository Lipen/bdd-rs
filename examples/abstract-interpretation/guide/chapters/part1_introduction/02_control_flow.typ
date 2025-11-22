// Chapter 2: Control Flow and the CFG

#import "../../theme.typ": *

= Control Flow and the CFG <ch-control-flow>

In the previous chapter, we defined the syntax of IMP using an Abstract Syntax Tree (AST).
While ASTs are great for parsing, they are awkward for analysis.
To analyze how a program executes, we need a *Control Flow Graph* (CFG).

== From AST to CFG

An AST is hierarchical (a tree). Execution is sequential and sometimes cyclic (loops).
A CFG flattens the hierarchy into a graph where:
- *Nodes* are Basic Blocks (sequences of instructions).
- *Edges* represent control flow (jumps and branches).

=== The MiniVerifier CFG

Standard CFGs group instructions into *Basic Blocks*.
A basic block is a sequence of instructions with a single entry and single exit.
Control flow only happens at the end of a block (the *terminator*).

```rust
type BlockId = usize;

#[derive(Clone, Debug)]
pub struct BasicBlock {
    pub id: BlockId,
    pub instructions: Vec<Instruction>,
    pub terminator: Terminator,
}

#[derive(Clone, Debug)]
pub enum Instruction {
    Assign(String, Expr),  // x = e
    Assert(Expr),          // assert(e)
}

#[derive(Clone, Debug)]
pub enum Terminator {
    Goto(BlockId),
    Branch {
        condition: Expr,
        true_target: BlockId,
        false_target: BlockId,
    },
    Return,
}

pub struct ControlFlowGraph {
    pub blocks: HashMap<BlockId, BasicBlock>,
    pub entry: BlockId,
}
```

=== Translating IMP to CFG

Let's see how we translate IMP statements into basic blocks.

*1. Assignment (`x = e`)*
Appended to the current basic block's instruction list.

*2. Sequence (`s1; s2`)*
We compile `s1`, then `s2` into the current flow.
If `s1` ends a block (e.g., with a branch), `s2` starts a new block.

*3. Conditional (`if c { t } else { e }`)*
    Terminates the current block with a `Branch` terminator.
- Creates a "then" block and an "else" block.
- Both branches eventually merge at a new "join" block.

*4. Loop (`while c { body }`)*
- Current block jumps to a new "header" block.
- Header block contains the condition `c`.
- If true, jump to "body" block.
- If false, jump to "exit" block.
- Body block jumps back to header.

These rules might seem abstract at first.
To solidify your understanding, here's a complete implementation that transforms AST nodes into basic blocks:

#example-reference(
  "control_flow",
  "cfg_builder.rs",
  "cfg_builder",
  [
    Implementation of CFG construction from IMP AST.
    Shows how to translate assignments, conditionals, and loops into basic blocks with proper control flow edges.
  ],
)

#figure(
  caption: [CFG for a simple loop `while x < 10 { x = x + 1 }`. Nodes are basic blocks containing instructions. Edges represent control flow.],

  cetz.canvas({
    import cetz.draw: *

    // Helper functions
    let draw-block(pos, label, content-text, is-start: false, is-end: false) = {
      let color = if is-start { colors.accent } else if is-end { colors.success } else { colors.primary }
      rect(
        (pos.at(0) - 1.5, pos.at(1) - 0.8),
        (pos.at(0) + 1.5, pos.at(1) + 0.8),
        fill: white,
        stroke: color + 1.5pt,
        name: label
      )
      content(label, text(size: 0.8em)[#content-text])
    }

    // Layout
    let l0 = (0, 4) // Header
    let l1 = (0, 0) // Body
    let l2 = (4, 4) // Exit

    // Header Block
    draw-block(l0, "header", [*Header* \ `if x < 10`], is-start: true)

    // Body Block
    draw-block(l1, "body", [*Body* \ `x = x + 1` \ `goto Header`])

    // Exit Block
    draw-block(l2, "exit", [*Exit* \ `return`], is-end: true)

    // Edges
    // Header -> Body (True)
    line("header.south", "body.north", stroke: colors.text-light + 1pt, mark: (end: ">"))
    content((0.5, 2), text(size: 0.7em)[True])

    // Header -> Exit (False)
    line("header.east", "exit.west", stroke: colors.text-light + 1pt, mark: (end: ">"))
    content((2, 4.2), text(size: 0.7em)[False])

    // Body -> Header (Back edge)
    // Use anchors to make it look like a loop
    line("body.west", (rel: (-1, 0)), (rel: (0, 4)), "header.west", stroke: colors.text-light + 1pt, mark: (end: ">"))

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
    We translate the hierarchical AST into a graph of Basic Blocks.
  ],
  [
    *Basic Blocks contain instructions.*
    Assignments update the state; Terminators (branches) control the flow.
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
