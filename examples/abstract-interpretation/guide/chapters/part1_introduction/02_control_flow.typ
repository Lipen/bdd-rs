// Chapter 2: Packet Flow and the Chain Graph

#import "../../theme.typ": *

= Packet Flow and the Chain Graph <ch-control-flow>

In the previous chapter, we defined the syntax of our Firewall Policy using an Abstract Syntax Tree (AST).
While ASTs are excellent for representing the *structure* of the policy (how it is written), they are often awkward for analyzing its *behavior* (how packets flow).

To analyze a policy, we need to view it not as a hierarchy of rules, but as a network of possible packet paths.
This representation is called the *Chain Graph* (often called Control Flow Graph or CFG in software).

#insight-box[
  *Analogy:* Think of an AST as a *Rule Book* --- it lists regulations chapter by chapter.
  A Chain Graph is like a *Traffic Map* --- it shows how vehicles (packets) actually move through the intersections and roads.
]

== From AST to Chain Graph

An AST is recursive and hierarchical.
Packet processing, however, is sequential (rule-by-rule) and sometimes jumps between chains.
A Chain Graph "flattens" the recursive structure into a graph.

#definition(title: "Chain Graph")[
  A *Chain Graph* $G = (V, E)$ consists of:
  - *Nodes* $V$: Rule Blocks (sequences of straight-line rules).
  - *Edges* $E$: Flow transitions (jumps, branches) between blocks.
]

=== The Rule Block

The fundamental unit of a Chain Graph is the *Rule Block*.

#definition(title: "Rule Block")[
  A *Rule Block* is a maximal sequence of rules with:
  + *Single Entry*: Packets can only enter at the first rule.
  + *Single Exit*: Packets can only leave from the last rule (the "terminator").
  + *Atomic Execution*: If the first rule executes, all subsequent rules in the block are guaranteed to execute (unless a match diverts the flow).
]

=== The Firewall Chain Structure

In our Rust implementation, we represent the Chain Graph as a collection of blocks, identified by unique integers (`BlockId`).

```rust
type BlockId = usize;

#[derive(Clone, Debug)]
pub struct RuleBlock {
    pub id: BlockId,
    pub rules: Vec<Rule>,       // The straight-line rules (e.g., ModField)
    pub terminator: Terminator, // How we leave the block
}

#[derive(Clone, Debug)]
pub enum Terminator {
    // Unconditional jump to another chain/block
    Jump(BlockId),
    // Conditional branch based on a packet match
    Branch {
        match_rule: Match, // Uses the Match type from our AST
        true_target: BlockId,
        false_target: BlockId,
    },
    // Final verdict
    Accept,
    Drop,
}
```

== Translating Policy to Chain Graph

The translation process involves breaking down complex AST nodes (like `Match` trees) into simple blocks and edges.
Let's visualize how each structure is transformed.

=== Sequence (`r1; r2`)

Sequences are simply concatenated.
If `r1` is just a modification (like NAT), `r2` is appended to it.
If~`r1` contains control flow (like a `Match`), it will end the current block, and `r2` will start in a new block that the previous blocks jump to.

=== Match (`match m { t } else { e }`)

A match rule splits the packet flow into two paths that eventually merge.

#figure(
  caption: [Translation of `match m { t } else { e }` into Chain Graph blocks.],
  cetz.canvas({
    import cetz.draw: *

    let style-block = (fill: colors.bg-subtle, stroke: colors.primary + 1pt)

    // Nodes
    rect((0, 0), (3, 1.5), ..style-block, name: "cond")
    content("cond", [*Header* \ `Branch(m)`])

    rect((-3.5, -3), (-0.5, -1.5), ..style-block, name: "then")
    content("then", [*True Chain* \ `t`])

    rect((0, -3), (3, -1.5), ..style-block, name: "else")
    content("else", [*False Chain* \ `e`])

    rect((0, -5.5), (3, -4), ..style-block, name: "join")
    content("join", [*Join Block* \ (next rule)])

    // Edges
    line(
      "cond.west",
      ((), "-|", "then.north"),
      "then.north",
      mark: (end: ">"),
      name: "true-edge",
    )
    content("true-edge.25%", text(size: 0.8em, fill: colors.success)[Match], anchor: "south", padding: 0.2)

    line("cond.south", "else.north", mark: (end: ">"), name: "false-edge")
    content("false-edge.mid", text(size: 0.8em, fill: colors.error)[No Match], anchor: "west", padding: 0.2)

    line(
      "then.south",
      ((), "|-", "join.west"),
      "join.west",
      mark: (end: ">"),
    )
    line("else.south", "join.north", mark: (end: ">"))
  }),
)

=== Routing Loops

While rare in simple ACLs, routing loops can occur in complex networks.
We need a "Header" block to evaluate the routing decision every time the packet loops.

#figure(
  caption: [Translation of a routing loop into Chain Graph blocks.],
  cetz.canvas({
    import cetz.draw: *

    let style-block = (fill: colors.bg-subtle, stroke: colors.primary + 1pt)

    // Nodes
    rect((0, -1), (3, 0.5), ..style-block, name: "header")
    content("header", [*Router* \ `Forward`])

    rect((0, -4), (3, -2.5), ..style-block, name: "body")
    content("body", [*Next Hop* \ `Process`])

    rect((4.5, -1), (7, 0.5), ..style-block, name: "exit")
    content("exit", [*Destination*])

    // Edges
    line((1.5, 1.5), "header.north", mark: (end: ">")) // Entry

    line("header.south", "body.north", mark: (end: ">"), name: "loop-edge")
    content("loop-edge.mid", text(size: 0.8em, fill: colors.success)[Route], anchor: "west", padding: 0.2)

    line("header.east", "exit.west", mark: (end: ">"), name: "exit-edge")
    content("exit-edge.mid", text(size: 0.8em, fill: colors.error)[Arrive], anchor: "south", padding: 0.2)

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
Why is network verification so hard?

The answer lies in the structure of the Chain Graph.
Every time we encounter a branch (like a `Match` rule), the number of possible packet flows multiplies.

Consider a sequence of just 3 independent matches:

```rust
match tcp { ... }
match port_80 { ... }
match src_internal { ... }
```

This creates $2 times 2 times 2 = 8$ flows.
For $N$ rules, we have $2^N$ flows.
This is *exponential growth*.

#figure(
  caption: [Visualizing Flow Explosion. As packets match rules, the number of distinct packet states we must track doubles at each step.],
  cetz.canvas({
    import cetz.draw: *

    let style-node = (fill: colors.primary, radius: 0.15)
    let style-state = (fill: colors.bg-code, stroke: colors.text-light + 0.5pt, radius: 0.1)

    // Level 0
    circle((0, 0), ..style-node, name: "n0")
    content((0, 0.5), text(size: 0.7em)[State: {}])

    // Level 1
    circle((-2, -1.5), ..style-node, name: "n1l")
    content((-2.5, -1.5), text(size: 0.7em)[{TCP}], anchor: "east")
    circle((2, -1.5), ..style-node, name: "n1r")
    content((2.5, -1.5), text(size: 0.7em)[{!TCP}], anchor: "west")

    // Level 2
    circle((-3, -3), ..style-node, name: "n2ll")
    content((-3, -3.5), text(size: 0.7em)[{TCP, 80}])

    circle((-1, -3), ..style-node, name: "n2lr")
    content((-1, -3.5), text(size: 0.7em)[{TCP, !80}])

    circle((1, -3), ..style-node, name: "n2rl")
    content((1, -3.5), text(size: 0.7em)[{!TCP, 80}])

    circle((3, -3), ..style-node, name: "n2rr")
    content((3, -3.5), text(size: 0.7em)[{!TCP, !80}])

    // Edges
    line("n0", "n1l", stroke: 0.5pt + colors.text-light)
    line("n0", "n1r", stroke: 0.5pt + colors.text-light)

    line("n1l", "n2ll", stroke: 0.5pt + colors.text-light)
    line("n1l", "n2lr", stroke: 0.5pt + colors.text-light)
    line("n1r", "n2rl", stroke: 0.5pt + colors.text-light)
    line("n1r", "n2rr", stroke: 0.5pt + colors.text-light)

    // Ellipsis for further explosion
    content((0, -4.5), text(size: 1.2em, fill: colors.error)[$2^N$ Flows!])
  }),
)

If we have a routing loop that iterates 100 times, it is conceptually similar to 100 nested `match` statements.
The number of flows becomes astronomical.

=== Path Sensitivity vs. Scalability

We want our analysis to be *Path Sensitive*.
This means distinguishing between different packet histories.

- *Path Insensitive*: "At this point, `src_ip` could be anything." (Fast, but imprecise)
- *Path Sensitive*: "If we matched the VPN rule, `src_ip` is Internal. If we matched the Public rule, `src_ip`~is~External." (Precise, but expensive)

#warning-box(title: "The Dilemma")[
  We want the precision of path sensitivity without the cost of enumerating exponential flows.
  Naive enumeration is impossible.
  Naive merging is imprecise.
]

== The Solution: Symbolic Representation

We need a "Third Way."
We need a data structure that can represent *sets of packets* compactly, without listing them one by one.

#intuition-box[
  *Analogy: 20 Questions*
  Imagine trying to identify a number between 1 and 1,000,000.
  - *Enumeration:* "Is it 1? Is it 2? Is it 3? ..." (Takes 500,000 guesses on average).
  - *Symbolic (Binary Search):* "Is it greater than 500,000?" (Takes 20 guesses).

  BDDs work like the "20 Questions" game.
  Instead of listing every packet, they ask a series of Yes/No questions (decisions) to efficiently narrow down the set of valid packets.
]

In this guide, we will use *Binary Decision Diagrams (BDDs)* as our symbolic representation.
BDDs will allow us to:
+ Encode the matching logic of the policy.
+ Represent huge sets of packet headers efficiently.
+ Perform operations on these sets (like "join" or "intersection") mathematically.

In the next chapter, we will dive into BDDs and see how they work their magic.

#chapter-summary[
  - *Chain Graphs capture behavior.*
    We transform the hierarchical AST into a flat graph of Rule Blocks to model packet flow.

  - *Rule Blocks are atomic.*
    They are sequences of rules that always execute together.
    Flow branching only happens at the boundaries.

  - *Flow Explosion is the bottleneck.*
    The number of packet flows grows exponentially with policy size, making naive enumeration impossible.

  - *Symbolic Execution is the key.*
    We will use BDDs to represent and manipulate sets of packets implicitly, avoiding the explosion problem.
]
