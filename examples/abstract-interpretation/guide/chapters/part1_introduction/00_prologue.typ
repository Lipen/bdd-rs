#import "../../theme.typ": *

#counter(heading).update(0)

#heading(numbering: none)[Prologue: The Case for Static Analysis]

#reading-path(path: "essential") #h(0.5em) #reading-path(path: "beginner")

Civilization runs on abstraction.
We navigate cities with maps, not by memorizing every brick.
We predict weather with pressure and temperature, not by tracking every air molecule.
To understand complexity, we must focus on structure and ignore noise.

Yet in software, we often abandon this wisdom.
We treat programs as concrete machines to operate, not mathematical objects to understand.
We rely on testing --- running code with specific inputs --- to guess at behavior.
But modern software is extraordinarily complex.
It has zero physical tolerance: one misplaced character in a smart contract or avionics controller can cause catastrophe.

As systems grow from thousands to millions of lines, concrete approaches collapse.
Complexity is the silent killer.
To tame it, we must rediscover abstraction.
We need tools that reason about *infinite* program behaviors using *finite* representations.
We need tools that don't just run code, but *understand* it.

== The Illusion of Testing

Testing runs code and observes output to check correctness.
But testing is fundamentally optimistic.
It assumes the future resembles the past, and that chosen inputs represent reality.
For modern software, this assumption fails under the scale of state space.

Consider a simple function that takes two 64-bit integers:

```rust
fn process(a: u64, b: u64) { ... }
```

How many possible input pairs exist?
Each variable has $2^64$ possibilities. Together, they form a state space of $2^128$ combinations.
That is approximately $3.4 times 10^38$ states.

To put this in perspective: if you had a supercomputer checking one trillion inputs per second, it would take *10 trillion trillion years* to test this single function exhaustively.
The universe is only 13.8 billion years old.

But the problem runs deeper than size.
Software is *discontinuous*.
In physics, nature is smooth: a bridge that holds 10 tons likely holds 10.1 tons.
In software, this intuition breaks.
Specific values like `0`, `u64::MAX`, or particular bit patterns can trigger entirely different code paths.
Testing `x = 5` reveals nothing about `x = 0`.

== The Abstract Approach

We must stop simulating the machine point by point.
We need to reason about *all* behaviors at once.

Testing is like fishing with a spear: you catch one input at a time.
*Abstract Interpretation* is like fishing with a net: you capture entire regions of state space in one pass.

Instead of asking "What does the program do for input $A$?", we ask "What does it do for *all positive integers*?".
We replace precise concrete values with *abstract properties*.

+ Concrete: `x = 5`, `y = 10`
+ Abstract: `x > 0`, `y > 0`

If we know `x` is positive and `y` is positive, we know `x + y` is positive.
We have proven a property for *infinite* concrete cases with a single abstract rule.
We lose exact values but preserve safety properties (no overflow, no negative result).

Patrick and Radhia Cousot formalized this approach in 1977.
Their insight was revolutionary: programs can be studied by approximating semantics in a mathematically controlled way.
This unified dataflow analysis, type checking, and interval analysis into one rigorous framework.

=== The Art of Approximation

Consider: is `x * x` always non-negative?
Proving this by testing requires checking every number from negative to positive infinity.
Proving this by abstract interpretation simply observes the rule of signs.
We map infinite integers to finite abstract values:

#figure(
  table(
    columns: 3,
    align: (left, left, left),
    [*Abstract Value*], [*Meaning*], [*Examples*],
    [$+$], [Positive integers], [1, 42, 5000],
    [$0$], [Zero], [0],
    [$-$], [Negative integers], [-1, -7, -100],
    [$\top$], [Unknown], [Any integer],
  ),
  caption: [The Sign Abstract Domain],
)

By defining operations on these values, we can prove properties without running the code.
Here is how we might express this in Rust:

```rust
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Sign { Neg, Zero, Pos, Top }

impl Sign {
    fn mul(self, other: Sign) -> Sign {
        use Sign::*;
        match (self, other) {
            (Zero, _) | (_, Zero) => Zero,
            (Pos, Pos) | (Neg, Neg) => Pos,
            (Pos, Neg) | (Neg, Pos) => Neg,
            _ => Top,
        }
    }
}
```

With this small abstraction, we can prove that `x * x` is always `Pos` or `Zero` (non-negative), covering infinite inputs instantly.

=== The Machinery: Lattices and Fixpoints

Two mathematical concepts make this rigorous: *Lattices* and *Fixpoints*.

A *Lattice* provides a standard way to combine information.
If one code path says `x` is positive and another says `x` is zero, the lattice tells us how to merge these facts (into "non-negative").
It defines precision ordering: some abstract values are more precise than others.

A *Fixpoint* is the stable state of analysis.
When analyzing loops, we cannot unroll them infinitely.
Instead, we iterate until abstract facts stop changing.
Because our lattices have finite height, we reach this stable state in finite time.

This approach trades discrete for continuous:
+ A *state* is a point in 256-dimensional hyperspace.
+ A *property* (like "no overflow") is a region in this space.
+ The *program* is a trajectory moving points through space.

Verification is no longer simulation.
It is geometry.
To prove safety, we ask: "Do reachable states intersect error states?"
Converting logic to geometry lets us answer this definitively for *all* inputs.

== The Promise of Formal Methods

Why does this matter?
Because failure costs are no longer just crashed apps.
They are crashed economies or lost lives.
Formal methods, once purely academic, are now essential for securing our digital world.

+ *Hardware Verification*: Intel and AMD use these techniques to ensure CPUs add numbers correctly. A bug here means billion-dollar recalls.
+ *Smart Contracts*: Billions in DeFi are secured by symbolic analysis. Code is law here, and one reentrancy bug can drain a vault instantly.
+ *Safety-Critical Systems*: Mars Rover flight software and nuclear reactor control loops are verified, not just tested. Failures here are disasters. The Ariane 5 rocket exploded 40 seconds after launch from integer overflow. The Mars Climate Orbiter disintegrated from a unit mismatch. At 140 million miles from Earth, you cannot push a hotfix.

Mastering these tools means more than learning new algorithms.
It means learning to tame the infinite.

== The Toolsmith's Craft

This guide is for those who want to build such tools.
We will not just study theory.
We will forge a *Symbolic Analyzer* from scratch.
Building precise, durable tools requires the right materials.

=== Why Rust?
Rust offers a combination rarely found in other languages: memory safety without garbage collection, an expressive type system, and algebraic data types.
For abstract interpretation, this allows us to:
+ Prototype abstract domains using traits and enums.
+ Ensure memory safety in our analyzer without overhead.
+ Leverage a rich ecosystem of libraries.

=== Why BDDs?
Many program properties reduce to Boolean conditions ("Is this variable zero?", "Is this path reachable?").
Binary Decision Diagrams provide compact, canonical representations of Boolean functions.
They compress logic, letting us represent massive state spaces ($2^100$ and beyond) in microseconds.

=== The Roadmap
By the end of this journey, you will have:
+ *Formal Foundations*: Complete lattices, Galois connections, and fixpoint theorems.
+ *Rust Implementations*: Abstract domains (intervals, signs), control-flow graphs, and fixpoint engines.
+ *Symbolic Analysis*: Using BDDs to encode complex logic and state spaces.
+ *Visualization*: Generating diagrams to see the geometry of your analysis.

You will see software not as a black box to poke and prod, but as a crystal structure to analyze and perfect.

Let us begin.
