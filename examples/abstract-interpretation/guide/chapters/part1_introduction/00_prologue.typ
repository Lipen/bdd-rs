#import "../../theme.typ": *

#import "@preview/numbly:0.1.0"
#set heading(numbering: numbly.numbly(
  "",
  "{2}.",
  "{2}.{3}",
))

#counter(heading).update(0)

#heading(numbering: none)[Prologue: The Case for Static Analysis]

#reading-path(path: "essential") #h(0.5em) #reading-path(path: "beginner")

Every act of understanding is an act of abstraction.
Humans navigate the world not by processing every detail, but by building models.
We do not memorize the position of every brick in a city; we use a map.
We do not track the motion of every molecule in a gas; we measure temperature.
We survive by ignoring the noise to focus on the structure.

In software, however, we often abandon this wisdom.
We treat our systems as concrete machines to be operated, rather than mathematical objects to be understood.
We rely on testing --- running the code with specific inputs --- to guess at its behavior.
But a modern software system is likely the most complex artifact ever constructed by human hands.
It has no physical tolerance; a single misplaced character in a smart contract or an avionics controller can lead to catastrophe.

As our systems grow from thousands of lines to millions, the concrete approach is collapsing.
Complexity is the silent killer.
To tame it, we must rediscover the art of abstraction.
We need tools that allow us to reason about the *infinite* behaviors of our software using *finite* representations.
We need tools that don't just run our code, but *understand* it.

== The Illusion of Testing

We typically rely on testing to ensure correctness --- running the code and observing the output.
But testing is an act of optimism.
It assumes that the future will look like the past, and that the inputs we choose are representative of reality.
In the context of modern hardware and software, this assumption collapses under the weight of the combinatorial explosion.

Consider a simple 64-bit floating-point multiplier:

+ Input A: 64 bits
+ Input B: 64 bits
+ Internal State: ~128 bits (pipeline registers, control logic)

The total state space is $2^(64+64+128) = 2^256$.

This number is difficult to comprehend.
It is orders of magnitude larger than the number of atoms in the observable universe.
If we could test one trillion states per nanosecond, the sun would burn out long before we covered even a fraction of a percent.

But the problem is deeper than just size.
Software is *discontinuous*.
In the physical world, small changes in input usually lead to small changes in output.
If you build a bridge and the load increases by 1%, the stress increases by roughly 1%.
In software, a single bit flip --- a buffer overflow, a race condition, an integer wrap-around --- can cause the entire system to diverge wildly from its intended behavior.
This discontinuity makes extrapolation impossible.
We cannot assume that because the system works for $N$ inputs, it will work for $N+1$.

#figure(
  caption: [Testing vs. Verification. Testing checks individual inputs (green). Verification analyzes the logic of the program itself (blue).],
  cetz.canvas({
    import cetz.draw: *

    // --- Styles & Helpers ---
    let style-space = (fill: colors.bg-subtle, stroke: colors.text-light + 1pt)
    let style-test = (fill: colors.success, stroke: none, radius: 0.08)
    let style-verify = (fill: colors.primary.lighten(80%), stroke: colors.primary + 1pt)

    // --- Layout Constants ---
    let w-space = 6
    let h-space = 4
    let x-verify = 4.5
    let y-verify = 2.5

    // Input Space
    rect((0, 0), (w-space, h-space), ..style-space, name: "space")
    content((w-space / 2, h-space + 0.3), text(weight: "bold")[State Space ($2^256$ states)])

    // Testing (Scattered points)
    for i in range(15) {
      let x = calc.rem(i * 7 + 3, 55) / 10.0 + 0.2
      let y = calc.rem(i * 3 + 2, 35) / 10.0 + 0.2
      circle((x, y), ..style-test)
    }
    content((1, 0.5), text(size: 0.8em, fill: colors.success)[Tests])

    // Verification (Covered region)
    rect((x-verify - 1, y-verify - 1), (x-verify + 1, y-verify + 1), ..style-verify, name: "region")
    content("region", align(center, text(size: 0.8em, fill: colors.primary)[Verified \ Logic]))

    // Bug (Uncovered)
    circle((5.2, 0.8), radius: 0.1, fill: colors.error, stroke: none, name: "bug")
    content((5.2, 0.4), text(size: 0.8em, fill: colors.error)[Bug])
  }),
)

== The Analyst's Lens

To solve this, we need a different kind of tool.
Testing is like exploring a dark forest with a flashlight.
You see exactly where you point the beam, but you remain blind to the wolves lurking in the shadows behind you.
Fuzzing is like running through that forest with a strobe light; you see more, but the chaos remains.

What if we had a tool that wasn't a light, but a *lens*?

*Abstract Interpretation* is that lens.
It does not try to visit every tree in the forest.
Instead, it allows us to stand above the canopy and see the shape of the woods.
It cannot show us the color of every leaf (that would be the concrete execution), but it can tell us with absolute certainty where the cliffs are, where the rivers flow, and which paths lead to dead ends.

=== The Art of Approximation

Consider a simple question: is `x * x` always non-negative?
To prove this by testing, you would need to plug in every number from negative infinity to positive infinity.
To prove this by abstract interpretation, you simply observe the rule of signs:
- A positive times a positive is a positive.
- A negative times a negative is a positive.
- Zero times zero is zero.

You have just performed an analysis.
You mapped the infinite set of integers to a finite set of abstract values: `{+, -, 0}`.
By reasoning about these abstract values, you proved a property for an infinite number of inputs without running the code a single time.

In our geometric framework, this lens allows us to trade the discrete for the continuous:
+ A *state* is a single point in a 256-dimensional hyperspace.
+ A *property* (like "no overflow") is a region in this space.
+ The *program* is a trajectory that moves points through this space.

Verification, then, is no longer about simulation.
It is about geometry.
To prove safety, we ask: "Does the set of all reachable states intersect with the set of error states?"
By converting logic into geometry, we can answer these questions definitively for *all* inputs at once.

== The Promise of Formal Methods

Why does this matter?
Because the cost of failure is no longer just a crashed app; it is a crashed economy or a lost life.
Formal methods, once the domain of academic theory, are now the only way to secure the foundations of our digital world.

+ *Hardware Verification*: Intel and AMD use these techniques to ensure that your CPU adds numbers correctly. A bug here is not patchable; it is a billion-dollar recall.
+ *Smart Contracts*: Billions of dollars in DeFi are secured by symbolic analysis. In this world, code is law, and a single reentrancy bug can drain a vault in seconds.
+ *Safety-Critical Systems*: The flight software of the Mars Rover and the control loops of nuclear reactors are verified, not just tested. When you are 140 million miles from Earth, you cannot push a hotfix.

By mastering these tools, you are not just learning a new algorithm.
You are learning how to tame the infinite.

== The Toolsmith's Craft

This guide is written for those who want to build such tools.
We will not just study the theory; we will forge a *Symbolic Analyzer* from scratch.
To build a tool that is both precise and durable, we need the right materials.

+ *Rust is the Foundation*: We use Rust not just for speed, but for its algebraic type system. It allows us to encode the mathematical laws of our analysis directly into the compiler, making invalid states unrepresentable.
+ *BDDs are the Engine*: We use Binary Decision Diagrams (BDDs) as the computational core. They act as a compression engine for logic, allowing us to represent massive state spaces ($2^100$ and beyond) in microseconds.

By the end of this journey, you will possess a rare and powerful skill: the ability to build tools that don't just run code, but *understand* it.
You will see software not as a black box to be poked and prodded, but as a crystal structure to be analyzed and perfected.

Let us begin.
