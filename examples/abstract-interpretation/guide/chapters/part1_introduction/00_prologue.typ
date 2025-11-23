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

We live in an age of invisible infrastructure.
Every time you step onto a plane, swipe a credit card, or undergo a medical scan, you are placing your trust in a silent, invisible web of logic.
For decades, we have built this web using a philosophy of "good enough".
We write code, we write tests, and if the tests pass, we ship.
But as our systems grow from thousands of lines to millions, "good enough" is becoming dangerous.
Software is no longer just a tool for efficiency; it is the structural steel of modern civilization.
And unlike steel, it buckles without warning.

The problem is not that we are bad engineers.
The problem is that we are fighting a losing battle against complexity.
A modern piece of software is likely the most complex artifact ever constructed by human hands.
It has no physical tolerance; a single misplaced character can bring down a global network.
To tame this complexity, we need better tools.
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

The total state space is $2^(64+64+128) = 2^(256)$.

This number is difficult to comprehend.
It is orders of magnitude larger than the number of atoms in the observable universe.
If we could test one trillion states per nanosecond, the sun would burn out long before we covered even a fraction of a percent.

But the problem is deeper than just size.
Software is *discontinuous*.
In the physical world, small changes in input usually lead to small changes in output.
If you build a bridge and the load increases by 1%, the stress increases by roughly 1%.
In software, a single bit flip --- a buffer overflow, a race condition, an integer wrap-around --- can cause the entire system to diverge wildly from its intended behavior.
Testing is like exploring a pitch-black continent with a flashlight; you see exactly where you point, but you remain ignorant of the vast darkness surrounding you.
To guarantee correctness, we must abandon the hope of exhaustive testing and instead analyze the infinite through the lens of the finite.

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

== A Different Way of Seeing

To solve this, we turn to *Abstract Interpretation*.
This formal method allows us to reason about software properties without executing the code.
It invites us to stop thinking about individual execution traces (the concrete domain) and start thinking about the *shape* of the program's behavior (the abstract domain).

Imagine you want to prove that `x * x` is always non-negative.
You don't need to plug in every number from negative infinity to positive infinity.
You simply observe the rule: "A negative times a negative is a positive. A positive times a positive is a positive."
You have just performed an abstract interpretation.
You mapped the infinite set of integers to a finite set of signs: `{+, -, 0}`.
By reasoning about these signs, you proved a property for an infinite number of inputs.

In our geometric framework, we trade the discrete for the continuous:
+ A *state* is a single point in a 256-dimensional hyperspace.
+ A *property* (like "no overflow") is a region in this space.
+ The *program* is a trajectory that moves points through this space.

Verification, then, is no longer about simulation.
It is about geometry.
To prove safety, we ask: "Does the set of all reachable states intersect with the set of error states?"
To prove liveness, we ask: "Does every trajectory eventually enter the 'success' region?"
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

== The Journey Ahead

This guide is an invitation to stop being a user of tools and start being a maker of them.
We will build a *Symbolic Analyzer* from scratch, relying on two pillars:

+ *Rust*: We use Rust not just for speed, but for its algebraic type system. We will use the type system to encode the logic of our verifier, making invalid states unrepresentable.
+ *Binary Decision Diagrams (BDDs)*: We will use BDDs as a compression engine for logic. They will allow us to represent and manipulate massive state spaces ($2^(100)$ and beyond) in microseconds, performing set operations that would be impossible with standard arrays or lists.

By the end of this journey, you will possess a rare and powerful skill: the ability to build tools that don't just run code, but *understand* it.
You will see software not as a black box to be poked and prodded, but as a crystal structure to be analyzed and perfected.

Let us begin.
