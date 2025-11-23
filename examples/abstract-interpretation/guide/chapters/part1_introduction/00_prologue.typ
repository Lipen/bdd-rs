#import "../../theme.typ": *

#counter(heading).update(0)

#heading(numbering: none)[Prologue: The Case for Verification]

#reading-path(path: "essential") #h(0.5em) #reading-path(path: "beginner")

_July 19, 2024._
_Global IT Infrastructure._

A routine sensor configuration update is pushed to millions of Windows hosts.
Within minutes, critical infrastructure across the globe grinds to a halt.
Airlines ground flights.
Hospitals cancel surgeries.
Emergency services go offline.
The "Blue Screen of Death" appears on 8.5 million devices.

The cause?
A logic error in the CrowdStrike Falcon sensor.
Specifically, the software attempted to read memory from an invalid address (0x9c).
This was an *out-of-bounds read*.
The C++ runtime, enforcing memory safety, triggered an access violation.
At the kernel level, this violation is fatal.

This was not a malicious attack.
It was not a hardware failure.
It was a failure of *verification*.
A static analysis tool capable of tracking value ranges could have proven that the offset `0x9c` was invalid for the given buffer.

But this story is not unique.
History is littered with expensive and deadly software failures that testing missed.

=== The High Cost of Bugs

*Ariane 5 (1996):*
Thirty-seven seconds after launch, the European Space Agency's Ariane 5 rocket disintegrated.
The cause?
A 64-bit floating-point number was converted to a 16-bit signed integer.
The value was too large to fit, causing an overflow exception.
*Cost: \$370 million and a decade of research.*

*Therac-25 (1985-1987):*
A radiation therapy machine killed or seriously injured six patients due to massive radiation overdoses.
The cause?
A race condition in the control software.
*Cost: Human lives.*

These disasters share a common thread:
The code passed standard testing pipelines.
It worked in the test environment.
But the *input space* --- the combination of all possible variables, timings, and configurations --- was not fully explored.

#v(1em)

== The Illusion of Testing

We have built a civilization that runs on software.
Yet, our primary method for ensuring reliability --- testing --- is fundamentally incapable of guaranteeing it.

Testing is the process of checking specific points in the input space.
If we test inputs $x_1, x_2, ..., x_n$, we know the program works for those $n$ inputs.
We know *nothing* about input $x_(n+1)$.

#figure(
  caption: [Testing vs. Verification. Testing checks individual points (green dots). Verification proves properties about the entire input space (blue region).],
  cetz.canvas({
    import cetz.draw: *

    let style-space = (fill: colors.bg-subtle, stroke: colors.text-light + 1pt)
    let style-test = (fill: colors.success, stroke: none, radius: 0.08)
    let style-verify = (fill: colors.primary.lighten(80%), stroke: colors.primary + 1pt)

    // Input Space
    rect((0, 0), (6, 4), ..style-space, name: "space")
    content((3, 4.3), text(weight: "bold")[Input Space ($2^{128}$ states)])

    // Testing (Scattered points)
    for i in range(15) {
      let x = calc.rem(i * 7 + 3, 55) / 10.0 + 0.2
      let y = calc.rem(i * 3 + 2, 35) / 10.0 + 0.2
      circle((x, y), ..style-test)
    }
    content((1, 0.5), text(size: 0.8em, fill: colors.success)[Tests])

    // Verification (Covered region)
    rect((3.5, 1.5), (5.5, 3.5), ..style-verify)
    content((4.5, 2.5), text(size: 0.8em, fill: colors.primary)[Verified Region])

    // Bug (Uncovered)
    circle((5.2, 0.8), radius: 0.1, fill: colors.error, stroke: none)
    content((5.2, 0.4), text(size: 0.8em, fill: colors.error)[Bug])

    // Arrow from verified to bug (showing it missed? No, verification covers regions)
    // Let's show that testing missed the bug
  }),
)

Consider a simple function taking two 64-bit integers:

```rust
fn critical_logic(a: u64, b: u64) -> u64 { ... }
```

The input space size is $2^128 approx 3.4 times 10^38$.
If we could run one trillion tests per second, covering this space would take $10^19$ years.
We cannot test our way to correctness.

== What is Verification?

If testing is "checking some inputs," then *verification* is "proving properties about *all* inputs."

In software, we use logic and mathematics to prove statements like:
- "This variable `index` is *always* within the bounds of array `buffer`."
- "This lock is *never* held by two threads simultaneously."
- "This function *always* returns a value greater than zero."

=== The Spectrum of Assurance

We can view software quality assurance as a spectrum:

+ *Unit Testing:* Checks specific, manually chosen inputs.
+ *Fuzzing:* Checks millions of random inputs.
+ *Static Analysis:* Checks for patterns of bugs without running the code.
+ *Formal Verification:* Mathematically proves that the code satisfies a specification for *all* possible inputs.

This guide focuses on a sweet spot in this spectrum: *Abstract Interpretation*.

== The Formal Alternative: Abstract Interpretation

Abstract Interpretation is a technique that allows us to reason about infinite state spaces using finite representations.
We do not run the program; we *analyze* it.

Instead of tracking the exact value of a variable (which could be anything), we track its *abstract property*.
For example, instead of knowing `x = 5`, we might know `x is Positive`.

If we know `x` is Positive and `y` is Positive, we know `x + y` is Positive.
We don't need to know the exact values to prove that the result is not negative.

== The Challenge: Combinatorial Explosion

However, abstract interpretation faces a massive hurdle: *Control Flow*.
Every `if` statement splits the execution path.
Every loop multiplies the number of paths.
A program with just 100 branches can have $2^100$ execution paths.

Naive analysis either:
1.  *Explodes*: Tries to track every path and runs out of memory.
2.  *Gives Up*: Merges all paths together, losing precision (e.g., concluding "x could be anything").

== Enter the BDD

This guide focuses on a specific, powerful synergy:
*Abstract Interpretation* combined with *Binary Decision Diagrams (BDDs)*.

*BDDs* are the secret weapon against combinatorial explosion.
They allow us to represent and manipulate *sets of paths* implicitly.
Instead of listing $2^100$ paths, a BDD might represent them with a graph of just a few hundred nodes.

Together, they enable *Path-Sensitive Analysis*: verification that understands how data values change depending on the path taken through the code, yet scales to real-world problems.

== The Journey Ahead

This is not just a theoretical textbook.
It is a practical guide to building verification tools in Rust.
We chose Rust because it is the language of modern systems programming, and its type system aligns beautifully with the goals of verification.

We will start from first principles:
+ *Abstraction:* How to trade precision for speed.
+ *Control Flow:* Why loops are the enemy of analysis.
+ *Symbolic Logic:* How BDDs crush combinatorial complexity.

Then, we will build a complete *Symbolic Executor* capable of proving properties that testing would miss.

The CrowdStrike incident demonstrated the fragility of our digital world.
It is our responsibility as engineers to build systems that are not just "probably" correct, but *provably* robust.

Let us begin.
