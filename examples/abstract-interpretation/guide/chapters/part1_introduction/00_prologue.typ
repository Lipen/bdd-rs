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
The software attempted to read memory from an invalid address (0x9c).
The C++ runtime, enforcing memory safety, triggered an access violation.
At the kernel level, this violation is fatal.

This was not a malicious attack.
It was not a hardware failure.
It was a failure of *verification*.

But this story is not unique.
History is littered with expensive and deadly software failures that testing missed.

=== The High Cost of Bugs

*Ariane 5 (1996):*
Thirty-seven seconds after launch, the European Space Agency's Ariane 5 rocket disintegrated.
The cause?
A 64-bit floating-point number was converted to a 16-bit signed integer.
The value was too large to fit, causing an overflow exception.
The backup computer, running the same software, failed in the exact same way.
*Cost: \$370 million and a decade of research.*

*Therac-25 (1985-1987):*
A radiation therapy machine killed or seriously injured six patients due to massive radiation overdoses.
The cause?
A race condition in the control software.
If a skilled operator typed commands too quickly, the software would configure the beam for high-power X-ray mode but deploy the target for low-power electron mode.
*Cost: Human lives.*

These disasters share a common thread:
The code passed standard testing pipelines.
It worked in the test environment.
It worked in the staging environment.
But the *input space* --- the combination of all possible variables, timings, and configurations --- was not fully explored.

#v(1em)

== The Illusion of Testing

We have built a civilization that runs on software.
Yet, our primary method for ensuring reliability --- testing --- is fundamentally incapable of guaranteeing it.

Testing is the process of checking specific points in the input space.
If we test inputs $x_1, x_2, ..., x_n$, we know the program works for those $n$ inputs.
We know *nothing* about input $x_(n+1)$.

Consider a simple function taking two 64-bit integers:

```rust
fn critical_logic(a: u64, b: u64) -> u64 { ... }
```

The input space size is $2^128 approx 3.4 times 10^38$.
If we could run one trillion tests per second, covering this space would take $10^19$ years.
The universe is only $1.38 times 10^10$ years old.

We cannot test our way to correctness.
We are searching for a needle in a haystack the size of the galaxy, and we are doing it by picking up one straw at a time.

== What is Verification?

If testing is "checking some inputs," then *verification* is "proving properties about *all* inputs."

Imagine you are designing a bridge.
- *Testing approach:* Drive a 10-ton truck over it.
  If it doesn't collapse, drive a 20-ton truck.
  Then a 30-ton truck.
- *Verification approach:* Use physics and mathematics to calculate the load-bearing capacity of the materials and the geometry of the structure.
  Prove that *for any load* up to 100 tons, the bridge will hold.

In software, we replace physics with logic.
We want to prove statements like:
- "This variable `index` is *always* within the bounds of array `buffer`."
- "This lock is *never* held by two threads simultaneously."
- "This function *always* returns a value greater than zero."

=== The Spectrum of Assurance

We can view software quality assurance as a spectrum:

+ *Unit Testing:* Checks specific, manually chosen inputs.
  (Low assurance, low cost)
+ *Fuzzing:* Checks millions of random inputs.
  Finds crashes, but cannot prove absence of bugs.
  (Medium assurance, medium cost)
+ *Static Analysis:* Checks for patterns of bugs (e.g., "use after free") without running the code.
  (High assurance, low cost, but often noisy)
+ *Formal Verification:* Mathematically proves that the code satisfies a specification for *all* possible inputs.
  (Highest assurance, high cost)

This guide focuses on a sweet spot in this spectrum: *Abstract Interpretation*.

== The Formal Alternative: Abstract Interpretation

Abstract Interpretation is a technique that allows us to reason about infinite state spaces using finite representations.
We do not run the program; we *analyze* it.

Instead of tracking the exact value of a variable (which could be anything), we track its *abstract property*.
For example, instead of knowing `x = 5`, we might know `x is Positive`.

If we know `x` is Positive and `y` is Positive, we know `x + y` is Positive.
We don't need to know the exact values to prove that the result is not negative.

We ask questions like:
- "Is it possible for *any* execution to result in a null pointer dereference?"
- "Does *every* path through this controller maintain the safety invariant?"
- "Can *any* combination of user inputs cause a buffer overflow?"

To answer these questions efficiently, we need powerful tools.
We need a way to represent the complex branching logic of modern software without succumbing to the combinatorial explosion of paths.

== Enter the BDD

This guide focuses on a specific, powerful synergy:
*Abstract Interpretation* combined with *Binary Decision Diagrams (BDDs)*.

- *Abstract Interpretation* gives us the mathematical framework to approximate data (e.g., knowing a variable is "positive" without knowing its exact value).
- *BDDs* give us the algorithmic power to handle control flow (e.g., representing millions of execution paths in a compact graph).

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
