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

The world runs on software.
But increasingly, the world also runs on *configuration*.
Cloud infrastructure, CI/CD pipelines, and firewall policies are no longer static settings managed by sysadmins.
They are *programs* written in domain-specific languages.

- A Terraform file is a program that provisions servers.
- A Kubernetes manifest is a program that orchestrates containers.
- A Firewall Policy is a program that filters packets.

Yet, while we have sophisticated tools to verify our C++ and Rust code, we often treat our infrastructure code as second-class citizens.
We "test" it by pushing it to production and seeing if the network breaks.

This guide is about bringing the rigor of *Program Analysis* to the world of infrastructure.

=== The "Program" of the Network

Consider a firewall policy.
It has variables (IP addresses, ports).
It has control flow (chains, jumps, `if/else` logic).
It has a massive input space (all possible packets).

When you write a rule like `deny tcp any any eq 80`, you are writing a line of code.
When you have 10,000 such lines, you have a complex software system.
And like any software system, it has bugs:
- *Dead Code:* Rules that are shadowed by earlier rules.
- *Infinite Loops:* Routing loops or circular chain references.
- *Logic Errors:* Allowing traffic you intended to block.

How do we find these bugs without crashing the network?

=== The Scale of the Input Space

We rely on testing --- sending packets (inputs) and checking the output.
But let's look at the math of a single packet header.

To fully test a firewall program, we need to cover the combination of all relevant input variables:
- IPv4 Source (32 bits)
- IPv4 Destination (32 bits)
- Source Port (16 bits)
- Destination Port (16 bits)
- Protocol (8 bits)

$ 32 + 32 + 16 + 16 + 8 = 104 "bits" $

The input space is $2^104$.
That is approximately $2 times 10^31$ possibilities.
If we could test *one billion packets per second*, it would still take longer than the age of the universe to test all combinations for a single policy.

Testing is like exploring a pitch-black cave with a laser pointer.
You see exactly where you point, but you have no idea what is hiding in the dark.

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
    content((w-space / 2, h-space + 0.3), text(weight: "bold")[Input Space ($2^104$ bits)])

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

== Abstract Interpretation: The Math of Analysis

To solve this, we turn to *Abstract Interpretation*.
This is the same mathematical framework used to verify critical software in avionics and medical devices.

Abstract Interpretation allows us to reason about infinite (or massive) state spaces using finite representations.
Instead of running the program with specific inputs (testing), we *analyze* the program's logic using abstract values.

In our context:
- A single *packet* is a concrete input point.
- A *rule* is an abstract shape (a volume) in the input space.
- The *policy* is a complex geometric object formed by these shapes.

We ask geometric questions about the program:
- "Does the 'Allowed Traffic' shape intersect with the 'Sensitive Data' shape?"
- "Is the 'Rule A' volume completely contained within the 'Rule B' volume?" (Dead Code)

=== Why Networks?

You might ask: "If this is a guide about Abstract Interpretation, why focus on networks?"

Networks are the perfect "Hello World" for learning Static Analysis:
+ *Finite but Huge:* The state space ($2^104$) is too big to test, but small enough to visualize.
+ *Structured:* The logic (CIDR blocks, ranges) is highly structured, making it ideal for specific data structures.
+ *Critical:* The impact of a bug is immediate and catastrophic.

By building a Firewall Checker, you will learn the core principles of Abstract Interpretation --- Lattices, Transfer Functions, Fixpoints --- in a concrete, visual domain.

== The Engine: BDDs and Rust

To implement this analysis efficiently, we need specialized tools.

+ *Binary Decision Diagrams (BDDs):*
  BDDs are a data structure that acts as a *compression engine* for boolean logic.
  They allow us to represent the complex logic of a firewall policy as a compact graph.
  They enable us to perform set operations (Union, Intersection, Difference) on the entire input space in microseconds.

+ *Rust:*
  We use Rust not just for performance, but for *correctness*.
  Rust's algebraic data types allow us to map the mathematical logic of verification directly into code.

  ```rust
  // If it compiles, we handled all cases!
  match packet_action {
      Action::Allow => log_traffic(),
      Action::Deny => drop_packet(),
      // No "default" case needed; the compiler knows we covered everything.
  }
  ```

== The Goal: Becoming a Toolsmith

The goal of this guide is not just to teach you how to verify a firewall.
It is to transform you into a *Toolsmith*.

By the end of this book, you will have built a *Symbolic Analyzer* from scratch.
You will understand how to apply Abstract Interpretation to solve complex verification problems.
You will possess the rare skill of building tools that don't just run the code, but *understand* it.

Let's build it.
