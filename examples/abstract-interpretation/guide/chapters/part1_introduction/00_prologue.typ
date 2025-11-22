#import "../../theme.typ": *

#counter(heading).update(0)

#heading(numbering: none)[Prologue: The Software Verification Challenge]

#reading-path(path: "essential") #h(0.5em) #reading-path(path: "beginner")

_November 4, 1996.
Paris, France._

The inaugural flight of the Ariane 5 rocket --- Europe's most advanced launch vehicle --- lasted 37 seconds.
The rocket carried four satellites worth over \$500 million.
It veered off course and was destroyed.

The cause: a software bug inherited from the Ariane 4 without revalidation.
A 64-bit floating-point number representing horizontal velocity was converted to a 16-bit signed integer.
The value exceeded 32,767 (the maximum for a 16-bit signed integer).
No overflow protection was implemented --- the code threw an exception.
This caused cascading failures in the inertial reference system.
Both the primary and backup systems failed identically from the same bug.

The inquiry board's report stated:
_"The failure could have been avoided by... appropriate protection against overflow."_

The defective code worked correctly in the Ariane 4, where horizontal velocities never exceeded the threshold.
Ariane 5's more powerful engines produced higher acceleration.
The assumption that certain values would remain bounded no longer held.

#v(1em)

_June 1985-1987.
Multiple medical facilities._

The Therac-25 radiation therapy machine delivered massive overdoses to at least six patients.
Three died from radiation poisoning.
Three others suffered severe radiation injuries.

The bug emerged from the interaction of three factors:
Race conditions in the control software allowed the operator to modify treatment parameters during a brief timing window.
The software lacked proper synchronization between the operator console and the machine controller.
Hardware safety interlocks present in previous models had been removed, with their function moved to software.

When an operator corrected a data entry error within approximately eight seconds, the software entered an inconsistent state.
The machine configured itself to deliver the electron beam at full power without the beam spreader plate in position.
Patients received doses hundreds of times higher than intended.

The race condition occurred so rarely during testing that it went undetected.
Only experienced operators, who worked quickly and knew common data entry patterns, triggered the bug frequently enough to cause injury.

#v(1em)

_April 2014._

Heartbleed was discovered in OpenSSL --- software protecting approximately two-thirds of all web servers.
The vulnerability allowed attackers to read arbitrary server memory.
This exposed passwords, cryptographic keys, and personal data.
The bug: a missing bounds check in the heartbeat extension.

```c
// Vulnerable code (simplified)
int length = request.length;  // Attacker-controlled
char* response = malloc(length);
memcpy(response, data, length);  // No validation of 'data' size
```

#v(1em)

== Testing is Insufficient

These failures share a pattern:
they involve logical errors that testing alone cannot reliably detect.
The programs executed correctly under test conditions.
They passed their test suites.
Under specific production conditions, they failed catastrophically.

Testing encounters fundamental limitations:

_Infinite input space._
A function accepting two 32-bit integers has $2^(64) approx 1.8 times 10^19$ possible inputs.
Testing one input per nanosecond would require over 580 years to cover all cases.

_Rare conditions._
Defects often manifest only under unusual input combinations, timing windows, or state sequences.
The Therac-25 race condition required specific timing (sub-second window) combined with specific operator behavior.
Testing finds common-case bugs effectively.
Rare bugs persist until they occur in production.

_Emergent complexity._
Modern systems comprise multiple interacting components.
Component interactions create emergent behaviors not captured by unit testing.
The Ariane 5 software worked correctly in isolation.
It failed when integrated with a system producing different operating conditions.

Consider this function:

```rust
fn divide(x: i32, y: i32) -> i32 {
    x / y
}
```

Testing validates several cases:
- `divide(10, 2)` returns `5`
- `divide(7, 3)` returns `2`
- `divide(-10, 2)` returns `-5`
- `divide(0, 5)` returns `0`

The function appears correct.
However, `divide(10, 0)` causes a runtime panic.
`divide(i32::MIN, -1)` triggers overflow.

We could add more tests.
But how do we determine when testing is sufficient?
How do we guarantee coverage of all cases?

== Formal Verification

Instead of testing individual inputs, we seek to prove program correctness for _all possible inputs_.

Mathematical verification can guarantee:
- No division by zero occurs
- Array accesses remain in bounds
- Arithmetic operations do not overflow
- Pointers reference valid memory
- Concurrent operations are properly synchronized

Formal verification replaces testing's "probably works" with mathematics' "provably correct."

#example-box(number: "0.1", title: "Loop Invariant Verification")[
  Consider this array processing loop:

  ```rust
  fn process_array(arr: &mut [i32]) {
      let mut i = 0;
      while i < arr.len() {
          arr[i] = arr[i] * 2;
          i += 1;
      }
  }
  ```

  Property to verify: `arr[i]` never accesses beyond bounds.

  We establish the loop invariant:
  $ 0 <= i <= "arr.len()" $

  - *Initially*: `i = 0`, so $0 <= 0 <= "arr.len()"$
  - *Loop body*: If invariant holds and $i < "arr.len()"$, then `arr[i]` is safe
  - *After increment*: `i += 1` maintains $i <= "arr.len()"$
  - *Termination*: Loop exits when $i >= "arr.len()"$

  By mathematical induction, all accesses are safe.
  No testing required --- we have a proof.
]

== The Challenge

Complete verification is computationally intractable for most programs.

#historical-note(
  person: "Alan Turing",
  year: "1936",
  title: "The Halting Problem",
  image-path: none,
)[
  Turing proved that _no algorithm_ can determine whether an arbitrary program terminates on arbitrary input.
  This fundamental result establishes theoretical limits on program analysis.
  Perfect program verification is _undecidable_.
]

Formal verification faces several obstacles:

_Computational complexity._
Precise program analysis often requires exponential time or space.
For non-trivial programs, exact analysis becomes infeasible.

_State space explosion._
A program with $n$ variables, each holding one of $k$ values, has $k^n$ possible states.
Even 10 boolean variables yield 1024 states.
Real programs have thousands of variables.

_Undecidability._
Determining whether code is reachable, whether loops terminate, or whether assertions hold is undecidable in the general case.

To make verification tractable, we must approximate.

#figure(
  caption: [The verification landscape. Different approaches trade off precision, automation, and scalability. Abstract interpretation occupies the sweet spot: fully automatic, scalable to large codebases, with tunable precision through domain choice.],

  cetz.canvas({
    import cetz.draw: *

    // Helper functions
    let draw-approach(pos, label, precision, automation, scalability, color) = {
      circle(pos, radius: 0.4, fill: color.lighten(70%), stroke: color + 1.5pt)
      content(pos, [#text(size: 0.7em, fill: color)[#label]])
    }

    let draw-axis-label(pos, text-content) = {
      content(pos, [#text(size: 0.75em, fill: colors.text-light)[#text-content]])
    }

    // Axes
    line((0, 0), (8, 0), stroke: colors.text-light + 1pt, mark: (end: ">"))
    line((0, 0), (0, 6), stroke: colors.text-light + 1pt, mark: (end: ">"))
    draw-axis-label((8.5, 0), [Scalability])
    draw-axis-label((0, 6.5), [Precision])

    // Approaches positioned by their tradeoffs
    draw-approach((1.5, 5), [Theorem\nProving], "high", "low", "low", colors.secondary)
    draw-approach((2.5, 4.5), [SMT\nSolvers], "high", "medium", "medium", colors.secondary)
    draw-approach((4, 3.5), [Abstract\nInterpretation], "medium", "high", "high", colors.primary)
    draw-approach((6, 2), [Type\nSystems], "low", "high", "high", colors.accent)
    draw-approach((2, 1.5), [Symbolic\nExecution], "high", "medium", "low", colors.warning)
    draw-approach((7, 1), [Testing], "varies", "high", "high", colors.error)

    // Annotations
    content((4, 0.8), [#text(size: 0.65em, fill: colors.primary, style: "italic")[This guide's focus]], anchor: "north")
    line((4, 1.2), (4, 3), stroke: colors.primary + 1pt, mark: (end: ">"))
  }),
) <fig:verification-landscape>

== Abstract Interpretation

#historical-note(
  person: "Patrick Cousot and Radhia Cousot",
  year: "1977",
  title: "Abstract Interpretation Framework",
  image-path: none,
)[
  The Cousots developed the mathematical framework of abstract interpretation at the University of Grenoble.
  Their work provided a principled foundation for approximating program semantics while guaranteeing soundness.
  Abstract interpretation has become fundamental to modern program analysis.
]

Abstract interpretation is a mathematical framework for approximating program behavior.
Rather than tracking exact values, we track properties of values.

Instead of computing with concrete values ($x = 5$, $y = -3$, $z = 0$), we reason about abstract properties ($x > 0$, $y < 0$, $z = 0$).

Consider tracking whether variables are positive, negative, or zero:

```rust
x = 5           // x is positive
y = x + 10      // y is positive (positive + positive = positive)
z = x - x       // z is zero (positive - itself = zero)
w = x - y       // w is negative (positive - larger positive = negative)
```

We do not know exact values.
We know properties that hold for all possible executions.

The analysis guarantees: if it reports "x is positive," then x is positive in all executions.
The analysis may be imprecise: if it reports "x is unknown," x might still be positive --- we simply cannot determine this from our abstraction.

This approach trades precision for decidability and efficiency:
- Analysis always terminates
- Results are sound: proven properties hold in all executions
- Results may be approximate: we may fail to prove true properties

#example-box(number: "0.2", title: "Sign Domain")[
  Consider an abstract domain tracking sign information:

  _Concrete values:_ $x in {..., -2, -1, 0, 1, 2, ...}$ (infinite)

  _Abstract signs:_ $x in {"Neg", "Zero", "Pos", "Unknown"}$

  For operation `y = x + 1`:

  - If $x = "Pos"$, then $y = "Pos"$ (positive + 1 = positive)
  - If $x = "Zero"$, then $y = "Pos"$ (0 + 1 = positive)
  - If $x = "Neg"$, then $y in {"Neg", "Zero", "Pos"}$ (depends on x's value)

  For $x = -1$: $y = 0$ (Zero)

  For $x = -2$: $y = -1$ (Neg)

  For $x = -100$: $y = -99$ (Neg)

  Safe approximation for Neg input: $y = "Unknown"$ (over-approximates all possibilities)

  We reduce infinite concrete values to four abstract values while maintaining soundness.
]

== Path Sensitivity

Abstract interpretation analyzes program behavior across all execution paths.
Real programs contain control flow: conditionals, loops, and state-dependent behavior.

Consider an embedded controller:

```rust
enum Mode { OFF, STANDBY, ACTIVE }

let mut mode = Mode::OFF;
let mut power = 0;

if battery_ok && temperature < 25 {
    mode = Mode::ACTIVE;
    power = 100;
} else if battery_ok {
    mode = Mode::STANDBY;
    power = 20;
}

match mode {
    Mode::ACTIVE => assert!(power == 100),
    Mode::STANDBY => assert!(power == 20),
    Mode::OFF => assert!(power == 0),
}
```

A path-insensitive analysis merges information from all branches:
- After conditionals: `power ∈ {0, 20, 100}`
- The analysis cannot verify the assertions --- correlation between `mode` and `power` is lost

A path-sensitive analysis maintains separate invariants:
- When `mode = ACTIVE`: `power = 100`
- When `mode = STANDBY`: `power = 20`
- When `mode = OFF`: `power = 0`

All assertions verify successfully.

However, path-sensitive analysis faces the path explosion problem:
a program with $n$ independent boolean conditions has $2^n$ distinct paths.
Enumerating paths explicitly becomes infeasible.

For 30 boolean flags: 1,073,741,824 paths.

We require path sensitivity without path explosion.

== Binary Decision Diagrams

#historical-note(
  person: "Randal Bryant",
  year: "1986",
  title: "Graph-Based Algorithms for Boolean Function Manipulation",
  image-path: none,
)[
  Bryant introduced Reduced Ordered Binary Decision Diagrams (ROBDDs) at Carnegie Mellon University.
  His canonical representation enabled efficient manipulation of boolean functions.
  BDDs became fundamental to hardware verification and symbolic model checking.
]

Binary Decision Diagrams provide a canonical, compact representation of boolean functions.
A boolean function with $n$ variables requires $2^n$ truth table entries.
A BDD can represent the same function using $O(n)$ nodes for many practical cases.

BDDs achieve compression through structural sharing:
multiple paths through the diagram share common substructure.

#example-box(number: "0.3", title: "BDD Representation")[
  Consider function $f$ encoding valid system states:

  $ f(x_1, x_2, x_3) = (x_1 and x_2) or (not x_1 and x_3) $

  Truth table: 8 rows

  BDD representation: 4 decision nodes + 2 terminals

  The BDD shares structure: both branches leading to the same outcome merge into a single subgraph.
  This structural sharing provides exponential compression for many boolean functions.
]

For program analysis:

_Path conditions_ can be encoded as boolean formulas.
Each program path corresponds to a conjunction of conditions.
The set of all feasible paths is a boolean function.

BDDs represent this function compactly, enabling:
- Efficient path-sensitive analysis without explicit path enumeration
- Symbolic state space exploration
- Precise modeling of control-dependent properties

A BDD-based analysis maintains one compact representation instead of exponentially many explicit paths.

== Combining BDDs with Abstract Interpretation

BDDs enable symbolic representation of control states.
Abstract domains track properties of data values.
Combining these techniques yields path-sensitive analysis with controlled complexity.

The approach:
- Use BDDs to represent sets of _control configurations_ (which conditions hold)
- Use abstract domains to represent sets of _data values_ (intervals, signs, etc.)
- Maintain the _product_: for each control configuration, track corresponding data constraints

Instead of enumerating $2^n$ paths, we maintain a single BDD encoding all reachable control states, coupled with abstract values for each configuration.

#example-box(number: "0.4", title: "BDD-Based Path-Sensitive Analysis")[
  Returning to the mode controller:

  ```rust
  if battery_ok && temperature < 25 {
      mode = ACTIVE; power = 100;
  } else if battery_ok {
      mode = STANDBY; power = 20;
  }
  ```

  BDD representation encodes three feasible control paths:
  - $"battery"_"ok" and "temp" < 25 => ("mode" = "ACTIVE" and "power" = 100)$
  - $"battery"_"ok" and "temp" >= 25 => ("mode" = "STANDBY" and "power" = 20)$
  - $not "battery"_"ok" => ("mode" = "OFF" and "power" = 0)$

  Single BDD captures all paths compactly.
  Abstract domain tracks exact power values per configuration.
  All assertions verify successfully.
]

This combination provides:
- _Path sensitivity:_ maintains separate invariants per control path
- _Scalability:_ symbolic representation avoids exponential blowup
- _Soundness:_ mathematical guarantees from abstract interpretation framework
- _Automation:_ no manual proof effort required

== Guide Structure

This guide develops understanding from intuition to implementation.

*@part-i: Foundations*

@ch-abstraction introduces abstract interpretation through concrete examples.
@ch-control-flow examines why control flow complicates analysis.
@ch-bdds explains BDD structure and operations.
@ch-bdd-programming shows how to program with BDDs.
@ch-combining-domains combines BDDs with abstract domains.
@ch-symbolic-executor provides a complete symbolic execution example.

*@part-ii: Formal Development*

@ch-lattice-theory establishes lattice theory, fixpoint theorems, and Galois connections.
@ch-fixpoint-algorithms presents chaotic iteration and worklist algorithms.
@ch-advanced-galois develops advanced transformer theory and reduced products.
@ch-domain-combinations synthesizes BDD-based path-sensitive analysis techniques.

*@part-iii: Applications*

@ch-security applies techniques to information flow security.
@ch-interprocedural extends analysis to interprocedural contexts.
@ch-performance discusses implementation optimizations and benchmarks.
@ch-ai-guided explores AI-guided verification techniques.
@ch-case-studies presents real-world case studies.

== Prerequisites

@part-i assumes:
- Programming experience (Rust examples, but concepts are language-agnostic)
- Basic understanding of program semantics
- Familiarity with boolean logic

@part-ii additionally requires:
- Mathematical maturity (reading formal definitions and proofs)
- Understanding of partial orders and lattices
- Familiarity with fixpoint theory

== Learning Objectives

After completing this guide, you will:

+ Understand abstract interpretation's theoretical foundations
+ Recognize when path-sensitive analysis is necessary
+ Apply BDD-based techniques to verification problems
+ Implement abstract domains using the bdd-rs library
+ Evaluate precision-performance tradeoffs systematically
+ Read and understand program analysis research literature

== Beginning the Journey

Software failure has consequences:
rockets explode, patients die, systems are compromised.
Testing finds some bugs.
Formal verification can prove their absence.

Abstract interpretation provides a mathematical framework for sound, automatic program analysis.
BDDs enable efficient symbolic reasoning about control flow.
Together, they make path-sensitive verification practical.

The following chapters develop this synthesis rigorously.
