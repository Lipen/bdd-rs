// Chapter 1: The World of Abstract Interpretation

#import "../../theme.typ": *

= The World of Abstract Interpretation <ch:abstraction>

#reading-path(path: "essential") #h(0.5em) #reading-path(path: "beginner")

The Prologue established the need: testing is insufficient, perfect verification is impossible.
We require approximation that is both sound and tractable.
Abstract interpretation provides the mathematical foundation for this compromise.

This chapter introduces abstraction through concrete examples.
We explore how approximating values enables decidable analysis while preserving correctness guarantees.

== The Essence of Abstraction

Abstraction is the art of forgetting details while preserving essential structure.

Consider a road map.
A perfect 1:1 scale map would be useless—as complex as the territory itself.
A useful map _abstracts_: buildings become dots, roads become lines, elevations become contour lines.
The map loses information (you cannot see individual windows) but gains tractability (you can plan a route).

Similarly, abstract interpretation creates a "map" of program behaviors.
- The _concrete semantics_ describes all possible executions—infinite and uncomputable.
- The _abstract semantics_ provides a finite representation that safely over-approximates all executions.

The key property is _soundness_.
If the abstract analysis says "property P holds," then P truly holds in all concrete executions.
The analysis may report "don't know" (false positives) but never "safe" when the program is actually unsafe (no false negatives).

== Running Example: A Simple Counter

Consider this loop:

```rust
let mut x = 0;
while x < 10 {
    x = x + 1;
}
// What is x here?
```

To verify properties about this code, we need to track the value of `x` throughout execution.

=== Concrete Semantics

The _concrete execution_ produces a trace of states:

$
  x = 0 arrow.r x = 1 arrow.r x = 2 arrow.r ... arrow.r x = 10
$

After the loop, we know _exactly_: $x = 10$.

But computing concrete semantics requires executing the program.
For loops with unknown bounds, we cannot compute all possible values.
For programs with inputs, we have infinitely many traces.

=== Abstract Semantics

Instead of tracking exact values, we track _intervals_:

$
  x in [0, 0] arrow.r x in [1, 1] arrow.r x in [2, 2] arrow.r ... arrow.r x in [10, 10]
$

Each interval $[a, b]$ represents all integers from $a$ to $b$.

For this simple loop, abstract and concrete semantics coincide.
The abstraction is _precise_: we lose no information.

But consider a more complex example:

```rust
let mut x = 0;
let mut y = 0;
while x < 100 {
    if user_input() {
        x = x + 1;
    } else {
        y = y + 1;
    }
}
```

Concrete execution has $2^(100)$ possible traces depending on user input.
Abstract interpretation with intervals computes:

$
  x in [0, 100], quad y in [0, 100]
$

We lose precision (cannot determine the exact relationship between `x` and `y`), but analysis terminates and is sound.

== The Sign Domain

The _sign domain_ tracks whether variables are negative, zero, or positive.

=== Domain Elements

$
  "Sign" = {bot, "Neg", "Zero", "Pos", top}
$

The domain has five basic elements:
- $bot$ (_bottom_) represents an unreachable state or no information
- $top$ (_top_) represents unknown sign—the value could be anything.
- Between them lie the concrete signs:
  - $"Neg"$ for strictly negative values ($x < 0$)
  - $"Zero"$ for exactly zero
  - $"Pos"$ for strictly positive values ($x > 0$)

We can extend this with compound signs:

$
  "SignExt" = {bot, "Neg", "Zero", "Pos", "NonNeg", "NonPos", top}
$

The compound signs $"NonNeg"$ (non-negative, covering $"Zero" union "Pos"$) and $"NonPos"$ (non-positive, covering $"Zero" union "Neg"$) provide intermediate precision when we know a value's relationship to zero but not its exact sign.

=== The Lattice Structure

These signs form a _partial order_ where $a <= b$ means "$a$ is more precise than $b$":

#align(center)[
  #v(1em)
  _[Lattice diagram would go here]_
  #v(1em)
]

At the bottom: $bot$ (most precise—no values)
At the top: $top$ (least precise—all values)
In between: progressively less precise abstractions.

This ordering has special operations:

_Join_ ($union.sq$): Combines information, loses precision
$
  "Pos" union.sq "Neg" = top
$

_Meet_ ($inter.sq$): Refines information, gains precision
$
  "NonNeg" inter.sq "NonPos" = "Zero"
$

#info-box(title: "Why Lattices?")[
  Lattice structure ensures our analysis has nice mathematical properties:
  - Join gives us a way to merge information from different program paths
  - Meet lets us refine information when we learn new facts
  - Bottom and top give us meaningful boundary cases
  - The ordering guarantees our analysis can converge to a fixpoint
]

== Abstract Operations

To analyze programs, we need to abstract _operations_:

=== Arithmetic Operations

*Addition:*

$
  "Pos" + "Pos" & = "Pos" \
  "Neg" + "Neg" & = "Neg" \
  "Pos" + "Neg" & = top quad "(could be anything)"
$

*Multiplication:*

$
  "Pos" times "Pos" & = "Pos" \
  "Neg" times "Neg" & = "Pos" \
  "Pos" times "Neg" & = "Neg" \
     "Zero" times x & = "Zero"
$

*Subtraction:*

$
  x - y = x + (- y)
$

Where negation flips the sign:
$
   - "Pos" & = "Neg" \
   - "Neg" & = "Pos" \
  - "Zero" & = "Zero"
$

#example-box(number: "1.1", title: "Sign Analysis")[
  Analyze this code fragment:

  ```rust
  let mut a = 5;      // a: Pos
  let mut b = -3;     // b: Neg
  let mut c = 0;      // c: Zero

  let x = a + b;      // x: Top (Pos + Neg)
  let y = a * 2;      // y: Pos (Pos * Pos)
  let z = b - 1;      // z: Neg (Neg - Pos)
  let w = c + a;      // w: Pos (Zero + Pos)
  ```

  For `x = a + b`:
  - We know `a` is positive and `b` is negative
  - Their sum could be positive, negative, or zero
  - Safe approximation: $x = top$

  For `y = a * 2`:
  - Both operands are positive
  - Product is definitely positive
  - Precise result: $y = "Pos"$
]

=== Comparison Operations

Comparisons produce boolean values, but we can track them symbolically:

$
  "Pos" > 0 & arrow.r.double "true" \
  "Neg" > 0 & arrow.r.double "false" \
    top > 0 & arrow.r.double "unknown"
$

This enables _path refinement_:

```rust
let x: Top;  // Unknown sign
if x > 0 {
    // Here: x is Pos
} else {
    // Here: x is NonPos
}
```

The abstract interpreter can track different signs in different branches, maintaining precision.

== Concrete to Abstract: The Abstraction Function

Formally, we define an _abstraction function_ $alpha$ that maps concrete values to abstract values:

$
  alpha: ZZ arrow "Sign"
$

$
  alpha(x) = cases(
    bot & "if no value",
    "Neg" & "if" x < 0,
    "Zero" & "if" x = 0,
    "Pos" & "if" x > 0
  )
$

For sets of values, we take the join:

$
  alpha({-5, -2, 0, 3, 7}) = "Neg" union.sq "Zero" union.sq "Pos" = top
$

The _concretization function_ $gamma$ goes the opposite direction:

$
  gamma: "Sign" arrow cal(P)(ZZ)
$

$
   gamma("Pos") & = {x in ZZ : x > 0} \
  gamma("Zero") & = {0} \
     gamma(top) & = ZZ
$

These functions form a _Galois connection_, ensuring soundness:
- $alpha$ over-approximates: $x subset.eq gamma(alpha(x))$
- $gamma compose alpha$ is inflationary
- $alpha compose gamma$ is reductive

#warning-box(title: "Precision vs. Soundness")[
  Abstract interpretation makes a deliberate tradeoff:

  _Soundness_ is non-negotiable.
  If analysis says "safe," the program must be safe.

  _Precision_ is best-effort.
  The analysis may report "possibly unsafe" even when the program is actually safe.
  This is acceptable—better safe than sorry.

  We accept false positives (spurious warnings) to guarantee no false negatives (missed bugs).
]

== Analyzing Loops: Fixpoint Iteration

The real power of abstract interpretation emerges when analyzing loops.

Consider:

```rust
let mut x = 0;
while x < 10 {
    x = x + 1;
}
```

We cannot unroll the loop infinitely.
Instead, we compute a _fixpoint_: a state that remains unchanged under one more iteration.

=== Iterative Analysis

Start with initial state:

_Iteration 0:_ $x = "Zero"$

Apply loop body:

_Iteration 1:_ $x = "Zero" + "Pos" = "Pos"$

Apply again:

_Iteration 2:_ $x = "Pos" + "Pos" = "Pos"$

We reached a fixpoint!
$x = "Pos"$ is stable: one more iteration gives $"Pos"$ again.

After the loop, we know: $x in "Pos"$, which is sound (the actual value is 10, which is positive).

=== Widening for Non-Termination

Some loops don't stabilize quickly:

```rust
let mut x = 0;
while condition {
    x = x + 1;
}
```

Without knowing when `condition` becomes false, our iteration might not converge:

$
  x = "Zero" arrow.r "Pos" arrow.r "Pos" arrow.r ...
$

To ensure termination, we use _widening_ ($nabla$):

$
  x_0 nabla x_1 = cases(
    x_1 & "if" x_1 "is more precise",
    top & "otherwise"
  )
$

After a few iterations without convergence, we _widen_ to $top$, guaranteeing termination at the cost of precision.

#info-box(title: "Widening: The Termination Guarantee")[
  Widening is the key to making abstract interpretation decidable.

  By jumping to a less precise (but sound) over-approximation, we ensure the analysis terminates even for:
  - Unbounded loops
  - Recursive functions
  - Complex control flow

  The analysis may lose precision, but it always completes and remains sound.
]

== Why This Works: Soundness Theorem

The fundamental theorem of abstract interpretation:

#theorem(title: "Soundness")[
  If the abstract analysis computes abstract state $a$, then all concrete executions produce states in $gamma(a)$.

  Formally: if $sigma$ is a reachable concrete state, then $sigma in gamma(a)$.
]

This means:
- If analysis says "x is positive," then x is positive in all executions
- If analysis says "no division by zero," then there truly is no division by zero
- If analysis reports a bug, the bug _may_ exist (or it might be a false alarm)

The analysis is _conservative_: it may reject safe programs, but never accepts unsafe ones.

== Comparison with Other Approaches

=== vs. Testing

*Testing:* Checks specific inputs, may miss bugs, provides no guarantees.

*Abstract Interpretation:* Checks _all_ inputs (approximately), may report false alarms, _guarantees_ found properties.

=== vs. SMT Solvers

*SMT Solvers:* Precise, may not terminate, limited to bounded programs.

*Abstract Interpretation:* Approximate, always terminates, handles unbounded programs.

=== vs. Type Systems

*Type Systems:* Fast, modular, very coarse abstractions (e.g., "is an integer").

*Abstract Interpretation:* Slower, whole-program, finer abstractions (e.g., "is a positive integer less than 100").

Abstract interpretation generalizes type checking: types are just a very coarse abstract domain.

== Summary

Abstract interpretation enables automatic verification by:

1. Defining abstract domains (like signs, intervals, or sets)
2. Defining abstract operations (how to add signs, compare intervals, etc.)
3. Computing fixpoints (stable states under program iteration)
4. Using widening to ensure termination
5. Guaranteeing soundness through mathematical foundations

The sign domain is simple but illustrates all key concepts.
Real analyses use richer domains: intervals, octagons, polyhedra, or combinations of multiple domains.

In the next chapter, we examine why control flow complicates this picture and why path-sensitive analysis requires special techniques.

#chapter-summary(
  [
    *Abstraction trades precision for decidability.*
    Instead of tracking exact values, we track properties.
  ],
  [
    *Abstract domains form lattices.*
    Join (⊔) combines information, meet (⊓) finds common properties.
  ],
  [
    *Abstraction function $alpha$ and concretization function $gamma$ connect concrete and abstract.*
    The Galois connection ensures soundness.
  ],
  [
    *Fixpoint iteration analyzes loops.*
    We repeatedly apply abstract operations until reaching a fixed point.
  ],
  [
    *Widening ensures termination.*
    When iteration doesn't converge, widening forces stabilization.
  ],
  [
    *Soundness theorem guarantees correctness.*
    All real behaviors are included in abstract analysis results.
  ],
  [
    *Main Insight:*
    Abstract interpretation makes verification tractable by tracking properties instead of exact values, using lattice theory to ensure sound approximations.
  ],
)

#v(2em)

#align(right)[
  _Chapter 2: Understanding Control Flow $->$_
]
