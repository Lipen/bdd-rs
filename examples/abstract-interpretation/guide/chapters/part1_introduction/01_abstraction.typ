// Chapter 1: The World of Abstract Interpretation

#import "../../theme.typ": *

= The World of Abstract Interpretation <ch-abstraction>

#reading-path(path: "essential") #h(0.5em) #reading-path(path: "beginner")

The Prologue established the need: testing is insufficient, perfect verification is impossible.
We require approximation that is both sound and tractable.
Abstract interpretation provides the mathematical foundation for this compromise.

This chapter introduces abstraction through concrete examples.
We explore how approximating values enables decidable analysis while preserving correctness guarantees.

== The Essence of Abstraction

Abstraction is the art of forgetting details while preserving essential structure.

Consider a road map.
A perfect 1:1 scale map would be useless --- as complex as the territory itself.
A useful map _abstracts_: buildings become dots, roads become lines, elevations become contour lines.
The map loses information (you cannot see individual windows) but gains tractability (you can plan a route).

Similarly, abstract interpretation creates a "map" of program behaviors.
- The _concrete semantics_ describes all possible executions --- infinite and uncomputable.
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
  x = 0 -> x = 1 -> x = 2 -> ... -> x = 10
$

After the loop, we know _exactly_: $x = 10$.

But computing concrete semantics requires executing the program.
For loops with unknown bounds, we cannot compute all possible values.
For programs with inputs, we have infinitely many traces.

=== Abstract Semantics

Instead of tracking exact values, we track _intervals_:

$
  x in [0, 0] -> x in [1, 1] -> x in [2, 2] -> ... -> x in [10, 10]
$

Each interval $[a, b]$ represents all integers from $a$ to $b$.

For this simple loop, abstract and concrete semantics coincide.
The abstraction is _precise_: we lose no information.

#figure(
  caption: [Concrete execution tracks exact values (circles), while abstract execution tracks intervals (rectangles). For this simple loop, both maintain complete precision.],

  cetz.canvas({
    import cetz.draw: *

    // Helper functions
    let draw-concrete-state(pos, value) = {
      circle(pos, radius: 0.3, fill: colors.success, stroke: colors.success + 1.5pt)
      content(pos, text(fill: white, size: 0.9em, weight: "bold")[#value])
    }

    let draw-abstract-state(pos, interval) = {
      rect(
        (pos.at(0) - 0.4, pos.at(1) - 0.3),
        (pos.at(0) + 0.4, pos.at(1) + 0.3),
        fill: colors.bg-code,
        stroke: colors.secondary + 1.5pt,
        radius: 0.1,
      )
      content(pos, text(fill: colors.secondary, size: 0.7em)[#interval])
    }

    let draw-arrow(from-x, y, to-x, color) = {
      line((from-x, y), (to-x, y), stroke: color + 1pt, mark: (end: ">"))
    }

    let draw-label(pos, body, anchor-side: "west") = {
      content(pos, text(fill: colors.text-light, size: 0.8em)[#body], anchor: anchor-side)
    }

    // Layout
    let concrete-y = 2.5
    let abstract-y = 0

    // Concrete execution trace
    content(
      (0, concrete-y + 0.8),
      text(fill: colors.primary, weight: "bold", size: 0.9em)[Concrete Execution],
      anchor: "west",
    )

    for i in range(0, 5) {
      let x = i * 1.5
      draw-concrete-state((x, concrete-y), i)
      if i < 4 {
        draw-arrow(x + 0.3, concrete-y, x + 1.2, colors.success)
      }
    }
    draw-label((6.5, concrete-y), [...])
    draw-concrete-state((8, concrete-y), 10)
    draw-label((9, concrete-y), [_precise_])

    // Abstract execution trace
    content(
      (0, abstract-y + 0.8),
      text(fill: colors.secondary, weight: "bold", size: 0.9em)[Abstract Execution],
      anchor: "west",
    )

    draw-abstract-state((0, abstract-y), $\[0,0\]$)
    draw-arrow(0.5, abstract-y, 1, colors.secondary)
    draw-abstract-state((1.5, abstract-y), $\[1,1\]$)
    draw-arrow(2, abstract-y, 2.5, colors.secondary)
    draw-label((3.5, abstract-y), [...])
    draw-arrow(4.5, abstract-y, 5, colors.secondary)
    draw-abstract-state((5.5, abstract-y), $\[10,10\]$)
    draw-label((7, abstract-y), [_still precise_])
  }),
) <fig:concrete-vs-abstract>

#v(0.5em)

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
- $top$ (_top_) represents unknown sign --- the value could be anything.
- Between them lie the concrete signs:
  - $"Neg"$ for strictly negative values ($x < 0$)
  - $"Zero"$ for exactly zero
  - $"Pos"$ for strictly positive values ($x > 0$)

We can extend this with compound signs:

$
  "SignExt" = {bot, "Neg", "Zero", "Pos", "NonNeg", "NonPos", top}
$

The compound signs $"NonNeg"$ (non-negative, covering $"Zero" union "Pos"$) and $"NonPos"$ (non-positive, covering $"Zero" union "Neg"$) provide intermediate precision when we know a value's relationship to zero but not its exact sign.

#figure(
  caption: [Extended sign domain lattice with compound elements. $"NonNeg" = "Zero" ljoin "Pos"$ and #box[$"NonPos" = "Zero" ljoin "Neg"$] provide intermediate precision levels.],

  cetz.canvas({
    import cetz.draw: *

    // Helper functions
    let draw-node(pos, label, color, radius: 0.4) = {
      circle(pos, radius: radius, fill: white, stroke: color)
      content(pos, label)
    }

    let draw-terminal(pos, label) = {
      circle(pos, radius: 0.4, fill: colors.bg-code, stroke: colors.primary)
      content(pos, label)
    }

    let draw-edge(from, to, dashed: false) = {
      let stroke-style = if dashed {
        (paint: colors.text-light, thickness: 0.5pt, dash: "dashed")
      } else {
        colors.text-light
      }
      line(from, to, stroke: stroke-style)
    }

    // Positions
    let top-pos = (0, 4.5)
    let upp-nonneg = (1.8, 3)
    let upp-nonpos = (-1.8, 3)
    let mid-neg = (-2.5, 1.5)
    let mid-zero = (0, 1.5)
    let mid-pos = (2.5, 1.5)
    let bot-pos = (0, 0)

    // Draw edges
    draw-edge(bot-pos, mid-neg)
    draw-edge(bot-pos, mid-zero)
    draw-edge(bot-pos, mid-pos)
    draw-edge(mid-neg, upp-nonpos)
    draw-edge(mid-zero, upp-nonpos)
    draw-edge(mid-zero, upp-nonneg)
    draw-edge(mid-pos, upp-nonneg)
    // draw-edge(mid-neg, top-pos, dashed: true)
    // draw-edge(mid-pos, top-pos, dashed: true)
    draw-edge(upp-nonpos, top-pos)
    draw-edge(upp-nonneg, top-pos)

    // Draw nodes
    draw-terminal(top-pos, text(fill: colors.primary)[$top$])
    draw-node(upp-nonneg, text(fill: colors.accent, size: 0.75em)[NonNeg], colors.accent, radius: 0.6)
    draw-node(upp-nonpos, text(fill: colors.accent, size: 0.75em)[NonPos], colors.accent, radius: 0.6)
    draw-node(mid-neg, text(fill: colors.secondary, size: 0.85em)[Neg], colors.secondary)
    draw-node(mid-zero, text(fill: colors.secondary, size: 0.85em)[Zero], colors.secondary)
    draw-node(mid-pos, text(fill: colors.secondary, size: 0.85em)[Pos], colors.secondary)
    draw-terminal(bot-pos, text(fill: colors.primary)[$bot$])
  }),
) <fig:sign-extended-lattice>
#v(0.5em)

=== The Lattice Structure

These signs form a _partial order_ where $a <= b$ means "$a$ is more precise than $b$":
- At the bottom: $bot$ (most precise --- no values)
- At the top: $top$ (least precise --- all values)
- In between: progressively less precise abstractions.

#figure(
  caption: [Sign domain lattice. Elements higher in the lattice are less precise but represent more values. The ordering $a <= b$ means "$a$ is more precise than $b$".],

  cetz.canvas({
    import cetz.draw: *

    // Helper functions for consistent styling
    let draw-lattice-node(pos, label, is-terminal: false) = {
      let node-color = if is-terminal { colors.primary } else { colors.secondary }
      let bg-fill = if is-terminal { colors.bg-code } else { white }
      circle(pos, radius: 0.4, fill: bg-fill, stroke: node-color)
      content(pos, label)
    }

    let draw-lattice-edge(from, to) = {
      line(from, to, stroke: colors.text-light)
    }

    // Positions
    let top-pos = (0, 3)
    let mid-neg = (-1.5, 1.5)
    let mid-zero = (0, 1.5)
    let mid-pos = (1.5, 1.5)
    let bot-pos = (0, 0)

    // Draw edges first (so they're behind nodes)
    draw-lattice-edge(bot-pos, mid-neg)
    draw-lattice-edge(bot-pos, mid-zero)
    draw-lattice-edge(bot-pos, mid-pos)
    draw-lattice-edge(mid-neg, top-pos)
    draw-lattice-edge(mid-zero, top-pos)
    draw-lattice-edge(mid-pos, top-pos)

    // Draw nodes
    draw-lattice-node(top-pos, text(fill: colors.primary, font: "Libertinus Math")[$top$], is-terminal: true)
    draw-lattice-node(mid-neg, text(fill: colors.secondary, size: 0.85em)[Neg])
    draw-lattice-node(mid-zero, text(fill: colors.secondary, size: 0.85em)[Zero])
    draw-lattice-node(mid-pos, text(fill: colors.secondary, size: 0.85em)[Pos])
    draw-lattice-node(bot-pos, text(fill: colors.primary, font: "Libertinus Math")[$bot$], is-terminal: true)

    // Add labels for precision
    content((3, 3), text(fill: colors.text-light, size: 0.8em)[_least precise_], anchor: "west")
    content((3, 0), text(fill: colors.text-light, size: 0.8em)[_most precise_], anchor: "west")
  }),
) <fig:sign-lattice>
#v(0.5em)

This ordering has special operations:

- _Join_ ($ljoin$): Combines information, loses precision
  $
    "Pos" ljoin "Neg" = top
  $

- _Meet_ ($lmeet$): Refines information, gains precision
  $
    "NonNeg" lmeet "NonPos" = "Zero"
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
  "Pos" > 0 & => "true" \
  "Neg" > 0 & => "false" \
    top > 0 & => "unknown"
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
  alpha({-5, -2, 0, 3, 7}) = "Neg" ljoin "Zero" ljoin "Pos" = top
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

  - _Soundness_ is non-negotiable.
    If analysis says "safe," the program must be safe.

  - _Precision_ is best-effort.
    The analysis may report "possibly unsafe" even when the program is actually safe.
    This is acceptable --- better safe than sorry.

  We accept _false positives_ (spurious warnings) to guarantee _no false negatives_ (missed bugs).
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

#figure(
  caption: [Fixpoint iteration for loop analysis. After iteration 1, the abstract state stabilizes at Pos and no longer changes.],

  cetz.canvas({
    import cetz.draw: *

    // Helper function for iteration state
    let draw-iteration(y, label, value, color, is-fixpoint: false) = {
      content((-1.5, y), text(fill: colors.text, size: 0.85em, weight: "bold")[#label], anchor: "east")
      rect(
        (0, y - 0.35),
        (2, y + 0.35),
        fill: if is-fixpoint { color.lighten(80%) } else { white },
        stroke: color + 1.5pt,
        radius: 0.1,
        name: label.replace(" ", "-"),
      )
      content((1, y), text(fill: color, size: 0.85em, weight: "bold")[$x =$ #value])
    }

    let iterations = (
      (label: "Iteration 0", value: "Zero", color: colors.warning),
      (label: "Iteration 1", value: "Pos", color: colors.accent),
      (label: "Iteration 2", value: "Pos", color: colors.success),
      (label: "Iteration 3", value: "Pos", color: colors.success),
    )

    for (i, iter) in iterations.enumerate() {
      let y = 3 - i * 1.2
      draw-iteration(y, iter.label, iter.value, iter.color, is-fixpoint: i == iterations.len() - 1)

      // Arrow between iterations
      if i > 0 {
        line(
          "Iteration-" + str(i - 1),
          "Iteration-" + str(i),
          stroke: colors.text-light + 1pt,
          mark: (end: ">", fill: colors.text-light),
        )
      }
    }

    // Fixpoint annotation
    content(
      (rel: (.5, 0), to: "Iteration-2.east"),
      align(top)[
        #text(fill: colors.success, size: 0.8em, style: "italic")[$<-$ Fixpoint reached!] \
        #text(fill: colors.text-light, size: 0.8em)[No further changes]
      ],
      anchor: "west",
    )
  }),
) <fig:fixpoint-iteration>
#v(0.5em)

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
  x = "Zero" -> "Pos" -> "Pos" -> ...
$

To ensure termination, we use _widening_ ($widen$):

$
  x_0 widen x_1 = cases(
    x_1 & "if" x_1 "is more precise",
    top & "otherwise"
  )
$

After a few iterations without convergence, we _widen_ to $top$, guaranteeing termination at the cost of precision.

#figure(
  caption: [Widening operator ($widen$) forces convergence. Without widening, iteration may continue indefinitely. With widening, the analysis jumps to ⊤ after detecting non-convergence.],

  cetz.canvas({
    import cetz.draw: *

    // Helper functions
    let draw-state-box(pos, name, label, color, highlight: false) = {
      let bg = if highlight { color.lighten(85%) }
      rect(
        (pos.at(0) - 0.4, pos.at(1) - 0.3),
        (pos.at(0) + 0.4, pos.at(1) + 0.3),
        fill: bg,
        stroke: color + 1.5pt,
        radius: 0.1,
        name: name,
      )
      content(pos, text(fill: color, size: 0.8em)[#label])
    }

    let draw-transition-arrow(from-pos, to-pos, color, label: none) = {
      line(from-pos, to-pos, stroke: color + 1pt, mark: (end: ">", fill: color))
      if label != none {
        content((from-pos, 40%, to-pos), text(fill: color, size: 0.7em)[#label], anchor: "south", padding: 0.2)
      }
    }

    // Layout
    let without-y = 2
    let with-y = 0
    let step-x = 1.8

    // Without widening scenario
    content(
      (-1.5, without-y + 0.8),
      text(fill: colors.error, weight: "bold", size: 0.9em)[Without Widening:],
      anchor: "east",
    )

    let states-nowiden = ("Zero", "Pos", "Pos", "Pos", "...")
    for (i, state) in states-nowiden.enumerate() {
      let x = i * step-x
      if state != "..." {
        draw-state-box((x, without-y), "state-nowiden-" + str(i), state, colors.error)
        if i < states-nowiden.len() - 1 {
          draw-transition-arrow((x + 0.5, without-y), (x + step-x - 0.5, without-y), colors.error)
        }
      } else {
        content((x, without-y), text(fill: colors.error, weight: "bold")[#state])
      }
    }
    content(
      (8, without-y),
      text(fill: colors.error, size: 0.8em, style: "italic")[may not converge!],
      anchor: "west",
    )

    // With widening scenario
    content(
      (-1.5, with-y + 0.8),
      text(fill: colors.success, weight: "bold", size: 0.9em)[With Widening:],
      anchor: "east",
    )

    let states-widen = (
      (val: "Zero", color: colors.text, highlight: false),
      (val: "Pos", color: colors.text, highlight: false),
      (val: [#sym.top], color: colors.success, highlight: true),
    )

    for (i, state) in states-widen.enumerate() {
      let x = i * step-x
      draw-state-box((x, with-y), "state-widen-" + str(i), state.val, state.color, highlight: state.highlight)

      if i < states-widen.len() - 1 {
        draw-transition-arrow((x + 0.5, with-y), (x + step-x - 0.5, with-y), state.color, label: if i == 1 {
          $widen$
        } else { none })
      }
    }

    content((5, with-y), text(fill: colors.success, size: 0.8em, style: "italic")[converged!], anchor: "west")
  }),
) <fig:widening>
#v(0.5em)

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
    *Main insight:*
    Abstract interpretation makes verification tractable by tracking properties instead of exact values, using lattice theory to ensure sound approximations.
  ],
)

#v(2em)

#align(right)[
  _@ch-control-flow $->$_
]
