#import "../../theme.typ": *

= The Theory of Approximation <ch-approximation>

#reading-path(path: "advanced")

In @ch-fixpoint-algorithms, we saw that Kleene iteration computes the least fixpoint of a monotone function.
However, this guarantee comes with a catch: it only terminates if the lattice has finite height or if the function has specific properties.
For many useful domains (like Intervals or Polyhedra), the lattice has infinite height.
A naive iteration `x := x join f(x)` might climb the lattice forever without reaching a fixpoint.

To solve this, we introduce *Widening* and *Narrowing*.
These operators allow us to trade precision for termination, ensuring we can analyze even infinite-state systems in finite time.

== Widening Operators

A *widening operator* $widen$ (nabla) is a binary operator $A times A -> A$ that accelerates convergence.
It acts like a "join" but with an extra property: it guesses a stable upper bound.

#definition(title: "Widening Operator")[
  An operator $widen: A times A -> A$ is a widening if:

  + *Upper Bound*: For all $x, y in A$, $x ljoin y lle x widen y$.
  + *Termination*: For any ascending chain $x_0 lle x_1 lle ...$, the sequence defined by $y_0 = x_0$ and $y_(n+1) = y_n widen x_(n+1)$ stabilizes in finite time.
]

The termination property is the magic.
Even if the underlying sequence $x_n$ grows forever, the widened sequence $y_n$ will hit a stable value (a post-fixpoint) in a finite number of steps.

=== Visualizing Widening

Consider the Interval domain.
The chain $[0, 1], [0, 2], [0, 3], ...$ never stabilizes.
A widening operator might observe the growth and jump to infinity.

#figure(
  caption: [Widening accelerates convergence by jumping over the limit],
  cetz.canvas({
    import cetz.draw: *

    // Draw axes
    line((0, 0), (6, 0), mark: (end: ">"), name: "x", stroke: colors.text-light + 1pt)
    line((0, 0), (0, 4), mark: (end: ">"), name: "y", stroke: colors.text-light + 1pt)
    content("x.end", anchor: "west", padding: 0.2)[Iterations]
    content("y.end", anchor: "south", padding: 0.2)[Value]

    // Draw the "staircase" (concrete iteration)
    set-style(stroke: (paint: colors.secondary, dash: "dashed"))
    line((0, 0), (1, 1), (2, 1.5), (3, 1.75), (4, 1.875), (5, 1.9))
    content((5, 1.9), anchor: "north", padding: 0.2, text(fill: colors.secondary)[Exact Sequence])

    // Draw the "widening" (jump)
    set-style(stroke: (paint: colors.primary, thickness: 2pt, dash: "solid"))
    line((0, 0), (1, 1), (2, 3))
    line((2, 3), (5, 3))
    content((5, 3), anchor: "south", padding: 0.2, text(fill: colors.primary)[Widened Sequence])

    // Limit line
    set-style(stroke: (paint: colors.text-light, dash: "dotted"))
    line((0, 2), (6, 2))
    content((6, 2), anchor: "west", padding: 0.2)[Least Fixpoint]

    // Post-fixpoint line
    line((0, 3), (6, 3))
    content((6, 3), anchor: "west", padding: 0.2)[Post-Fixpoint]
  })
)

In the diagram above, the exact sequence approaches the Least Fixpoint (LFP) asymptotically but never reaches it.
The widened sequence jumps *above* the LFP to a "Post-Fixpoint".
This result is sound (it over-approximates the true behavior) but less precise.

== Narrowing Operators

Widening often overshoots.
It might jump to $+infinity$ when the true bound is $100$.
Once we have a safe post-fixpoint $x^hash$ (where $f(x^hash) lle x^hash$), we can try to refine it.
We can't just iterate $f(x^hash)$ because we might re-enter an infinite descending chain.
We need a *narrowing operator* $narrow$ (Delta).

#definition(title: "Narrowing Operator")[
  An operator $narrow: A times A -> A$ is a narrowing if:

  + *Refinement*: For all $y lle x$, $y lle x narrow y lle x$.
  + *Termination*: For any sequence $y_0 = x^hash$, $y_(n+1) = y_n narrow f(y_n)$, the sequence stabilizes in finite time.
]

Narrowing allows us to step down from the coarse post-fixpoint towards the least fixpoint, stopping safely before we run out of time.

== The Analysis Loop Pattern

The standard recipe for analyzing loops with infinite domains is:

+ *Upward Iteration (Widening)*:
  Compute $x_0 = bot$, $x_(i+1) = x_i widen f(x_i)$.
  Repeat until convergence $x_n = x_(n+1)$.
  Let $x^hash = x_n$.
  *Result:* $x^hash$ is a sound over-approximation.

+ *Downward Iteration (Narrowing)*:
  Compute $y_0 = x^hash$, $y_(i+1) = y_i narrow f(y_i)$.
  Repeat for a fixed number of steps or until convergence.
  *Result:* $y_k$ is a more precise sound over-approximation.

#example-box(title: "Real-World Example: Loop Analysis")[
  Consider a loop incrementing a counter:
  `i = 80; while i < 100 { process(i); i++ }`

  *Widening Phase:*
  - Iter 0: $[80, 80]$
  - Iter 1: $[80, 80] widen ([80, 80] ljoin [81, 81]) = [80, 80] widen [80, 81]$
    - Standard widening jumps to $+infinity$ if bound is unstable.
    - Result: $[80, +infinity]$
  - Iter 2: Check stability. $f([80, +infinity]) = [80, 100]$.
    - $[80, +infinity]$ is a post-fixpoint (since $[80, 100] subset.eq [80, +infinity]$).

  *Narrowing Phase:*
  - Start: $[80, +infinity]$
  - Apply $f$: $f([80, +infinity]) = [80, 100]$ (effect of loop guard `i < 100`).
  - Narrow: $[80, +infinity] narrow [80, 100] = [80, 100]$.
  - Result: $[80, 100]$. Perfect precision!
]

== Designing Widening Operators

Good widening operators are domain-specific.

- *Intervals:* If a bound changes, set it to $+infinity$ (or $-infinity$).
- *Thresholds:* Instead of jumping to infinity, jump to the next value in a fixed set $T = {0, 1, 2, 4, 8, ...}$.
- *Delayed Widening:* Perform $N$ normal joins before applying widening.
  This handles short loops precisely without over-approximation.

#warning-box(title: "Widening and BDDs")[
  BDD domains usually have finite height (for a fixed number of variables), so strictly speaking, they don't *need* widening to terminate.
  However, the lattice height is $2^N$, which is practically infinite.
  We apply "structural widening" to BDDs (e.g., limiting node count or merging paths) to ensure *efficient* termination, as discussed in @ch-bdd-path.
]
