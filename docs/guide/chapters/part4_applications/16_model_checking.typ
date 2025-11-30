#import "../../theme.typ": *

= Model Checking with BDDs <ch-model-checking>

In 1987, Ken McMillan demonstrated that BDDs could verify systems with $10^(20)$ states --- far beyond what explicit enumeration could ever hope to reach.
This breakthrough, called *symbolic model checking*, revolutionized hardware verification and remains one of BDDs' most celebrated applications.

This chapter shows how BDDs transform the impossible into routine.

== The State Explosion Problem

Consider a simple system: 100 flip-flops.
How many possible states? $2^(100) approx 10^(30)$.
At a billion states per second, explicit enumeration would take $10^(13)$ *years* --- longer than the age of the universe.

#figure(
  cetz.canvas(length: 1cm, {
    import cetz.draw: *

    content((6, 6.5), text(weight: "bold", size: 1em)[State Space Explosion])

    // Axes
    line((1, 1), (11, 1), stroke: 1pt + colors.line, mark: (end: ">"))
    content((11.3, 1), text(size: 0.7em)[bits])
    line((1, 1), (1, 6), stroke: 1pt + colors.line, mark: (end: ">"))
    content((1, 6.3), text(size: 0.7em)[states])

    // Exponential growth curve
    let exp-points = ()
    for x in range(0, 10) {
      let y = calc.min(calc.pow(1.5, x) * 0.15 + 1, 5.5)
      exp-points.push((x + 1.5, y))
    }
    line(..exp-points, stroke: 2pt + colors.error)

    // Annotations
    content((3, 1.8), text(size: 0.7em, fill: colors.text-muted)[10 bits])
    content((3, 0.5), text(size: 0.7em, fill: colors.text-muted)[$10^3$])
    content((6, 3.2), text(size: 0.7em, fill: colors.text-muted)[32 bits])
    content((6, 0.5), text(size: 0.7em, fill: colors.text-muted)[$10^9$])
    content((9.5, 5.2), text(size: 0.7em, fill: colors.error)[100 bits])
    content((9.5, 0.5), text(size: 0.7em, fill: colors.error)[$10^(30)$])

    // Feasibility line
    line((1, 2.5), (5, 2.5), stroke: (dash: "dashed", paint: colors.success, thickness: 1.5pt))
    content((3, 2.9), text(size: 0.7em, fill: colors.success)[Explicit: feasible])
    content((8, 4.5), text(size: 0.7em, fill: colors.error)[Explicit: impossible])
  }),
  caption: [State spaces grow exponentially with the number of state bits.],
)

Yet real hardware has thousands of flip-flops.
The key insight: *we don't need to enumerate states individually*.

#insight-box[
  BDDs represent *sets of states* as Boolean functions.
  A BDD with 1000 nodes can represent $10^(20)$ states.
  Operations on BDDs manipulate entire sets at once.
]

== Encoding States and Transitions

The key insight of symbolic model checking is representing state *sets* as Boolean functions rather than enumerating individual states.

A finite-state system consists of:
- *State variables* $bold(x) = (x_1, ..., x_n)$: Boolean variables encoding the current state
- *Next-state variables* $bold(x)' = (x'_1, ..., x'_n)$: Primed copies for the next state
- *Transition relation* $T(bold(x), bold(x)')$: A Boolean function capturing *all* legal transitions
- *Initial states* $I(bold(x))$: Boolean function true exactly on starting states
- *Property* $P(bold(x))$: Boolean function characterizing "good" or "bad" states

#example-box(title: "Two-Bit Counter")[
  A counter with state bits $x_0, x_1$ counts $0 -> 1 -> 2 -> 3 -> 0 -> ...$

  Transition relation:
  $ T(x_0, x_1, x'_0, x'_1) = (x'_0 <-> not x_0) and (x'_1 <-> (x_1 xor x_0)) $

  Initial state (start at 0):
  $ I(x_0, x_1) = not x_0 and not x_1 $
]

#figure(
  cetz.canvas(length: 1cm, {
    import cetz.draw: *

    content((6, 6.5), text(weight: "bold", size: 1em)[State Transition Diagram vs. BDD])

    // Explicit diagram
    content((2.5, 5.5), text(size: 0.9em, weight: "semibold")[Explicit: 4 states])

    circle((1.5, 3.5), radius: 0.5, fill: colors.box-definition.lighten(40%), stroke: 1pt + colors.primary)
    content((1.5, 3.5), text(size: 0.8em)[00])

    circle((3.5, 3.5), radius: 0.5, fill: colors.box-definition.lighten(40%), stroke: 1pt + colors.primary)
    content((3.5, 3.5), text(size: 0.8em)[01])

    circle((3.5, 1.5), radius: 0.5, fill: colors.box-definition.lighten(40%), stroke: 1pt + colors.primary)
    content((3.5, 1.5), text(size: 0.8em)[10])

    circle((1.5, 1.5), radius: 0.5, fill: colors.box-definition.lighten(40%), stroke: 1pt + colors.primary)
    content((1.5, 1.5), text(size: 0.8em)[11])

    // Arrows (clockwise)
    line((2, 3.5), (3, 3.5), stroke: 1pt + colors.line, mark: (end: ">"))
    line((3.5, 3), (3.5, 2), stroke: 1pt + colors.line, mark: (end: ">"))
    line((3, 1.5), (2, 1.5), stroke: 1pt + colors.line, mark: (end: ">"))
    line((1.5, 2), (1.5, 3), stroke: 1pt + colors.line, mark: (end: ">"))

    // Symbolic representation
    content((9, 5.5), text(size: 0.9em, weight: "semibold")[Symbolic: BDD for $T$])

    bdd-decision-node((8, 4), [$x_0$], name: "t-x0")
    bdd-decision-node((7, 2.5), [$x'_0$], name: "t-x0p-l")
    bdd-decision-node((9, 2.5), [$x'_0$], name: "t-x0p-r")

    // Simplified - just showing structure
    bdd-terminal-node((6.5, 1.2), "0", name: "t-0")
    bdd-terminal-node((10, 1.2), "...", name: "t-rest")

    line((7.7, 3.6), (7.2, 2.9), stroke: (dash: "dashed", paint: colors.line, thickness: 1pt))
    line((8.3, 3.6), (8.8, 2.9), stroke: 1pt + colors.line)

    // Key insight
    content((6, 0), align(center)[
      #set text(size: 0.8em)
      BDD encodes *all* transitions in *one* compact structure
    ])
  }),
  caption: [Explicit representation lists states; symbolic representation encodes the transition function.],
)

== Reachability Analysis

The fundamental question: *can the system ever reach a bad state?*

If we can compute the set of all reachable states, verification becomes trivial: check whether any bad state is reachable.
The challenge is computing this set without enumerating states individually.

=== Forward Reachability

Starting from initial states, repeatedly compute successors until reaching a *fixpoint* --- a point where no new states appear:

#algorithm(title: "Symbolic Reachability (Forward)")[
  ```
  Reachable(Init, Trans):
    Reached = Init
    repeat:
      Reached_old = Reached
      Reached = Reached ∪ Image(Reached, Trans)
    until Reached == Reached_old
    return Reached
  ```
]

The *Image* operation computes successor states:
$ "Image"(S, T) = exists bold(x). T(bold(x), bold(x)') and S(bold(x)) $

#figure(
  cetz.canvas(length: 1cm, {
    import cetz.draw: *

    content((5.5, 6), text(weight: "bold", size: 1em)[Symbolic Reachability])

    // Step 0: Initial
    rect((0.5, 3.5), (2, 5), fill: colors.box-definition.lighten(40%), stroke: 1pt + colors.primary, radius: 4pt)
    content((1.25, 4.5), text(size: 0.8em)[$R_0$])
    content((1.25, 4), text(size: 0.7em, fill: colors.text-muted)[Init])

    // Arrow
    line((2.1, 4.25), (2.6, 4.25), stroke: 1pt + colors.text-muted, mark: (end: ">"))

    // Step 1
    rect(
      (2.7, 3),
      (4.5, 5.3),
      fill: colors.box-example.lighten(40%),
      stroke: 1pt + colors.success.lighten(20%),
      radius: 4pt,
    )
    content((3.6, 4.8), text(size: 0.8em)[$R_1$])
    content((3.6, 4.3), text(size: 0.7em, fill: colors.text-muted)[+1 step])
    rect(
      (2.9, 3.2),
      (3.4, 3.6),
      fill: colors.box-definition.lighten(40%),
      stroke: 0.5pt + colors.primary.lighten(40%),
      radius: 2pt,
    )

    // Arrow
    line((4.6, 4.15), (5.1, 4.15), stroke: 1pt + colors.text-muted, mark: (end: ">"))

    // Step 2
    rect(
      (5.2, 2.7),
      (7.3, 5.5),
      fill: colors.box-warning.lighten(40%),
      stroke: 1pt + colors.warning.lighten(20%),
      radius: 4pt,
    )
    content((6.25, 5), text(size: 0.8em)[$R_2$])
    content((6.25, 4.5), text(size: 0.7em, fill: colors.text-muted)[+2 steps])
    rect(
      (5.4, 2.9),
      (6.3, 3.6),
      fill: colors.box-example.lighten(40%),
      stroke: 0.5pt + colors.success.lighten(40%),
      radius: 2pt,
    )

    // Arrow
    line((7.4, 4.1), (7.9, 4.1), stroke: 1pt + colors.text-muted, mark: (end: ">"))

    // Fixpoint
    rect((8, 2.7), (10.2, 5.5), fill: colors.box-insight.lighten(30%), stroke: 2pt + colors.info, radius: 4pt)
    content((9.1, 5), text(size: 0.8em, weight: "semibold")[$R^*$])
    content((9.1, 4.5), text(size: 0.7em, fill: colors.text-muted)[Fixpoint])
    rect(
      (8.2, 2.9),
      (9.2, 3.6),
      fill: colors.box-warning.lighten(40%),
      stroke: 0.5pt + colors.warning.lighten(40%),
      radius: 2pt,
    )

    // Key insight at bottom
    content((5.5, 1.7), text(size: 0.8em)[Each $R_i$ is a *single BDD* representing $10^(20)$ states])
  }),
  caption: [Reachability iterates until the set of reached states stabilizes.],
)

=== Why This Works

The magic: each iteration manipulates *BDDs*, not individual states.
Consider the scale difference:
- $S$ might represent $10^(15)$ states --- more than atoms in a human body
- The BDD for $S$ might have only 5000 nodes
- Image computation operates on these 5000 nodes, taking milliseconds
- Result: a BDD for the next frontier, perhaps 6000 nodes representing $10^(16)$ states

#insight-box[
  BDD size depends on the *structure* of the function, not the number of satisfying assignments.
  Regular, structured systems often have compact BDD representations even with huge state spaces.
]

== CTL Model Checking

*CTL* (Computation Tree Logic) expresses temporal properties:
- $"EF" P$: "Eventually $P$ might hold" (exists a path where $P$ eventually true)
- $"AG" P$: "Always globally $P$" (on all paths, $P$ always true)
- $"EG" P$: "Exists a path where $P$ is always true"
- $"AF" P$: "On all paths, $P$ eventually holds"

#definition(title: "CTL Semantics via Fixpoints")[
  CTL operators can be computed as fixpoints:
  - $"EF" P = mu Z. (P or "EX" Z)$ --- least fixpoint
  - $"EG" P = nu Z. (P and "EX" Z)$ --- greatest fixpoint
  - $"AF" P = mu Z. (P or "AX" Z)$
  - $"AG" P = nu Z. (P and "AX" Z)$

  Where $"EX" S = "PreImage"(S)$ and $"AX" S = not "EX"(not S)$.
]

#algorithm(title: "Computing EF (Backward Reachability)")[
  ```
  EF(P, Trans):
    Z = False        // Start with empty set
    repeat:
      Z_old = Z
      Z = P ∨ PreImage(Z, Trans)
    until Z == Z_old
    return Z         // States that can reach P
  ```
]

== Image and PreImage Computation

These are the workhorses of symbolic model checking:

#comparison-table(
  [*Operation*],
  [*Computes*],
  [*Formula*],
  [Image],
  [Successors of $S$],
  [$exists bold(x). T(bold(x), bold(x)') and S(bold(x))$],
  [PreImage],
  [Predecessors of $S$],
  [$exists bold(x)'. T(bold(x), bold(x)') and S(bold(x)')$],
)

Implementation uses *relational product* (And-Exists) for efficiency:

```rust
fn image(&self, states: Ref, trans: Ref) -> Ref {
    // Conjoin states with transition relation
    let conjoined = self.and(states, trans);
    // Quantify out current-state variables
    let next = self.exists_cube(conjoined, current_vars);
    // Rename x' back to x
    self.rename(next, next_to_current)
}
```

#warning-box(title: "The Image Bottleneck")[
  Image computation is often the bottleneck in model checking.
  Optimizations include:
  - *Partitioned transition relations*: Split $T$ into smaller pieces
  - *Early quantification*: Quantify variables as soon as possible
  - *Transition clustering*: Group related transitions
]

== Practical Example: Mutual Exclusion

Consider verifying Peterson's mutual exclusion algorithm with two processes:

```rust
// State variables per process: {idle, trying, critical}
// Need at least 2 bits per process = 4 bits total

let trans = build_peterson_transition(&bdd);
let init = build_initial_state(&bdd);

// Bad states: both processes in critical section
let bad = bdd.and(p1_critical, p2_critical);

// Check: can we reach bad states?
let reachable = symbolic_reachability(&bdd, init, trans);
let bad_reachable = bdd.and(reachable, bad);

if bdd.is_zero(bad_reachable) {
    println!("Verified: mutual exclusion holds!");
} else {
    println!("Bug found! Extracting counterexample...");
    let cex = extract_counterexample(&bdd, init, trans, bad);
}
```

== Limitations and Modern Approaches

BDD-based model checking, despite its power, has fundamental limits:
- *BDD blowup*: Some functions (like multiplication) have exponential BDDs regardless of variable ordering
- *Memory pressure*: Intermediate BDDs during image computation can be 10-100× larger than the final result
- *Ordering sensitivity*: The "right" ordering can mean the difference between seconds and days

Modern alternatives have emerged:
- *SAT-based BMC*: Bounded model checking unrolls transitions $k$ times and asks "is a bad state reachable in $k$ steps?"
- *IC3/PDR*: Property-directed reachability builds proofs incrementally, often without BDDs entirely
- *Hybrid approaches*: Use BDDs for control logic, SAT for data paths

#info-box(title: "When to Use BDDs")[
  BDDs excel when:
  - The system is highly regular (hardware, protocols)
  - You need to *count* or *enumerate* states
  - The property involves complex temporal patterns
  - You'll verify many properties on the same system

  Consider SAT/SMT when:
  - The instance is too big for BDDs
  - You only need to find *one* bug (not prove absence)
  - The system has irregular, data-dependent structure
]
