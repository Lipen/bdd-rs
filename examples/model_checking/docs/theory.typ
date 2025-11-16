#import "@preview/cetz:0.4.2"
#import "@preview/fletcher:0.5.8" as fletcher: diagram, edge, node

#set document(title: "Symbolic Model Checking: Theory and Implementation")
#set page(
  numbering: "1",
  number-align: center,
  margin: (x: 1.5cm, y: 2cm),
)
#set text(size: 12pt)
#set par(justify: true)
#set heading(numbering: "1.")

// Fix emptyset symbol
#show sym.emptyset: set text(font: "Libertinus Sans")

// Show i.e. in italic:
#show "i.e.": set text(style: "italic")
// Show e.g. in italic:
#show "e.g.": set text(style: "italic")
// Shot etc. in italic:
#show "etc.": set text(style: "italic")

// Blue emphasis for important terms
#show emph: set text(fill: rgb("#0066cc"))

// Enhanced code blocks
#show raw.where(block: true): it => block(
  fill: luma(95%),
  inset: 10pt,
  radius: 4pt,
  width: 100%,
  text(size: 0.8em, it),
)

// Custom theorem environments with enhanced styling
#let theorem(body, name: none) = block(
  fill: rgb("#e3f2fd"),
  stroke: (left: 3pt + rgb("#1976d2")),
  inset: 1em,
  radius: 3pt,
  breakable: true,
  [
    #text(fill: rgb("#1565c0"), weight: "bold")[
      Theorem#if name != none [ (#name)]
    ]: #body
  ],
)

#let definition(body, name: none) = block(
  fill: rgb("#f5f5f5"),
  stroke: (left: 3pt + rgb("#757575")),
  inset: 1em,
  radius: 3pt,
  breakable: true,
  [
    #text(fill: rgb("#424242"), weight: "bold")[
      Definition#if name != none [ (#name)]
    ]: #body
  ],
)

#let example(body, name: none) = block(
  fill: rgb("#fffde7"),
  stroke: (left: 3pt + rgb("#f9a825")),
  inset: 1em,
  radius: 3pt,
  breakable: true,
  [
    #text(fill: rgb("#bb6611"), weight: "bold")[
      Example#if name != none [ (#name)]
    ]: #body
  ],
)

#let note(body) = block(
  fill: rgb("#e8f5e9"),
  stroke: (left: 3pt + rgb("#66bb6a")),
  inset: 1em,
  radius: 3pt,
  breakable: true,
  [
    #text(fill: rgb("#388e3c"), weight: "bold")[
      Note
    ]: #body
  ],
)

#let Green(x) = text(green.darken(20%), x)
#let Red(x) = text(red.darken(20%), x)
#let Blue(x) = text(blue.darken(20%), x)

#let True = Green(`true`)
#let False = Red(`false`)

#let YES = Green(sym.checkmark)
#let NO = Red(sym.crossmark)

#align(center)[
  #text(size: 20pt, weight: "bold")[
    Symbolic Model Checking:\
    Theory and Implementation
  ]

  #v(1em)

  #text(size: 12pt)[
    A Comprehensive Guide to BDD-Based Verification
  ]

  #v(2em)

  #text(size: 11pt)[
    November 2025
  ]
]

#pagebreak()

#outline(depth: 2)

#pagebreak()

= Introduction

_Model checking_ is an automated formal verification technique that exhaustively explores all possible behaviors of a system to verify whether it satisfies specified properties.
Unlike _testing_, which examines selected execution scenarios, or _theorem proving_, which requires manual proof construction, model checking provides a fully automated "push-button" approach to verification.

The fundamental promise of model checking is compelling: *given a model of your system and a specification of desired behavior, the model checker will automatically determine whether the specification holds*.
If the property holds, you get a _proof_ of correctness.
If it fails, you get a _counterexample_ --- a concrete execution trace demonstrating the violation.

This makes model checking particularly valuable for:
- *Finding subtle bugs* that testing might miss (rare interleavings, corner cases)
- *Proving correctness* rather than merely building confidence through testing
- *Understanding failures* through concrete counterexamples
- *Exhaustive exploration* without writing test cases

== The Challenge: State Explosion

The fundamental challenge in model checking is the *state explosion problem*.
Consider a system with $n$ boolean variables:

$ |S| = 2^n $

where $S$ is the set of all possible states.
The number of states grows _exponentially_ with the number of variables.
For even modest systems:
- 10 variables $arrow.r.double$ 1,024 states
- 20 variables $arrow.r.double$ 1,048,576 states
- 30 variables $arrow.r.double$ 1,073,741,824 states (over a billion!)
- 100 variables $arrow.r.double$ $1.27 times 10^30$ states (impossible to enumerate!)

Traditional _explicit-state_ model checking stores each state individually, making verification infeasible for systems with more than a few million states.

Real systems easily exceed these limits:
- A simple mutual exclusion protocol with 10 processes: $> 10^10$ states
- A processor cache coherence protocol: $> 10^20$ states
- A distributed system with modest parallelism: $> 10^30$ states

The state explosion problem threatened to limit model checking to toy examples.

== The Solution: Symbolic Representation

_Symbolic model checking_ uses Boolean formulas to represent _sets of states_ rather than enumerating them individually.
This simple idea leads to dramatic improvements in scalability.

The key insight:

#definition[
  A set of states $S subset.eq {0,1}^n$ can be represented by its *characteristic function* $chi_S : {0,1}^n -> {0,1}$ where:
  $
    chi_S (s) = cases(
      1 "if" s in S,
      0 "if" s in.not S
    )
  $
]

Using *Binary Decision Diagrams (BDDs)*, we can represent these characteristic functions _compactly_ and perform operations _efficiently_.

#example(name: "The Power of Symbolic Representation")[
  Consider representing all even numbers from 0 to $2^100 - 1$:

  - *Explicit representation*: Store $2^99$ numbers individually
    - Memory required: $2^99 times 100$ bits $approx 10^29$ GB (impossible!)

  - *Symbolic representation*: Encode the formula "last bit = 0"
    - BDD representation: Single node checking bit $x_0$!
    - Memory required: $approx$ 100 bytes

  The characteristic function is simply $chi_"even" (x_0, x_1, ..., x_99) = overline(x_0)$ where $x_0$ is the least significant bit.

  This *exponential compression* --- representing $2^99$ states with a constant-sized BDD—is what makes symbolic model checking feasible.
]

This dramatic compression makes it possible to verify systems with $10^20$ states or more—systems that were completely intractable with explicit-state methods.

The compression works because many real systems have _structure_: states aren't random but follow patterns determined by the system's logic.
BDDs exploit this structure through _sharing_: common subformulas are represented once and reused throughout.

= Preliminaries

== States and State Spaces

#definition(name: "State")[
  A *state* is a complete assignment of values to all system variables.
  For a system with variables $V = {v_1, v_2, ..., v_n}$ where each $v_i in {0,1}$, a state is an element $s in {0,1}^n$.
]

#example(name: "Two-Bit Counter")[
  Consider a counter with two bits $x$ (high bit) and $y$ (low bit):

  #table(
    columns: 4,
    stroke: (x, y) => if y == 0 { (bottom: 0.8pt) },
    [*State*], [*$x$*], [*$y$*], [*Value*],
    [$s_0$], [0], [0], [0],
    [$s_1$], [1], [0], [1],
    [$s_2$], [0], [1], [2],
    [$s_3$], [1], [1], [3],
  )

  Each row represents one complete state of the system.
]

== Sets of States: Symbolic Representation

In symbolic model checking, we work with *sets of states* rather than individual states.
A set $S subset.eq {0,1}^n$ is represented by a Boolean formula $phi(v_1, ..., v_n)$ such that:

$ S = {s in {0,1}^n | phi(s) = 1} $

#example(name: "State Set")[
  For the two-bit counter, consider the set of "odd" states:

  $ S_"odd" = {s_1, s_3} = {(1,0), (1,1)} $

  This can be represented by the formula $phi_"odd" (x,y) = x$, meaning "states where $x = 1$".

  We can verify:
  - $phi_"odd" (0,0) = 0$ → $s_0 in.not S_"odd"$ ✓
  - $phi_"odd" (1,0) = 1$ → $s_1 in S_"odd"$ ✓
  - $phi_"odd" (0,1) = 0$ → $s_2 in.not S_"odd"$ ✓
  - $phi_"odd" (1,1) = 1$ → $s_3 in S_"odd"$ ✓
]

The power of this representation is that we can describe exponentially large sets with polynomial-sized formulas.

= Transition Systems

A transition system (also called a *Kripke structure*) formally models how a system evolves over time.

== Formal Definition

#definition(name: "Transition System")[
  A transition system is a tuple $M = (S, I, T, L)$ where:

  - $S$ is a finite set of *states*
  - $I subset.eq S$ is the set of *initial states*
  - $T subset.eq S times S$ is the *transition relation*
  - $L: S -> 2^("AP")$ is a *labeling function* mapping states to sets of atomic propositions

  We write $s -> s'$ to denote $(s, s') in T$, meaning "there is a transition from state $s$ to state $s'$".
]

#example(name: "Toggle System")[
  A simple system with one boolean variable $x$ that toggles between 0 and 1:

  #table(
    columns: 4,
    stroke: (x, y) => if y == 0 { (bottom: 0.8pt) },
    [*Component*], [*Symbolic*], [*Explicit*], [*Meaning*],
    [$S$], [${0,1}$], [${s_0, s_1}$], [Two states],
    [$I$], [$overline(x)$], [${s_0}$], [Start with $x=0$],
    [$T$], [$x xor x'$], [${(s_0,s_1), (s_1,s_0)}$], [Toggle],
    [$L$], [$L(s_0) = emptyset$, $L(s_1) = {"on"}$], [], [Label when $x=1$],
  )

  State diagram:

  #align(center)[
    #cetz.canvas({
      import cetz.draw: *

      circle((0, 0), radius: 0.8, stroke: 2pt, name: "s0")
      content("s0", [*s₀* \ $x=0$])

      circle((4, 0), radius: 0.8, stroke: 2pt, fill: rgb("#ffffcc"), name: "s1")
      content("s1", [*s₁* \ $x=1$ \ {"on"}])

      line((-1.5, 0), "s0.west", mark: (end: ">"), stroke: 1pt)
      content((-2.2, 0.3), [start])

      bezier("s0.east", "s1.west", (1.5, 0.6), (2.5, 0.6), mark: (end: ">"), stroke: 1pt)
      content((2, 0.8), [toggle])

      bezier("s1.west", "s0.east", (2.5, -0.6), (1.5, -0.6), mark: (end: ">"), stroke: 1pt)
      content((2, -0.8), [toggle])
    })
  ]
]

== Present and Next State Variables

To represent transitions symbolically, we use two copies of each variable:

#definition(name: "Present and Next State Variables")[
  For each state variable $v in V$, we introduce:
  - *Present-state variable* $v$ (sometimes written $v$ or $v_"pres"$): Represents the value in the *current* state
  - *Next-state variable* $v'$ (sometimes written $v_"next"$): Represents the value in the *next* state after a transition

  The full variable set is $V union V' = {v_1, ..., v_n, v'_1, ..., v'_n}$.
]

With this notation, the transition relation $T$ becomes a Boolean formula over $V union V'$:

$ T(v_1, ..., v_n, v'_1, ..., v'_n) $

The formula $T(s, s')$ evaluates to 1 if and only if there is a legal transition from state $s$ to state $s'$.

#example(name: "Toggle Transition Relation")[
  For the toggle system with variable $x$:

  $ T(x, x') = x xor x' = (x and overline(x')) or (overline(x) and x') $

  Let's verify all possible transitions:

  #table(
    columns: 5,
    stroke: (x, y) => if y == 0 { (bottom: 0.8pt) },
    [*Current ($x$)*], [*Next ($x'$)*], [*$T(x,x')$*], [*Legal?*], [*Meaning*],
    [0], [0], [0], [No], [Can't stay at 0],
    [0], [1], [1], [Yes], [From 0 to 1 ✓],
    [1], [0], [1], [Yes], [From 1 to 0 ✓],
    [1], [1], [0], [No], [Can't stay at 1],
  )
]

== Two-Bit Counter: Complete Example

Let's build a complete transition system for a 2-bit counter that increments modulo 4.

#example(name: "Two-Bit Counter Transition System")[

  *Variables*: $x$ (high bit), $y$ (low bit)

  *States*: $S = {(0,0), (1,0), (0,1), (1,1)}$ representing values 0, 1, 2, 3

  *Initial state*: $I = {(0,0)}$, represented by formula $overline(x) and overline(y)$

  *Transitions*: Increment by 1 (mod 4):
  - $(0,0) -> (1,0)$ (0→1)
  - $(1,0) -> (0,1)$ (1→2)
  - $(0,1) -> (1,1)$ (2→3)
  - $(1,1) -> (0,0)$ (3→0)

  *Transition relation*: How do we encode this symbolically?

  Observe the pattern:
  - $y$ always flips: $y' = overline(y)$
  - $x$ flips when $y = 1$: $x' = x xor y$

  Therefore:
  $ T(x, y, x', y') = (x' equiv x xor y) and (y' equiv overline(y)) $


  where $equiv$ denotes logical equivalence (XNOR).

  State diagram:

  #align(center)[
    #cetz.canvas({
      import cetz.draw: *

      let node-style = (stroke: 1.5pt, radius: 0.8)

      circle((0, 0), ..node-style, fill: rgb("#e3f2fd"), name: "s0")
      content("s0", align(center)[*s₀* \ $(0,0)$ \ val=0])

      circle((0, -3), ..node-style, name: "s1")
      content("s1", [*s₁* \ $(1,0)$ \ val=1])

      circle((3, -3), ..node-style, name: "s2")
      content("s2", [*s₂* \ $(0,1)$ \ val=2])

      circle((3, 0), ..node-style, name: "s3")
      content("s3", [*s₃* \ $(1,1)$ \ val=3])

      line((-1.5, 0), "s0.west", mark: (end: ">"), stroke: 1pt)
      content((-1.8, 0), [start])

      line("s0.south", "s1.north", mark: (end: ">"), stroke: 1pt)
      content((0, -1.5), [$y -> 1$], anchor: "east", padding: 0.2)

      line("s1.east", "s2.west", mark: (end: ">"), stroke: 1pt)
      content((1.5, -3), [$y -> 0,\ x -> 0$], anchor: "south", padding: 0.2)

      line("s2.north", "s3.south", mark: (end: ">"), stroke: 1pt)
      content((3, -1.5), [$y -> 1$], anchor: "west", padding: 0.2)

      line("s3.west", "s0.east", mark: (end: ">"), stroke: 1pt)
      content((1.5, 0), [$y -> 0,\ x -> 0$], anchor: "south", padding: 0.2)
    })
  ]
]

= Symbolic State Space Exploration

Now that we can represent states and transitions symbolically, we need operations to explore the state space.
The two fundamental operations are *image* (forward reachability) and *preimage* (backward reachability).

== Image: Forward Reachability

#definition(name: "Image Operation")[
  Given a set of states $S$ and a transition relation $T$, the *image* of $S$ under $T$ is the set of all states reachable from $S$ in one transition:

  $ "Img"(S, T) = {s' | exists s in S : (s, s') in T} $

  In logical notation:
  $ "Img"(S, T) = exists v_1, ..., v_n . S(v_1, ..., v_n) and T(v_1, ..., v_n, v'_1, ..., v'_n) $
]

Intuitively, the image operation answers: "Where can I go in one step from these states?"

=== Computing the Image

The image computation has three steps:

+ *Conjunction*: $S(v) and T(v, v')$ --- combine current states with transition relation
+ *Existential quantification*: $exists v . (S(v) and T(v, v'))$ --- eliminate present-state variables
+ *Variable renaming*: Rename $v'$ back to $v$ for the result

#example(name: "Image of Toggle System")[
  Consider the toggle system with $T(x, x') = x xor x'$.

  *Question*: From state $s_0$ (where $x=0$), what states can we reach?

  $S = {s_0}$ is represented by $overline(x)$.

  *Step 1: Conjunction*

  $
    S(x) and T(x, x') & = overline(x) and (x xor x') \
                      & = overline(x) and ((x and overline(x')) or (overline(x) and x')) \
                      & = overline(x) and x'
  $

  (The term $x and overline(x')$ vanishes because $x = 0$)

  *Step 2: Existential Quantification*

  $ exists x . (overline(x) and x') = x' $

  We eliminate $x$ by computing:
  $ (overline(x) and x')[x -> 0] or (overline(x) and x')[x -> 1] = (1 and x') or (0 and x') = x' $

  *Step 3: Rename*

  Rename $x'$ to $x$: result is $x$, which represents state $s_1$ where $x=1$. ✓

  *Conclusion*: From $x=0$, we can reach $x=1$ in one step.
]

=== Reachability Analysis

The image operation enables us to compute *all* reachable states through iterative fixpoint computation:

#theorem(name: "Reachable States")[
  The set of all states reachable from initial states $I$ is the least fixpoint:

  $ R^* = mu Z . I or "Img"(Z, T) $

  Algorithmically:

  ```
  R := I
  loop:
    R_new := R ∪ Img(R, T)
    if R_new = R: break
    R := R_new
  return R
  ```
]

#example(name: "Reachability in Two-Bit Counter")[
  Starting from $(0,0)$, what states are reachable?

  $
    R_0 & = I = {(0,0)} \
    R_1 & = R_0 union "Img"(R_0) = {(0,0)} union {(1,0)} = {(0,0), (1,0)} \
    R_2 & = R_1 union "Img"(R_1) = {(0,0), (1,0)} union {(1,0), (0,1)} \
        & = {(0,0), (1,0), (0,1)} \
    R_3 & = R_2 union "Img"(R_2) = {(0,0), (1,0), (0,1)} union {(1,0), (0,1), (1,1)} \
        & = {(0,0), (1,0), (0,1), (1,1)} \
    R_4 & = R_3 union "Img"(R_3) \
        & = {(0,0), (1,0), (0,1), (1,1)} union {(1,0), (0,1), (1,1), (0,0)} \
        & = {(0,0), (1,0), (0,1), (1,1)} = R_3
  $

  Fixpoint reached! All four states are reachable.
]

= The Modal Mu-Calculus: Foundation of Fixpoints

Before diving into CTL, we need to understand the _modal mu-calculus_ --- the theoretical foundation underlying fixpoint-based model checking.
This calculus provides the mathematical framework for expressing recursive properties through least ($mu$) and greatest ($nu$) fixpoints.

== Why Fixpoints?

Many temporal properties are inherently _recursive_: to determine if a property holds, we need to check both the current state and future states, which themselves require checking their futures, and so on.
Fixpoints provide a elegant mathematical mechanism to handle this recursion.

#definition(name: "Fixpoint")[
  Let $f: 2^S -> 2^S$ be a _monotone_ function on sets of states (i.e., $X subset.eq Y => f(X) subset.eq f(Y)$).

  - A set $X subset.eq S$ is a *fixpoint* of $f$ if $f(X) = X$
  - The *least fixpoint* $mu Z . f(Z)$ is the smallest set $X$ such that $f(X) = X$
  - The *greatest fixpoint* $nu Z . f(Z)$ is the largest set $X$ such that $f(X) = X$
]

#theorem(name: "Knaster-Tarski")[
  For any monotone function $f: 2^S -> 2^S$ on a finite lattice:

  - The least fixpoint exists and equals: $mu Z . f(Z) = inter.big {X | f(X) subset.eq X}$
  - The greatest fixpoint exists and equals: $nu Z . f(Z) = union.big {X | X subset.eq f(X)}$

  Moreover, these can be computed iteratively:
  - $mu Z . f(Z) = union.big_(i=0)^infinity f^i (emptyset) = emptyset union f(emptyset) union f(f(emptyset)) union ...$
  - $nu Z . f(Z) = inter.big_(i=0)^infinity f^i (S) = S inter f(S) inter f(f(S)) inter ...$
]

== Intuition: Least vs Greatest Fixpoints

#note[
  The key difference lies in what we're trying to prove:

  *Least fixpoint ($mu$)*: "Eventually reaches the property"
  - Start from nothing ($emptyset$)
  - Iteratively add states that can reach the property
  - Converges to _minimal_ set of states satisfying the property
  - Used for: *EF* (eventually), *reachability*, *termination*

  *Greatest fixpoint ($nu$)*: "Always maintains the property"
  - Start from everything ($S$)
  - Iteratively remove states that violate the property
  - Converges to _maximal_ set of states satisfying the property
  - Used for: *AG* (always), *invariants*, *safety*
]

#example(name: "Fixpoint Intuition: Reachability")[
  Consider computing states from which we can reach a target set $T$.

  Define $f(Z) = T union "Pre"(Z)$ ("target or can reach $Z$ in one step").

  *Least fixpoint* $mu Z . f(Z)$:

  $
    Z_0 & = emptyset \
    Z_1 & = T union "Pre"(emptyset) = T \
    Z_2 & = T union "Pre"(T) = "states reaching" T "in" <= 1 "step" \
    Z_3 & = T union "Pre"(Z_2) = "states reaching" T "in" <= 2 "steps" \
        & dots.v
  $

  Converges to _all_ states that can _eventually_ reach $T$.
]

#example(name: "Fixpoint Intuition: Invariants")[
  Consider computing states from which property $P$ _always_ holds.

  Define $f(Z) = P inter "Pre"(Z)$ ("$P$ holds and all successors in $Z$").

  *Greatest fixpoint* $nu Z . f(Z)$:

  $
    Z_0 & = S "  (all states)" \
    Z_1 & = P inter "Pre"(S) = P "  (states satisfying" P "with any successor)" \
    Z_2 & = P inter "Pre"(Z_1) = "states where" P "holds and all successors satisfy" P \
    Z_3 & = P inter "Pre"(Z_2) = "states where" P "always holds for" >= 2 "steps" \
        & dots.v
  $

  Converges to states from which $P$ holds on _all_ future paths forever.
]

== Why Is This Confusing?

The mu-calculus notation can be initially perplexing for several reasons:

+ *Variable binding*: The $Z$ in $mu Z . f(Z)$ is a bound variable ranging over _sets of states_, not individual states
+ *Monotonicity requirement*: Functions must be monotone for fixpoints to exist
+ *Nested fixpoints*: Complex properties involve alternating $mu$ and $nu$, creating intricate recursive structures
+ *Dual nature*: $mu$ computes from below (pessimistic), $nu$ from above (optimistic)

#note[
  Think of $mu$ as "prove by construction" (build up the set) and $nu$ as "prove by elimination" (remove counterexamples).

  - $mu Z . phi or "EX" Z$: Start with $phi$, expand to states reaching $phi$
  - $nu Z . phi and "AX" Z$: Start with all states, keep only those satisfying $phi$ with all successors good
]

= CTL Model Checking

CTL (Computation Tree Logic) is a temporal logic for specifying properties about how systems evolve over time.
It allows us to express complex requirements about system behavior in a precise mathematical way.
Every CTL operator can be understood as a fixpoint computation!

== The Computation Tree

From any state, multiple futures may be possible due to non-determinism.
This creates a tree structure where each node is a state and each path represents one possible execution sequence.

#example(name: "Computation Tree")[
  For a system with non-deterministic choice:

  ```
                s₀ (initial)
               /  \
              /    \
            s₁      s₂
           / \      |
          s₃  s₄    s₅
          ...  ...  ...
  ```

  Each path from root to leaves represents one possible execution.
]

== CTL Syntax

#definition(name: "CTL Formula Syntax")[
  CTL formulas $phi$ are defined by the grammar:

  $
    phi & ::= p | top | bot | not phi | phi and psi | phi or psi | phi => psi \
        & | "EX" phi | "AX" phi | "EF" phi | "AF" phi | "EG" phi | "AG" phi \
        & | "E"[phi "U" psi] | "A"[phi "U" psi]
  $

  where $p$ is an atomic proposition from the labeling function $L$.
]

=== Path Quantifiers

- *E* (Exists): "There exists at least one path where..."
- *A* (All): "For all possible paths..."

=== Temporal Operators

- *X* (neXt): Property holds in the immediate next state
- *F* (Finally): Property eventually becomes true (in the Future)
- *G* (Globally): Property remains true forever (Always)
- *U* (Until): First property holds until second becomes true

=== CTL Operators: Informal Semantics

#table(
  columns: 3,
  stroke: (x, y) => if y == 0 { (bottom: 0.8pt) },
  [*Formula*], [*Informal Meaning*], [*Example*],
  [*EX* $phi$], [Possibly next $phi$], [System can transition to a state satisfying $phi$],
  [*AX* $phi$], [Necessarily next $phi$], [All possible next states satisfy $phi$],
  [*EF* $phi$], [Possibly eventually $phi$], [There's a path where $phi$ becomes true],
  [*AF* $phi$], [Inevitably $phi$], [On all paths, $phi$ eventually becomes true],
  [*EG* $phi$], [Possibly always $phi$], [There's a path where $phi$ remains true forever],
  [*AG* $phi$], [Invariantly $phi$], [On all paths, $phi$ remains true forever],
  [*E*[$phi$ *U* $psi$]], [Possibly $phi$ until $psi$], [There's a path: $phi$ holds until $psi$ becomes true],
  [*A*[$phi$ *U* $psi$]], [Inevitably $phi$ until $psi$], [On all paths: $phi$ holds until $psi$ becomes true],
)

== CTL Semantics: Formal Definition

Let $M = (S, I, T, L)$ be a transition system and $s in S$ be a state.
We write $M, s models phi$ to mean "state $s$ satisfies formula $phi$ in model $M$".

#definition(name: "CTL Semantics")[
  The satisfaction relation $models$ is defined recursively:

  / Atomic propositions:
  $ M, s models p <==> p in L(s) $

  / Boolean operators:
  $
        M, s models not phi & <==> "not" (M, s models phi) \
    M, s models phi and psi & <==> (M, s models phi) "and" (M, s models psi) \
     M, s models phi or psi & <==> (M, s models phi) "or" (M, s models psi)
  $

  / Temporal operators:
  $
    M, s models "EX" phi & <==> exists s' : (s, s') in T and M, s' models phi \
    M, s models "AX" phi & <==> forall s' : (s, s') in T => M, s' models phi \
    M, s models "EF" phi & <==> exists pi = s_0, s_1, ... : s_0 = s and exists i >= 0 : M, s_i models phi \
    M, s models "AF" phi & <==> forall pi = s_0, s_1, ... : s_0 = s => exists i >= 0 : M, s_i models phi
  $
]

== Properties: Safety and Liveness

CTL formulas typically express either _safety_ or _liveness_ properties --- the two fundamental classes of system requirements.

#definition(name: "Safety Property")[
  A *safety property* asserts that "something bad never happens":

  $ "AG"(not "bad") $

  This means: on all paths, globally (always), the bad condition does not hold.
  Safety properties express _invariants_ --- conditions that must hold in every reachable state.
]

#example(name: "Safety Properties")[
  / Mutual exclusion: $"AG"(not ("critical"_1 and "critical"_2))$ \
    "Two processes are never simultaneously in the critical section"

  / No buffer overflow: $"AG"("count" <= "capacity")$ \
    "The buffer count never exceeds capacity"

  / No division by zero: $"AG"("divisor" != 0)$ \
    "The divisor is always non-zero"

  / Type safety: $"AG"(not "type-error")$ \
    "No type errors occur during execution"

  / Memory safety: $"AG"("allocated" => not "freed")$ \
    "Accessing only allocated memory"
]

#definition(name: "Liveness Property")[
  A *liveness property* asserts that "something good eventually happens":

  $ "AF"("good") $

  This means: on all paths, eventually (in the future), the good condition holds.
  Liveness properties ensure _progress_ --- the system doesn't get stuck but eventually achieves desired outcomes.
]

#example(name: "Liveness Properties")[
  / Termination: $"AF"("terminated")$ \
    "The process eventually terminates"

  / Request-response: $"AG"("request" => "AF" "response")$ \
    "Every request is eventually responded to"

  / Fair scheduling: $"AG"("waiting" => "AF" "granted")$ \
    "Every waiting process is eventually granted access"

  / Deadlock freedom: $"AG"("EF" "enabled")$ \
    "From every state, some action is eventually enabled"

  / Message delivery: $"AG"("sent" => "AF" "received")$ \
    "Every sent message is eventually received"
]

== Concrete Example: Traffic Light Controller

Let's work through a complete, detailed example to see how CTL properties capture real system requirements.

#example(name: "Traffic Light System")[
  Consider a simple traffic light controller for a two-way intersection (North-South and East-West).

  *State variables:*
  - `ns_light` $in$ {red, yellow, green}
  - `ew_light` $in$ {red, yellow, green}
  - `timer` $in$ {0, 1, 2, 3} (countdown timer)

  *Transitions:*
  - Green lasts 3 cycles, then yellow for 1 cycle, then red
  - When one direction turns red, the other turns green
  - Timer decrements each cycle

  *Key properties to verify:*

  #table(
    columns: 2,
    stroke: (x, y) => if y == 0 { (bottom: 0.8pt) },
    [*Property*], [*CTL Formula*],
    [*Safety*: Never both green], [$"AG"(not ("ns"_"green" and "ew"_"green"))$],
    [*Safety*: Red before green], [$"AG"("ns"_"red" => "AX"(not "ns"_"green"))$],
    [*Liveness*: Eventually green], [$"AG"("ns"_"red" => "AF" "ns"_"green")$],
    [*Liveness*: Cycles through states], [$"AG"("EF" "ns"_"green" and "EF" "ew"_"green")$],
    [*Fairness*: Both get green], [$"AG"("AF" "ns"_"green") and "AG"("AF" "ew"_"green")$],
  )

  Let's verify the first property in detail: *Never both green simultaneously*.

  *Step 1: Encode bad states*

  $ "bad" = "ns"_"green" and "ew"_"green" $

  *Step 2: Compute* $"AG"(not "bad")$ *via greatest fixpoint*

  Recall: $"AG" phi = nu Z . phi and "AX" Z$

  $
    Z_0 & = S quad "(all states)" \
    Z_1 & = (not "bad") and "AX" Z_0 \
        & = (not "bad") and S = (not "bad") \
        & = "states where not both green" \
    Z_2 & = (not "bad") and "AX" Z_1 \
        & = (not "bad") and "all successors also satisfy" (not "bad")
  $

  If the transition relation is correctly designed (never transitions to both-green state), then $Z_2 = Z_1$ and the property holds!

  *Step 3: Check initial states*

  If $I subset.eq Z_"final"$, property is verified ✓

  If not, model checker produces a _counterexample_: a path $s_0 -> s_1 -> ... -> s_k$ where $s_k in "bad"$.
]

#example(name: "Detailed Walkthrough: Request-Response")[
  Consider a client-server system where clients make requests and expect responses.

  *Variables:*
  - `request`: boolean (client has pending request)
  - `processing`: boolean (server is processing)
  - `response`: boolean (response ready)

  *Desired property:* Every request eventually gets a response.

  $ "AG"("request" => "AF" "response") $

  Reading: "Always, if there's a request, then on all future paths, eventually there's a response."

  Let's compute this step by step.

  *Subformula 1:* $"AF" "response"$ --- states from which response is inevitable

  Using $"AF" phi = mu Z . phi or "AX" Z$:  $ Z_0 & = emptyset \
  Z_1 & = "response" or "AX" Z_0 = "response" \
  Z_2 & = "response" or "AX" Z_1 \
      & = "response" or "Pre"("response") \
      & = "states where response holds or is reachable in 1 step" \
  Z_3 & = "response" or "AX" Z_2 \
      & = "states reaching response in" <= 2 "steps" \
      & dots.v $

  Converges to $R = "states from which response is inevitable"$.

  *Subformula 2:* $"request" => "AF" "response"$ --- equivalent to $not "request" or "AF" "response"$

  $ phi_"rr" = (not "request") or R $

  *Main formula:* $"AG" phi_"rr"$ --- always holds  Using $"AG" phi = nu Z . phi and "AX" Z$:

  $
    W_0 & = S \
    W_1 & = phi_"rr" and "AX" W_0 = phi_"rr" \
    W_2 & = phi_"rr" and "AX" W_1 \
        & = phi_"rr" and "Pre"(phi_"rr") \
        & dots.v
  $

  If $I subset.eq W_"final"$, the property holds: every request gets a response! ✓

  *Counterexample scenario:*
  If the server has a bug where it sometimes ignores requests, there might be a path:

  $ s_0 ("no request") -> s_1 ("request sent") -> s_2 ("stuck, no response") -> s_2 -> s_2 -> ... $

  State $s_2$ would _not_ be in $R$ (response inevitable), so $s_1 in.not W_"final"$, and the model checker would report this path as a counterexample.
]

== Fixpoint Characterization

The key insight for symbolic model checking is that CTL operators can be computed as fixpoints of monotone functions over sets of states.

#theorem(name: "CTL Fixpoint Characterization")[
  The CTL temporal operators have the following fixpoint characterizations:

  $
            "EF" phi & = mu Z . phi or "EX" Z \
            "AF" phi & = mu Z . phi or "AX" Z \
            "EG" phi & = nu Z . phi and "EX" Z \
            "AG" phi & = nu Z . phi and "AX" Z \
    "E"[phi "U" psi] & = mu Z . psi or (phi and "EX" Z) \
    "A"[phi "U" psi] & = mu Z . psi or (phi and "AX" Z)
  $

  where:
  - $mu Z . f(Z)$ denotes the *least fixpoint* (start from $emptyset$, iterate)
  - $nu Z . f(Z)$ denotes the *greatest fixpoint* (start from $S$, iterate)
]

=== Least Fixpoint ($mu$)

For formulas like *EF* $phi$ (exists eventually), we compute the *least fixpoint*:

```
Z₀ := ∅
Z₁ := φ ∨ EX Z₀ = φ
Z₂ := φ ∨ EX Z₁  (states reaching φ in ≤1 step)
Z₃ := φ ∨ EX Z₂  (states reaching φ in ≤2 steps)
...
```

Iteration continues until $Z_(i+1) = Z_i$ (fixpoint reached).

#example(name: "EF Computation")[
  Consider checking $"EF"("x" = 1)$ on the two-bit counter starting from $(0,0)$.

  Let $phi = (x = 1) = {(1,0), (1,1)}$ (states where $x = 1$).

  $
    Z_0 & = emptyset \
    Z_1 & = phi or "EX" Z_0 = {(1,0), (1,1)} or emptyset = {(1,0), (1,1)} \
    Z_2 & = phi or "EX" Z_1 = {(1,0), (1,1)} or "Pre"({(1,0), (1,1)}) \
        & = {(1,0), (1,1)} or {(0,0), (0,1)} = {(0,0), (1,0), (0,1), (1,1)} \
    Z_3 & = phi or "EX" Z_2 = {(1,0), (1,1)} or "Pre"({(0,0), (1,0), (0,1), (1,1)}) \
        & = {(0,0), (1,0), (0,1), (1,1)} = Z_2
  $

  Fixpoint!
  All states satisfy $"EF"("x" = 1)$, meaning $x = 1$ is reachable from all states.
]

=== Greatest Fixpoint ($nu$)

For formulas like *AG* $phi$ (always globally), we compute the *greatest fixpoint*:

```
Z₀ := S (all states)
Z₁ := φ ∧ AX Z₀
Z₂ := φ ∧ AX Z₁  (states where φ holds and all successors in Z₁)
...
```

#example(name: "AG Computation")[
  Check $"AG"("x" = 0)$ on the two-bit counter.

  Let $phi = (x = 0) = {(0,0), (0,1)}$.

  $
    Z_0 & = S = {(0,0), (1,0), (0,1), (1,1)} \
    Z_1 & = phi and "AX" Z_0 = {(0,0), (0,1)} and S = {(0,0), (0,1)} \
    Z_2 & = phi and "AX" Z_1 = {(0,0), (0,1)} and "AX"({(0,0), (0,1)}) \
        & = {(0,0), (0,1)} and emptyset = emptyset
  $

  Why?
  Because $(0,0)$ transitions to $(1,0) in.not {(0,0), (0,1)}$.

  Result: $emptyset$ means no state satisfies $"AG"("x" = 0)$.
  Property fails!
]

== Symbolic CTL Model Checking Algorithm

#theorem(name: "Symbolic Model Checking")[
  Given a transition system $M$ and CTL formula $phi$, we can compute the set of states satisfying $phi$:

  $ "SAT"(phi) = {s in S | M, s models phi} $

  as a BDD in time polynomial in $|phi|$ and the BDD sizes.
]

The algorithm proceeds by structural induction on $phi$:

/ Base case ($phi = p$):
  $ "SAT"(p) = {s | p in L(s)} $ (given by labeling function)

/ Boolean operators:
  $
        "SAT"(not phi) & = overline("SAT"(phi)) \
    "SAT"(phi and psi) & = "SAT"(phi) inter "SAT"(psi) \
     "SAT"(phi or psi) & = "SAT"(phi) union "SAT"(psi)
  $

/ EX operator:
  $ "SAT"("EX" phi) = "Pre"("SAT"(phi), T) $

/ AX operator:
  $ "SAT"("AX" phi) = overline("SAT"("EX"(not phi))) $

/ EF operator (least fixpoint):
  ```
  Z := SAT(φ)
  loop:
    Z_new := Z ∪ Pre(Z, T)
    if Z_new = Z: break
    Z := Z_new
  return Z
  ```

/ AG operator (greatest fixpoint):
  ```
  Z := S (all states)
  loop:
    Z_new := SAT(φ) ∩ Pre(Z, T)
    if Z_new = Z: break
    Z := Z_new
  return Z
  ```

#example(name: "Complete Verification")[
  Let's verify mutual exclusion in a simple protocol.

  *System*: Two processes, each with three control states

  *Property*: $"AG"(not ("critical"_1 and "critical"_2))$

  *Steps*:
  1. Encode system as BDD transition relation
  2. Compute $"SAT"("critical"_1 and "critical"_2)$ = bad states
  3. Compute $"SAT"("AG"(not "bad"))$ via greatest fixpoint
  4. Check if initial state $in "SAT"("AG"(not "bad"))$

  If yes: property holds ✓ \
  If no: counterexample exists (extract witness path)
]

== Programming Example: Using bdd-rs for Model Checking

Let's see how to implement model checking using the `bdd-rs` library.
This example demonstrates building a transition system and verifying CTL properties programmatically.

```rust
use bdd::BddManager;
use std::collections::HashMap;

/// A simple model checking framework using BDDs
struct ModelChecker {
    bdd: BddManager,
    // Map variable names to BDD variable indices
    vars: HashMap<String, usize>,
    // Present and next-state variable pairs
    present_vars: Vec<usize>,
    next_vars: Vec<usize>,
    // Transition relation T(v, v')
    transition: usize,
    // Initial states I(v)
    initial: usize,
    // Atomic proposition labels
    labels: HashMap<String, usize>,
}

impl ModelChecker {
    fn new() -> Self {
        Self {
            bdd: BddManager::new(),
            vars: HashMap::new(),
            present_vars: Vec::new(),
            next_vars: Vec::new(),
            transition: 0, // Will be set later
            initial: 0,
            labels: HashMap::new(),
        }
    }

    /// Declare a state variable (creates both present and next)
    fn declare_var(&mut self, name: &str) -> (usize, usize) {
        let present = self.bdd.new_var();
        let next = self.bdd.new_var();
        self.vars.insert(name.to_string(), present);
        self.vars.insert(format!("{}'", name), next);
        self.present_vars.push(present);
        self.next_vars.push(next);
        (present, next)
    }

    /// Compute image: successors of states in 'from'
    fn image(&self, from: usize) -> usize {
        // Step 1: Conjunction from(v) ∧ T(v,v')
        let conj = self.bdd.and(from, self.transition);

        // Step 2: Eliminate present-state variables
        let mut result = conj;
        for &var in &self.present_vars {
            result = self.bdd.exists(result, var);
        }

        // Step 3: Rename next-state to present-state
        self.rename_next_to_present(result)
    }

    /// Compute preimage: predecessors of states in 'to'
    fn preimage(&self, to: usize) -> usize {
        // Step 1: Rename to(v) -> to(v')
        let to_next = self.rename_present_to_next(to);

        // Step 2: Conjunction T(v,v') ∧ to(v')
        let conj = self.bdd.and(self.transition, to_next);

        // Step 3: Eliminate next-state variables
        let mut result = conj;
        for &var in &self.next_vars {
            result = self.bdd.exists(result, var);
        }

        result
    }

    /// Compute EF φ: states that can eventually reach φ
    fn eventually(&self, phi: usize) -> usize {
        // μZ. φ ∨ EX Z = μZ. φ ∨ Pre(Z)
        let mut z = phi;
        loop {
            let pre_z = self.preimage(z);
            let z_new = self.bdd.or(phi, pre_z);
            if z_new == z {
                return z;
            }
            z = z_new;
        }
    }

    /// Compute AG φ: states where φ always holds
    fn always(&self, phi: usize) -> usize {
        // νZ. φ ∧ AX Z = νZ. φ ∧ Pre(Z)
        let mut z = self.bdd.constant(true);
        loop {
            let pre_z = self.preimage(z);
            let z_new = self.bdd.and(phi, pre_z);
            if z_new == z {
                return z;
            }
            z = z_new;
        }
    }

    /// Check if property holds from initial states
    fn check(&self, property: usize) -> bool {
        // initial ⊆ property  ⟺  initial ∧ ¬property = ∅
        let not_prop = self.bdd.not(property);
        let bad = self.bdd.and(self.initial, not_prop);
        self.bdd.is_false(bad)
    }

    // Helper: rename variables (implementation omitted for brevity)
    fn rename_next_to_present(&self, f: usize) -> usize {
        /* compose next vars with present vars */
        todo!()
    }

    fn rename_present_to_next(&self, f: usize) -> usize {
        /* compose present vars with next vars */
        todo!()
    }
}

/// Example: Two-bit counter model checking
fn main() {
    let mut mc = ModelChecker::new();

    // Declare variables: x (high bit), y (low bit)
    let (x, x_next) = mc.declare_var("x");
    let (y, y_next) = mc.declare_var("y");

    // Initial state: (0, 0)
    let not_x = mc.bdd.not(mc.bdd.var(x));
    let not_y = mc.bdd.not(mc.bdd.var(y));
    mc.initial = mc.bdd.and(not_x, not_y);

    // Transition relation: y' = ¬y, x' = x ⊕ y
    let y_flips = mc.bdd.xor(mc.bdd.var(y_next), mc.bdd.var(y));
    let x_flips = mc.bdd.equiv(
        mc.bdd.var(x_next),
        mc.bdd.xor(mc.bdd.var(x), mc.bdd.var(y))
    );
    mc.transition = mc.bdd.and(y_flips, x_flips);

    // Label: "odd" = x holds
    mc.labels.insert("odd".to_string(), mc.bdd.var(x));

    // Property 1: AG(count < 4)  — always true (trivial)
    let always_valid = mc.bdd.constant(true);
    assert!(mc.check(mc.always(always_valid)));
    println!("✓ Property 1: Always valid (count < 4)");

    // Property 2: AG EF(odd)  — can always reach odd states
    let odd = mc.labels["odd"];
    let ef_odd = mc.eventually(odd);
    let ag_ef_odd = mc.always(ef_odd);
    assert!(mc.check(ag_ef_odd));
    println!("✓ Property 2: Can always eventually reach odd state");

    // Property 3: AG(even → AF odd)  — from even, eventually odd
    let even = mc.bdd.not(odd);
    let af_odd = mc.eventually(odd); // In this case, AF = EF (deterministic)
    let implies = mc.bdd.or(odd, af_odd);
    let property = mc.always(implies);
    assert!(mc.check(property));
    println!("✓ Property 3: From even, eventually odd");
}
```

This example demonstrates:
- Declaring state variables with present/next-state pairs
- Building transition relations symbolically
- Implementing image/preimage operations
- Computing fixpoints for temporal operators
- Verifying properties from initial states

The actual `bdd-rs` library in this repository provides these operations through its core BDD manipulation functions.

= Implementation

This section describes how symbolic model checking is implemented in practice using BDDs.

== BDD Representation

Binary Decision Diagrams (BDDs) are the key data structure enabling symbolic model checking.
A BDD is a directed acyclic graph representing a Boolean function.

#definition(name: "Binary Decision Diagram")[
  A BDD is a rooted, directed acyclic graph where:
  - Each internal node is labeled with a boolean variable
  - Each internal node has two outgoing edges: low (dashed, for variable=0) and high (solid, for variable=1)
  - There are two terminal nodes: 0 (false) and 1 (true)
  - All paths from root to terminals respect a fixed variable ordering
]

#example(name: "BDD for XOR")[
  The function $f(x,y) = x xor y$ can be represented as a BDD:

  #align(center)[
    #cetz.canvas(length: 1.2cm, {
      import cetz.draw: *

      // Root node
      circle((0, 0), radius: 0.4, stroke: 1.5pt, name: "x")
      content("x", [$x$])

      // Second level
      circle((-1.5, -1.5), radius: 0.4, stroke: 1.5pt, name: "y0")
      content("y0", [$y$])
      circle((1.5, -1.5), radius: 0.4, stroke: 1.5pt, name: "y1")
      content("y1", [$y$])

      // Terminal nodes
      rect((-2.5, -3), (-1.8, -2.4), stroke: 2pt, fill: rgb("#ffcccc"), name: "f0")
      content("f0", [*0*])

      rect((-1.2, -3), (-0.5, -2.4), stroke: 2pt, fill: rgb("#ccffcc"), name: "t0")
      content("t0", [*1*])

      rect((0.5, -3), (1.2, -2.4), stroke: 2pt, fill: rgb("#ccffcc"), name: "t1")
      content("t1", [*1*])

      rect((1.8, -3), (2.5, -2.4), stroke: 2pt, fill: rgb("#ffcccc"), name: "f1")
      content("f1", [*0*])

      // Edges from x (dashed = low, solid = high)
      line("x", "y0", stroke: (dash: "dashed", paint: black), mark: (end: ">", fill: black, stroke: 1pt + black))
      content((-0.7, -0.5), [0], fill: white)

      line("x", "y1", stroke: 1.5pt, mark: (end: ">", fill: black, stroke: 1pt + black))
      content((0.7, -0.5), [1], fill: white)

      // Edges from y nodes
      line("y0", "f0", stroke: (dash: "dashed", paint: black), mark: (end: ">", fill: black, stroke: 1pt + black))
      line("y0", "t0", stroke: 1.5pt, mark: (end: ">", fill: black, stroke: 1pt + black))
      line("y1", "t1", stroke: 1.5pt, mark: (end: ">", fill: black, stroke: 1pt + black))
      line("y1", "f1", stroke: (dash: "dashed", paint: black), mark: (end: ">", fill: black, stroke: 1pt + black))
    })
  ]

  Reading the BDD:
  - Start at root node $x$
  - Dashed edge (low): follow when variable = 0
  - Solid edge (high): follow when variable = 1
  - Terminal *0*: function evaluates to false
  - Terminal *1*: function evaluates to true

  Example evaluation for $x=0, y=1$:
  - At $x$: take dashed (low) edge to left $y$ node
  - At $y$: take solid (high) edge to terminal *1*
  - Result: $0 xor 1 = 1$ ✓
]

=== Reduced Ordered BDDs (ROBDDs)

To ensure canonicity (same function = same BDD), we enforce two reduction rules:

+ *Merge isomorphic subgraphs*: If two nodes have identical low/high children and same variable, merge them
+ *Remove redundant tests*: If low and high children are identical, bypass the node

#theorem(name: "Canonical Form")[
  Given a fixed variable ordering, every Boolean function has a unique reduced ordered BDD representation.
]

This canonicity enables:
- *Constant-time equality checking*: Same function ↔ same BDD pointer
- *Hash consing*: Automatic sharing of subformulas

== Variable Management: Present and Next

The implementation maintains two BDD variables for each state variable:

```rust
struct VarManager {
    // Maps each Var to (present_index, next_index)
    vars: HashMap<Var, (usize, usize)>,
    next_var_index: usize,
}

impl VarManager {
    fn declare_var(&mut self, v: Var) -> (usize, usize) {
        let pres = self.next_var_index;
        let next = self.next_var_index + 1;
        self.next_var_index += 2;
        self.vars.insert(v, (pres, next));
        (pres, next)
    }

    fn get_present(&self, v: &Var) -> Option<usize> {
        self.vars.get(v).map(|(p, _)| *p)
    }

    fn get_next(&self, v: &Var) -> Option<usize> {
        self.vars.get(v).map(|(_, n)| *n)
    }
}
```

This ensures:
- Consecutive allocation: `x_pres=1, x_next=2, y_pres=3, y_next=4, ...`
- Efficient quantification: We know exactly which variables to eliminate
- Clean separation: Present and next-state variables never interfere

== Image Computation Implementation

The image operation $"Img"(S, T)$ is implemented as:

```rust
fn image(&self, from: Ref) -> Ref {
    // Step 1: Conjunction S(v) ∧ T(v,v')
    let conj = self.bdd.apply_and(from, self.transition);

    // Step 2: Eliminate present-state variables
    let mut result = conj;
    for var in &self.present_vars {
        result = self.exists(result, *var);
    }

    // Step 3: Rename next-state to present-state
    self.rename(result, &self.next_vars, &self.present_vars)
}
```

Where `exists` is implemented via Shannon expansion:

```rust
fn exists(&self, f: Ref, var: usize) -> Ref {
    // ∃v.f = f[v/0] ∨ f[v/1]
    let f0 = self.bdd.compose(f, var, self.bdd.zero);
    let f1 = self.bdd.compose(f, var, self.bdd.one);
    self.bdd.apply_or(f0, f1)
}
```

And `rename` uses variable substitution:

```rust
fn rename(&self, f: Ref, from_vars: &[usize], to_vars: &[usize]) -> Ref {
    let mut result = f;
    for (from_var, to_var) in from_vars.iter().zip(to_vars) {
        let to_bdd = self.bdd.mk_var(*to_var);
        result = self.bdd.compose(result, *from_var, to_bdd);
    }
    result
}
```

== Preimage Computation

Similarly, preimage $"Pre"(S, T)$:

```rust
fn preimage(&self, to: Ref) -> Ref {
    // Step 1: Rename to(v) -> to(v')
    let to_next = self.rename(to, &self.present_vars, &self.next_vars);

    // Step 2: Conjunction T(v,v') ∧ to(v')
    let conj = self.bdd.apply_and(self.transition, to_next);

    // Step 3: Eliminate next-state variables
    let mut result = conj;
    for var in &self.next_vars {
        result = self.exists(result, *var);
    }

    result
}
```

== Reachability Analysis

Forward reachability computes all states reachable from initial states:

```rust
fn reachable(&self) -> Ref {
    let mut reached = self.initial;
    loop {
        let img = self.image(reached);
        let new_reached = self.bdd.apply_or(reached, img);

        // Check fixpoint
        if new_reached == reached {
            return reached;
        }

        reached = new_reached;
    }
}
```

The loop terminates because:
+ The state space $S$ is finite
+ Each iteration adds new states or stabilizes
+ Monotonicity: $R_i subset.eq R_(i+1)$

In practice, convergence is often fast (logarithmic in diameter of state graph).

== CTL Model Checking Implementation

The `CtlChecker` implements the recursive algorithm:

```rust
struct CtlChecker<'a> {
    ts: &'a TransitionSystem,
    cache: RefCell<HashMap<CtlFormula, Ref>>,
}

impl<'a> CtlChecker<'a> {
    fn check(&self, formula: &CtlFormula) -> Ref {
        // Check cache first
        if let Some(&cached) = self.cache.borrow().get(formula) {
            return cached;
        }

        let result = match formula {
            CtlFormula::Atom(label) => {
                self.ts.labels.get(label)
                    .copied()
                    .unwrap_or(self.ts.bdd.zero)
            }

            CtlFormula::Not(phi) => {
                let sat_phi = self.check(phi);
                self.ts.bdd.apply_not(sat_phi)
            }

            CtlFormula::And(phi, psi) => {
                let sat_phi = self.check(phi);
                let sat_psi = self.check(psi);
                self.ts.bdd.apply_and(sat_phi, sat_psi)
            }

            CtlFormula::EX(phi) => {
                let sat_phi = self.check(phi);
                self.ts.preimage(sat_phi)
            }

            CtlFormula::EF(phi) => {
                // μZ. φ ∨ EX Z
                let sat_phi = self.check(phi);
                let mut z = sat_phi;
                loop {
                    let ex_z = self.ts.preimage(z);
                    let z_new = self.ts.bdd.apply_or(sat_phi, ex_z);
                    if z_new == z {
                        break z;
                    }
                    z = z_new;
                }
            }

            CtlFormula::EG(phi) => {
                // νZ. φ ∧ EX Z
                let sat_phi = self.check(phi);
                let mut z = self.ts.bdd.one; // Start from all states
                loop {
                    let ex_z = self.ts.preimage(z);
                    let z_new = self.ts.bdd.apply_and(sat_phi, ex_z);
                    if z_new == z {
                        break z;
                    }
                    z = z_new;
                }
            }

            // AG, AF, AU, EU similar...
            _ => todo!()
        };

        self.cache.borrow_mut().insert(formula.clone(), result);
        result
    }

    fn holds_initially(&self, formula: &CtlFormula) -> bool {
        let sat = self.check(formula);
        // Check if initial ⊆ SAT(formula)
        let initial_and_not_sat = self.ts.bdd.apply_and(
            self.ts.initial,
            self.ts.bdd.apply_not(sat)
        );
        initial_and_not_sat == self.ts.bdd.zero
    }
}
```

Key implementation details:

+ *Caching*: Memoize results for subformulas to avoid recomputation
+ *Fixpoint iteration*: Loop until BDD pointer equality (constant time check)
+ *Symbolic throughout*: Never enumerate states explicitly

== Performance Considerations

=== BDD Variable Ordering

The BDD size is *highly sensitive* to variable ordering.
Consider $f(x_1, ..., x_n, y_1, ..., y_n) = (x_1 equiv y_1) and ... and (x_n equiv y_n)$:

- *Bad ordering* $(x_1, ..., x_n, y_1, ..., y_n)$: BDD has $2^n$ nodes
- *Good ordering* $(x_1, y_1, x_2, y_2, ..., x_n, y_n)$: BDD has $O(n)$ nodes

For model checking:
- *Interleave* present and next-state variables: $x_"pres", x_"next", y_"pres", y_"next", ...$
- This minimizes BDD size for typical transition relations

=== When BDDs Work Well

BDDs excel for:
- *Regular structures*: Counters, protocols, state machines
- *Local transitions*: Changes affect few variables
- *Invariants*: Properties with high symmetry

Real-world successes:
- Hardware verification: 10^120+ states verified
- Protocol verification: 10^20 states is routine
- Cache coherence protocols

=== When BDDs Struggle

BDDs can blow up for:
- *Multiplication*: BDD for integer multiplication has exponential size
- *Irregular patterns*: Random logic, hash functions
- *Poor variable ordering*: Can cause exponential blowup

Mitigation strategies:
- *Abstraction*: Simplify model while preserving properties
- *Compositional verification*: Verify components separately
- *SAT-based methods*: Alternative to BDDs for some problems

== Memory Management

BDDs use *hash consing* to share nodes:

```rust
struct BddTable {
    // Hash table: (var, low, high) -> node_id
    unique_table: HashMap<(usize, Ref, Ref), Ref>,
    nodes: Vec<BddNode>,
}

impl BddTable {
    fn mk_node(&mut self, var: usize, low: Ref, high: Ref) -> Ref {
        // Reduction rule: skip redundant tests
        if low == high {
            return low;
        }

        // Hash cons: check if node already exists
        let key = (var, low, high);
        if let Some(&existing) = self.unique_table.get(&key) {
            return existing;
        }

        // Create new node
        let id = self.nodes.len();
        self.nodes.push(BddNode { var, low, high });
        self.unique_table.insert(key, id);
        id
    }
}
```

This ensures:
- *Sharing*: Identical subgraphs stored once
- *Canonicity*: Same function → same representation
- *Efficiency*: BDD operations are polynomial in BDD size (not function size)

= Conclusion

Symbolic model checking using BDDs represents one of the great success stories in formal methods and automated verification.

== Key Takeaways

*Symbolic representation*: By encoding sets of states as Boolean formulas (BDDs) rather than enumerating them explicitly, we can handle systems with $10^20$ or more states --- far beyond what explicit-state methods can manage.

*Image and preimage operations*: These fundamental operations --- computing successors and predecessors symbolically --- are the building blocks for all reachability analysis and temporal logic model checking.

*Fixpoint computation*: CTL operators are computed iteratively until stabilization, leveraging the finite state space to guarantee termination and the canonical BDD representation for efficient fixpoint detection.

*Practical impact*: BDD-based model checking has been successfully applied to verify:
- Hardware designs (microprocessors with billions of states)
- Communication protocols (cache coherence, mutual exclusion)
- Control systems (aerospace, automotive, medical devices)
- Software abstractions (concurrent programs, distributed algorithms)

== The Power of BDDs

BDDs achieve dramatic compression through two mechanisms:

+ *Sharing*: Common subformulas are represented once and shared throughout the graph
+ *Reduction*: Redundant decision nodes are eliminated, producing minimal representations

When these mechanisms align with problem structure (regular patterns, local transitions, good variable ordering), BDDs can represent exponentially large sets with polynomial-sized graphs.

== Limitations and Extensions

While BDDs are remarkably powerful, understanding their limitations is crucial for effective application.

=== When BDDs Excel

BDDs achieve dramatic compression for systems with:

*Regular structure*:
- Counters, shift registers, state machines
- Control logic with regular patterns
- Protocols with symmetric processes

*Locality*:
- Transitions affect few variables at a time
- Sparse dependency graphs
- Local updates dominate global changes

*Good variable ordering*:
- Related variables placed nearby
- Interleaved present/next-state variables
- Natural ordering from system structure

*Characteristic examples*:
- Cache coherence protocols: 10²⁰+ states routinely verified
- Communication protocols: Sliding window, alternating bit
- Hardware control units: Instruction decoders, FSMs

=== When BDDs Struggle

BDDs can suffer exponential blowups for:

*Arithmetic operations*:
- Integer multiplication: BDD size grows exponentially in bit-width
- Division, modulo operations
- General arithmetic circuits

#note[
  *Why multiplication is hard:* The function $z = x times y$ (for $n$-bit numbers) requires BDD with $Theta(2^n)$ nodes for most variable orderings.
  This is because multiplication creates intricate dependencies between all input bits --- no local structure to exploit.
]

*Irregular patterns*:
- Random logic (no exploitable structure)
- Hash functions (designed to destroy regularity)
- Cryptographic operations (intentionally complex)

*Poor variable ordering*:
- Suboptimal ordering can cause exponential blowup
- Finding optimal ordering is NP-complete
- Heuristics work well for structured designs but fail on random logic

*Example: Variable ordering sensitivity*

Consider $f(x_1, y_1, ..., x_n, y_n) = (x_1 equiv y_1) and ... and (x_n equiv y_n)$:

/ Bad ordering $(x_1, ..., x_n, y_1, ..., y_n)$: BDD has $Theta(2^n)$ nodes
/ Good ordering $(x_1, y_1, ..., x_2, y_2, ..., x_n, y_n)$: BDD has $O(n)$ nodes

This exponential difference highlights the critical importance of variable ordering.

=== Complementary Techniques

Modern verification employs a diverse toolkit, using each method where it excels:

*SAT-based methods*:

_Strengths_:
- Excellent for datapaths, arithmetic, irregular logic
- Modern SAT solvers (CDCL) handle millions of variables
- Conflict-driven learning exploits problem structure dynamically

_Weaknesses_:
- No canonical representation (equality checking expensive)
- Less efficient for highly regular control logic
- Requires unrolling or abstraction

*Bounded Model Checking (BMC)*:
- Check properties up to depth $k$ by unrolling transition relation
- Encode as SAT/SMT problem: $I(s_0) and T(s_0, s_1) and ... and T(s_(k-1), s_k) and not P(s_0, ..., s_k)$
- Excellent for bug-finding (many bugs found at small depths)
- Incomplete: May miss bugs beyond bound $k$

*IC3/PDR (Property Directed Reachability)*:
- Incrementally constructs inductive invariants
- Avoids explicit BDD representation or BMC unrolling
- Represents states using CNF clauses
- Highly effective for safety properties on hardware
- Now dominates industrial hardware verification

*Abstraction-Refinement (CEGAR)*:
- Start with coarse abstraction (fewer variables)
- Model check abstraction
- If spurious counterexample, refine and retry
- Iterates until real counterexample or proof found
- Enables verification of infinite-state systems

*Hybrid approaches*:
- Use BDDs for control, SAT for datapaths
- Combine symbolic and explicit-state methods
- Portfolio solvers: Run multiple techniques in parallel

=== Choosing the Right Tool

*Use BDDs when*:
- System has regular structure (protocols, control logic)
- Properties involve reachability, CTL model checking
- Need canonical representation for equivalence checking
- Transitions are local and symbolic operations efficient

*Use SAT/BMC when*:
- System has irregular structure or arithmetic
- Bug-finding is primary goal (completeness not required)
- Need to handle large bit-vectors or complex datapaths
- Bounded analysis sufficient

*Use IC3/PDR when*:
- Verifying safety properties on hardware
- Need complete verification without fixed bounds
- BDD variable ordering problematic
- Modern industrial tools available

*Use abstraction when*:
- System too large for direct verification
- Can identify relevant variables automatically
- Iterative refinement feasible

#note[
  In practice, modern verification tools often combine multiple techniques, leveraging the strengths of each.
  The choice depends on the system structure, property type, and available computational resources.
]

== Historical Context

The development of symbolic model checking represents one of the most significant breakthroughs in formal verification, transforming it from a theoretical curiosity into an indispensable industrial practice.

=== The Early Days (1980s)

*Temporal logic model checking* was independently introduced by Edmund M. Clarke and E. Allen Emerson (1981) and by Jean-Pierre Queille and Joseph Sifakis (1982).
The initial approaches used _explicit-state_ representations, enumerating and storing each state individually.

Early achievements:
- Clarke & Emerson: Model checking for CTL on finite Kripke structures
- Queille & Sifakis: Path quantifiers and branching-time logic
- Practical limit: ~10⁴-10⁵ states (enough for small protocols)

The state explosion problem was immediately recognized as the fundamental challenge.
Even simple systems like communication protocols with a dozen processes would exceed the capacity of explicit-state methods.

=== The BDD Revolution (1986-1990)

*Randal E. Bryant's 1986 paper* "Graph-Based Algorithms for Boolean Function Manipulation" introduced _Binary Decision Diagrams_ as an efficient data structure for representing and manipulating Boolean functions.
Bryant showed that with:
- Fixed variable ordering
- Reduction rules (merge isomorphic subtrees, eliminate redundant tests)

Every Boolean function has a _canonical_ representation, enabling constant-time equality checking.

This seemingly theoretical result had profound practical implications.

=== Symbolic Model Checking is Born (1990-1993)

The breakthrough came when researchers realized BDDs could represent _sets of states symbolically_:

*Key insight*: Instead of storing states ${s_1, s_2, ..., s_n}$ explicitly, represent them as a Boolean formula $phi(v_1, ..., v_k)$ encoded as a BDD.

*1990: Burch, Clarke, McMillan, Dill, Hwang*
- "Symbolic Model Checking: 10²⁰ States and Beyond" (LICS 1990)
- First symbolic model checker using BDDs
- Verified hardware circuits with astronomically large state spaces
- Demonstrated: Systems previously intractable now verifiable in minutes

*1992-1993: Ken McMillan's SMV*
- Symbolic Model Verifier (SMV) tool released
- First industrial-strength symbolic model checker
- Book: _Symbolic Model Checking_ (1993) --- foundational text
- Successfully verified real Intel and Motorola designs

*Impact*: The "10²⁰ states" milestone shattered previous limits.
Explicit-state methods topped out at ~10⁷ states; symbolic methods routinely handled 10²⁰-10³⁰ states or more.

=== Industrial Adoption (1990s-2000s)

Symbolic model checking rapidly transitioned from academia to industry:

*Hardware verification*:
- Intel: Verified floating-point units, cache coherence protocols
- IBM: Processor verification (PowerPC, POWER series)
- AMD, Motorola, ARM: Design verification workflows
- Industry standard: Every major hardware company adopted BDD-based tools

*Tool ecosystem*:
- SMV (McMillan, 1992): First widely-used symbolic model checker
- VIS (UC Berkeley, 1996): Verification Interacting with Synthesis
- NuSMV (FBK-IRST, 2000): Open-source rewrite of SMV
- Cadence SMV: Commercial tool for hardware verification

*Success stories*:
- Verified cache coherence protocols with 10²⁰+ states
- Found subtle bugs in processor designs before fabrication
- Reduced verification time from weeks to hours

=== Limitations and Extensions (2000s)

As symbolic model checking matured, practitioners identified limitations:

*BDD limitations*:
- Sensitive to variable ordering (finding optimal ordering is NP-complete)
- Struggle with arithmetic operations (multiplication, division)
- Memory consumption can explode for irregular structures

*Response: Complementary techniques*:

*Bounded Model Checking (BMC)* (Biere et al., 1999):
- Unroll transition relation to fixed depth $k$
- Encode as SAT problem, solve with modern SAT solvers
- Excels where BDDs struggle: datapaths, arithmetic, irregular logic
- Trade-off: Only checks bounded depths (not complete), but very effective for bug-finding

*SAT-based model checking*:
- Leverages advances in SAT solving (CDCL, DPLL, learned clauses)
- Complementary to BDDs: strong on different problem classes
- Modern tools use hybrid approaches

*IC3/PDR* (Bradley, 2011):
- Incremental Construction of Inductive Clauses for Indubitable Correctness
- Computes inductive invariants without BDDs or BMC unrolling
- Represents major algorithmic breakthrough
- Dominates modern hardware verification (especially safety properties)

*Abstraction-refinement*:
- Start with coarse abstraction, refine on counterexamples (CEGAR)
- Enables verification of infinite-state systems (software, hybrid systems)
- Combines symbolic and abstract interpretation techniques

=== Modern Applications (2010s-Present)

Symbolic model checking has expanded far beyond its hardware origins:

*Software verification*:
- _Bounded model checkers_: CBMC (C programs), SMACK, ESBMC
- _Abstract interpretation_: Combine with BDDs for scalability
- _Concurrency bugs_: Data races, atomicity violations, deadlocks

*Cyber-physical systems*:
- Autonomous vehicles: Verify control algorithms, sensor fusion
- Medical devices: FDA-accepted verification for life-critical systems
- Aerospace: Flight control systems, avionics

*Security verification*:
- Protocol verification: TLS/SSL, cryptographic protocols
- Side-channel analysis: Verify absence of timing leaks
- Smart contract verification: Ethereum, blockchain systems

*AI/ML verification*:
- Neural network verification: Prove robustness properties
- Reinforcement learning: Verify learned policies
- Autonomous systems: Certified AI for safety-critical domains

*Emerging applications*:
- Quantum circuit verification: BDD-like structures for quantum states
- Biological systems: Verify gene regulatory networks, metabolic pathways
- Financial systems: High-frequency trading algorithms, settlement protocols

=== Impact on Computer Science

Symbolic model checking has influenced multiple areas:

*Formal methods*:
- Established automated verification as practical
- Inspired SAT/SMT solver development
- Foundation for modern program analysis

*Hardware industry*:
- Changed design methodology: "formal verification first"
- Reduced costly post-fabrication bugs
- Standard part of chip design flow

*Software engineering*:
- Static analysis tools based on symbolic techniques
- Model-based testing and test generation
- Concurrency bug detection

*Education*:
- Core topic in formal methods courses
- Widely taught in CS curricula
- Accessible through open-source tools (NuSMV, CBMC)

=== Awards and Recognition

The impact of symbolic model checking has been widely recognized:

*Turing Award (2007)*: Clarke, Emerson, and Sifakis
- "For their role in developing model checking into a highly effective verification technology"
- Turing Award citation emphasizes practical impact on hardware and software

*CAV Award* (Computer-Aided Verification conference):
- Multiple awards to BDD pioneers (Bryant, McMillan, et al.)
- Recognized both theoretical foundations and practical tools

*Industrial impact*:
- Prevented countless hardware bugs worth billions of dollars
- Reduced time-to-market for complex chips
- Enabled verification of systems otherwise unverifiable

== Further Reading

*Foundational papers*:
- Bryant, R. E. (1986). "Graph-based algorithms for boolean function manipulation." _IEEE Trans. on Computers_, 35(8).
- Burch, J. R. et al. (1990). "Symbolic model checking: $10^20$ states and beyond." _LICS_.
- McMillan, K. L. (1993). _Symbolic Model Checking_. Kluwer Academic Publishers.

*Textbooks*:
- Clarke, E. M., Grumberg, O., & Peled, D. A. (1999). _Model Checking_. MIT Press.
- Baier, C. & Katoen, J. (2008). _Principles of Model Checking_. MIT Press.
- Huth, M. & Ryan, M. (2004). _Logic in Computer Science: Modelling and Reasoning about Systems_. Cambridge.

*CTL and temporal logic*:
- Emerson, E. A. (1990). "Temporal and modal logic." _Handbook of Theoretical Computer Science_.
- Clarke, E. M. & Emerson, E. A. (1981). "Design and synthesis of synchronization skeletons using branching time temporal logic." _LICS_.

*Advanced topics*:
- Symbolic abstraction and refinement
- Compositional verification techniques
- Counterexample-guided abstraction refinement (CEGAR)
- SAT-based model checking and bounded model checking
- Automata-theoretic model checking for LTL

== Final Thoughts

Symbolic model checking demonstrates how the right abstractions and data structures can transform intractable problems into practical solutions.
By moving from explicit enumeration to symbolic representation, we gain not just quantitative improvements (bigger state spaces) but qualitative ones: entirely new classes of systems become verifiable.

The techniques described in this document --- BDDs, image/preimage operations, fixpoint computation, CTL model checking --- form the foundation for modern formal verification.
Understanding these concepts provides a solid basis for exploring advanced topics and applying verification to real-world systems.

The ultimate goal of formal verification is not merely to find bugs (though that's valuable!) but to provide *guarantees* about system behavior.
Symbolic model checking brings us closer to that goal, enabling us to reason about all possible executions of a system exhaustively and automatically.

As systems grow more complex and critical—autonomous vehicles, medical devices, financial infrastructure, AI systems—the need for rigorous verification only increases.
The techniques presented here will remain central to ensuring correctness, safety, and reliability in the systems we depend on.

#align(center)[
  #text(size: 10pt, style: "italic")[
    _End of Document_
  ]
]
