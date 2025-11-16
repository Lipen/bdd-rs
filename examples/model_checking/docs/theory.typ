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

#let rel(x) = math.class("relation", x)
#let nrel(x) = rel(math.cancel(x))

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
      content("s0", align(center)[*s₀* \ $x=0$])

      circle((4, 0), radius: 0.8, stroke: 2pt, fill: rgb("#ffffcc"), name: "s1")
      content("s1", align(center)[*s₁* \ $x=1$ \ {"on"}])

      line((-1.5, 0), "s0.west", mark: (end: ">"), stroke: 1pt)
      content((-1.5, 0), [start], anchor: "east", padding: 0.2)

      bezier("s0.east", "s1.west", (1.5, 0.6), (2.5, 0.6), mark: (end: ">", fill: black), stroke: 1pt)
      content((2, 0.8), [toggle])

      bezier("s1.west", "s0.east", (2.5, -0.6), (1.5, -0.6), mark: (end: ">", fill: black), stroke: 1pt)
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
  - $(0,0) -> (1,0)$ (0 $=>$ 1)
  - $(1,0) -> (0,1)$ (1 $=>$ 2)
  - $(0,1) -> (1,1)$ (2 $=>$ 3)
  - $(1,1) -> (0,0)$ (3 $=>$ 0)

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
      content("s1", align(center)[*s₁* \ $(1,0)$ \ val=1])

      circle((3, -3), ..node-style, name: "s2")
      content("s2", align(center)[*s₂* \ $(0,1)$ \ val=2])

      circle((3, 0), ..node-style, name: "s3")
      content("s3", align(center)[*s₃* \ $(1,1)$ \ val=3])

      line((-1.5, 0), "s0.west", mark: (end: ">"), stroke: 1pt)
      content((-1.5, 0), [start], anchor: "east", padding: 0.2)

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

== Preimage: Backward Reachability

The *preimage* (or *predecessor*) operation computes states that can reach a given set in one step.
This is the dual of the image operation, working backwards through the transition relation.

#definition(name: "Preimage Operation")[
  Given a set of states $S$ and transition relation $T$, the *preimage* of $S$ under $T$ is:

  $ "Pre"(S, T) = {s | exists s' : (s, s') in T and s' in S} $

  In logical notation:
  $ "Pre"(S, T) = exists v'_1, ..., v'_n . T(v_1, ..., v_n, v'_1, ..., v'_n) and S(v'_1, ..., v'_n) $
]

Intuitively, preimage answers: "From which states can I reach $S$ in one step?"

=== Computing the Preimage

The preimage computation has three steps (compare with image):

+ *Variable renaming*: Rename present-state variables to next-state in $S(v) arrow S(v')$
+ *Conjunction*: $S(v') and T(v, v')$ --- combine target states with transition relation
+ *Existential quantification*: $exists v' . (S(v') and T(v, v'))$ --- eliminate next-state variables

#example(name: "Preimage of Toggle System")[
  Recall the toggle system with $T(x, x') = x xor x'$.

  *Question*: From which states can we reach $s_1$ (where $x=1$)?

  Let $S = {s_1} = {x = 1}$, represented by formula $x$.

  *Step 1: Rename* $S(x) arrow S(x')$

  $ S(x') = x' $

  *Step 2: Conjunction*

  $
    S(x') and T(x, x') & = x' and (x xor x') \
                       & = x' and ((x and overline(x')) or (overline(x) and x')) \
                       & = x' and (overline(x) and x') quad "(since" x' "is true, first term vanishes)" \
                       & = overline(x) and x'
  $

  *Step 3: Existential Quantification*

  $ exists x' . (overline(x) and x') = overline(x) $

  We eliminate $x'$ by computing:
  $ (overline(x) and x')[x' arrow 0] or (overline(x) and x')[x' arrow 1] = 0 or overline(x) = overline(x) $

  *Conclusion*: From state $s_0$ (where $x=0$), we can reach state $s_1$ in one step. ✓
]

#example(name: "Preimage in Two-Bit Counter")[
  For the counter, find predecessors of state $(1,1)$.

  Target set: $S = {(1,1)}$, represented by $x and y$.

  Transition: $y' = not y$, $x' = x xor y$

  After renaming $S$: $x' and y'$

  Transition relation:
  $ T(x, y, x', y') = (y' equiv not y) and (x' equiv x xor y) $

  Conjunction:
  $ x' and y' and (y' equiv not y) and (x' equiv x xor y) $

  From $y' = 1$ and $y' equiv not y$, we get $y = 0$.
  From $x' = 1$ and $x' equiv x xor y$, we get $x xor y = 1$.
  With $y = 0$: $x xor 0 = 1$, so $x = 1$.

  After eliminating $x', y'$: result is $(x and not y)$, representing state $(1,0)$.

  *Conclusion*: State $(1,0)$ can reach $(1,1)$ in one step. ✓
]

=== Backward Reachability Analysis

Just as image enables forward reachability, preimage enables *backward reachability*:

#theorem(name: "Backward Reachable States")[
  The set of states that can reach a target set $T$ is:

  $ R^*_"back"(T) = mu Z . T or "Pre"(Z, T_"rel") $

  Algorithmically:
  ```
  R := T (target states)
  loop:
    R_new := R ∪ Pre(R, T_rel)
    if R_new = R: break
    R := R_new
  return R
  ```
]

This is useful for:
- *Safety checking*: Can initial states reach bad states? $I inter R^*_"back"("Bad") eq.not emptyset$?
- *Invariant checking*: Working backwards from violations
- *Goal-directed search*: Start from targets, work backwards

#note[
  *Forward vs Backward*:
  - Forward reachability: $R^* = mu Z . I or "Img"(Z)$ --- starts from initial states
  - Backward reachability: $R^*_"back" = mu Z . T or "Pre"(Z)$ --- starts from target states

  Choose based on problem:
  - Use forward if initial states are small/simple
  - Use backward if target states are small/simple
  - Sometimes one direction has much smaller BDDs!
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

  - $mu Z . phi or op("EX") Z$: Start with $phi$, expand to states reaching $phi$
  - $nu Z . phi and op("AX") Z$: Start with all states, keep only those satisfying $phi$ with all successors good
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
        & | op("EX") phi | op("AX") phi | op("EF") phi | op("AF") phi | op("EG") phi | op("AG") phi \
        & | op("E")[phi rel("U") psi] | op("A")[phi rel("U") psi]
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
    M, s models op("EX") phi & <==> exists s' : (s, s') in T and M, s' models phi \
    M, s models op("AX") phi & <==> forall s' : (s, s') in T => M, s' models phi \
    M, s models op("EF") phi & <==> exists pi = s_0, s_1, ... : s_0 = s and exists i >= 0 : M, s_i models phi \
    M, s models op("AF") phi & <==> forall pi = s_0, s_1, ... : s_0 = s => exists i >= 0 : M, s_i models phi
  $
]

== Properties: Safety and Liveness

CTL formulas typically express either _safety_ or _liveness_ properties --- the two fundamental classes of system requirements.

#definition(name: "Safety Property")[
  A *safety property* asserts that "something bad never happens":

  $ op("AG") (not "bad") $

  This means: on all paths, globally (always), the bad condition does not hold.
  Safety properties express _invariants_ --- conditions that must hold in every reachable state.
]

#example(name: "Safety Properties")[
  / Mutual exclusion: $op("AG") (not ("critical"_1 and "critical"_2))$ \
    "Two processes are never simultaneously in the critical section"

  / No buffer overflow: $op("AG") ("count" <= "capacity")$ \
    "The buffer count never exceeds capacity"

  / No division by zero: $op("AG") ("divisor" != 0)$ \
    "The divisor is always non-zero"

  / Type safety: $op("AG") (not "type-error")$ \
    "No type errors occur during execution"

  / Memory safety: $op("AG") ("allocated" => not "freed")$ \
    "Accessing only allocated memory"
]

#definition(name: "Liveness Property")[
  A *liveness property* asserts that "something good eventually happens":

  $ op("AF") ("good") $

  This means: on all paths, eventually (in the future), the good condition holds.
  Liveness properties ensure _progress_ --- the system doesn't get stuck but eventually achieves desired outcomes.
]

#example(name: "Liveness Properties")[
  / Termination: $op("AF") ("terminated")$ \
    "The process eventually terminates"

  / Request-response: $op("AG") ("request" => op("AF") "response")$ \
    "Every request is eventually responded to"

  / Fair scheduling: $op("AG") ("waiting" => op("AF") "granted")$ \
    "Every waiting process is eventually granted access"

  / Deadlock freedom: $op("AG") ("EF" "enabled")$ \
    "From every state, some action is eventually enabled"

  / Message delivery: $op("AG") ("sent" => op("AF") "received")$ \
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
    [*Safety*: Never both green], [$op("AG") (not ("ns"_"green" and "ew"_"green"))$],
    [*Safety*: Red before green], [$op("AG") ("ns"_"red" => op("AX") (not "ns"_"green"))$],
    [*Liveness*: Eventually green], [$op("AG") ("ns"_"red" => op("AF") "ns"_"green")$],
    [*Liveness*: Cycles through states], [$op("AG") (op("EF") "ns"_"green" and op("EF") "ew"_"green")$],
    [*Fairness*: Both get green], [$op("AG") (op("AF") "ns"_"green") and op("AG") (op("AF") "ew"_"green")$],
  )

  Let's verify the first property in detail: *Never both green simultaneously*.

  *Step 1: Encode bad states*

  $ "bad" = "ns"_"green" and "ew"_"green" $

  *Step 2: Compute* $op("AG") (not "bad")$ *via greatest fixpoint*

  Recall: $op("AG") phi = nu Z . phi and op("AX") Z$

  $
    Z_0 & = S quad "(all states)" \
    Z_1 & = (not "bad") and op("AX") Z_0 \
        & = (not "bad") and S = (not "bad") \
        & = "states where not both green" \
    Z_2 & = (not "bad") and op("AX") Z_1 \
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

  $ op("AG") ("request" => op("AF") "response") $

  Reading: "Always, if there's a request, then on all future paths, eventually there's a response."

  Let's compute this step by step.

  *Subformula 1:* $op("AF") "response"$ --- states from which response is inevitable

  Using $op("AF") phi = mu Z . phi or op("AX") Z$:  $ Z_0 & = emptyset \
  Z_1 & = "response" or op("AX") Z_0 = "response" \
  Z_2 & = "response" or op("AX") Z_1 \
      & = "response" or "Pre"("response") \
      & = "states where response holds or is reachable in 1 step" \
  Z_3 & = "response" or op("AX") Z_2 \
      & = "states reaching response in" <= 2 "steps" \
      & dots.v $

  Converges to $R = "states from which response is inevitable"$.

  *Subformula 2:* $"request" => op("AF") "response"$ --- equivalent to $not "request" or op("AF") "response"$

  $ phi_"rr" = (not "request") or R $

  *Main formula:* $op("AG") phi_"rr"$ --- always holds

  Using $op("AG") phi = nu Z . phi and op("AX") Z$:

  $
    W_0 & = S \
    W_1 & = phi_"rr" and op("AX") W_0 = phi_"rr" \
    W_2 & = phi_"rr" and op("AX") W_1 \
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
                  op("EF") phi & = mu Z . phi or op("EX") Z \
                  op("AF") phi & = mu Z . phi or op("AX") Z \
                  op("EG") phi & = nu Z . phi and op("EX") Z \
                  op("AG") phi & = nu Z . phi and op("AX") Z \
    op("E") [phi rel("U") psi] & = mu Z . psi or (phi and op("EX") Z) \
    op("A") [phi rel("U") psi] & = mu Z . psi or (phi and op("AX") Z)
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
  Consider checking $op("EF") ("x" = 1)$ on the two-bit counter starting from $(0,0)$.

  Let $phi = (x = 1) = {(1,0), (1,1)}$ (states where $x = 1$).

  $
    Z_0 & = emptyset \
    Z_1 & = phi or op("EX") Z_0 = {(1,0), (1,1)} or emptyset = {(1,0), (1,1)} \
    Z_2 & = phi or op("EX") Z_1 = {(1,0), (1,1)} or "Pre"({(1,0), (1,1)}) \
        & = {(1,0), (1,1)} or {(0,0), (0,1)} = {(0,0), (1,0), (0,1), (1,1)} \
    Z_3 & = phi or op("EX") Z_2 = {(1,0), (1,1)} or "Pre"({(0,0), (1,0), (0,1), (1,1)}) \
        & = {(0,0), (1,0), (0,1), (1,1)} = Z_2
  $

  Fixpoint!
  All states satisfy $op("EF") ("x" = 1)$, meaning $x = 1$ is reachable from all states.
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
  Check $op("AG") ("x" = 0)$ on the two-bit counter.

  Let $phi = (x = 0) = {(0,0), (0,1)}$.

  $
    Z_0 & = S = {(0,0), (1,0), (0,1), (1,1)} \
    Z_1 & = phi and op("AX") Z_0 = {(0,0), (0,1)} and S = {(0,0), (0,1)} \
    Z_2 & = phi and op("AX") Z_1 = {(0,0), (0,1)} and op("AX") ({(0,0), (0,1)}) \
        & = {(0,0), (0,1)} and emptyset = emptyset
  $

  Why?
  Because $(0,0)$ transitions to $(1,0) in.not {(0,0), (0,1)}$.

  Result: $emptyset$ means no state satisfies $op("AG") ("x" = 0)$.
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
  $ "SAT"(op("EX") phi) = "Pre"("SAT"(phi), T) $

/ AX operator:
  $ "SAT"(op("AX") phi) = overline("SAT"(op("EX") (not phi))) $

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

  *Property*: $op("AG") (not ("critical"_1 and "critical"_2))$

  *Steps*:
  1. Encode system as BDD transition relation
  2. Compute $"SAT"("critical"_1 and "critical"_2)$ = bad states
  3. Compute $"SAT"(op("AG") (not "bad"))$ via greatest fixpoint
  4. Check if initial state $in "SAT"(op("AG") (not "bad"))$

  If yes: property holds ✓ \
  If no: counterexample exists (extract witness path)
]

== Counterexample Generation

When a property fails, the model checker should produce a *counterexample* --- a concrete execution trace demonstrating the violation.
This is one of model checking's most valuable features: not just "property fails," but "here's exactly how it fails."

=== What is a Counterexample?

#definition(name: "Counterexample")[
  For a property $phi$ that fails from initial state $s_0$:
  - A *counterexample* is a path $pi = s_0 arrow s_1 arrow s_2 arrow ... arrow s_k$ where $s_k models not phi$
  - For liveness properties (e.g., $op("AG") op("EF") p$), may need an infinite path (lasso-shaped)
]

=== Extracting Counterexamples

During fixpoint computation, we can record *predecessor information* to reconstruct paths.

*Algorithm for Safety Property* $op("AG") phi$:

```
check_AG(phi):
  // Compute greatest fixpoint with predecessor tracking
  Z := S
  pred := empty_map()  // maps state to predecessor

  loop:
    Z_old := Z
    Z := SAT(phi) ∩ AX(Z)

    // Record predecessors for states leaving Z
    for each state s in Z_old \ Z:
      for each s' such that (s, s') in T and s' ∉ Z:
        pred[s'] := s  // s can reach bad state s'

    if Z = Z_old: break

  // Check if property holds
  if initial ⊆ Z:
    return "Property holds"
  else:
    // Extract counterexample
    return extract_path(initial, pred)

extract_path(s, pred):
  path := [s]
  while s in pred:
    s := pred[s]
    path.append(s)
  return path
```

#example(name: "Counterexample for Mutual Exclusion")[
  Property: $op("AG") (not ("crit"_1 and "crit"_2))$ (never both in critical section)

  If property fails, counterexample might be:
  ```
  s₀: (idle₁, idle₂)       // both idle
    ↓
  s₁: (trying₁, idle₂)      // P1 tries
    ↓
  s₂: (trying₁, trying₂)    // P2 tries
    ↓
  s₃: (crit₁, trying₂)      // P1 enters
    ↓
  s₄: (crit₁, crit₂)        // P2 enters - VIOLATION!
  ```

  This shows exactly how the mutual exclusion property was violated.
]

=== Liveness Counterexamples

For liveness properties (e.g., $op("AG") op("EF") p$), counterexamples are *lasso-shaped*:
- A *stem*: path from initial state to a cycle
- A *loop*: cycle that never satisfies the property

#example(name: "Liveness Counterexample")[
  Property: $op("AG") op("EF") "request" => op("AF") "grant"$ (every request eventually granted)

  Counterexample:
  ```
         s₀ (no request)
          ↓
  Stem:  s₁ (request sent)
          ↓
         s₂ (waiting)
          ↓
  Loop:  s₃ (still waiting) → s₄ (busy) → s₃  ↺
  ```

  The loop $s_3 arrow s_4 arrow s_3$ repeats forever without granting the request.
]

=== Symbolic Counterexample Extraction

In symbolic model checking, we work with BDDs (sets of states), not individual states.

*Challenge*: How to extract a single path from a BDD representing many states?

*Solution*: Pick arbitrary representatives at each step:

```
extract_symbolic_path(bad_states, pred_map):
  // Start with any bad state
  current := pick_any_state(bad_states ∩ initial)
  path := [current]

  while current not in initial_states:
    // Find predecessors of current
    preds := pred_map[current] ∩ reachable

    // Pick any predecessor
    current := pick_any_state(preds)
    path.prepend(current)

  return path

pick_any_state(state_set_bdd):
  // Walk BDD, choosing any path to terminal 1
  // Construct concrete state assignment
  result := {}
  node := state_set_bdd

  while node is not terminal:
    var := node.variable
    // Choose either branch (prefer high for determinism)
    if node.high != 0:
      result[var] := 1
      node := node.high
    else:
      result[var] := 0
      node := node.low

  return result
```

=== Shortest Counterexample

For better debugging, prefer *shortest* counterexamples:

```
shortest_counterexample(initial, bad):
  // BFS-like approach
  reached := initial
  frontier := initial
  pred := {}
  depth := 0

  while frontier ≠ ∅:
    // Check if we reached bad states
    if frontier ∩ bad ≠ ∅:
      return extract_path(pick_any(frontier ∩ bad), pred)

    // Expand frontier
    new_states := Img(frontier) \ reached

    // Record predecessors
    for each s in new_states:
      pred[s] := frontier  // symbolic: BDD of possible preds

    reached := reached ∪ new_states
    frontier := new_states
    depth := depth + 1

  return "No counterexample exists"
```

#note[
  *Practical Considerations*:
  - Shortest counterexamples are easier to understand
  - But computing them requires additional BFS-like search
  - Trade-off: speed vs. counterexample quality
  - Some tools offer both options
]

== Fairness Constraints

Many systems require *fairness assumptions* --- constraints ensuring "infinitely often" behavior.
Without fairness, model checking can produce unrealistic counterexamples.

=== Why Fairness Matters

#example(name: "Unfair Scheduler")[
  System: Two processes competing for a resource

  Property: $op("AG") ("request"_1 => op("AF") "grant"_1)$ (every request eventually granted)

  *Without fairness*: Counterexample where process 2 is scheduled forever, process 1 never runs.
  This is technically valid but unrealistic --- real schedulers are fair.

  *With fairness*: "Process 1 is scheduled infinitely often"
  Now the counterexample disappears --- if P1 runs infinitely often, it will eventually be granted.
]

=== Types of Fairness

#definition(name: "Fairness Constraints")[

  - *Unconditional (Strong) Fairness*:
    $ op("GF") phi $ --- $phi$ holds infinitely often

  - *Conditional (Weak) Fairness*:
    $ op("FG") phi => op("GF") psi $ --- if $phi$ holds continuously from some point, then $psi$ holds infinitely often

    Equivalently: $op("GF") phi or op("FG") psi$
]

*Common Uses*:
- *Process fairness*: Every process runs infinitely often
- *Communication fairness*: Every enabled transition is eventually taken
- *Channel fairness*: Every message eventually delivered

=== Fair CTL (FCTL)

CTL extended with fairness:

#definition(name: "Fair Paths")[
  Given fairness constraint $F$ (typically conjunction of $op("GF") phi_i$):
  - A path is *fair* if it satisfies $F$
  - CTL operators quantify over fair paths only
]

*Fair CTL Semantics*:
- $op("EF")_F phi$: exists a *fair* path where $phi$ eventually holds
- $op("AG")_F phi$: on all *fair* paths, $phi$ always holds

=== Model Checking with Fairness

Fairness changes fixpoint computations:

#theorem(name: "Fair EF")[
  For fairness $F = op("GF") f_1 and ... and op("GF") f_n$:

  $ op("EF")_F phi = mu Z . phi or (op("EX") Z and op("EX") (op("EF")_F f_1) and ... and op("EX") (op("EF")_F f_n)) $
]

*Intuition*: To reach $phi$ fairly, each step must be on a path that visits each $f_i$ infinitely often.

#theorem(name: "Fair AG")[
  For fairness $F = op("GF") f_1 and ... and op("GF") f_n$:

  $ op("AG")_F phi = nu Z . phi and op("AX") (Z or not op("EF")_F "true") $
]

*Algorithm for Fair Reachability*:

```
fair_EF(phi, fairness_constraints):
  // Compute states from which all fairness constraints
  // can be satisfied infinitely often

  fair_states := S
  for each f in fairness_constraints:
    // States from which f is reachable infinitely often
    fair_inf := nu Z. f ∧ EX(Z) ∨ EX(EF(f))
    fair_states := fair_states ∩ fair_inf

  // Now compute EF over fair paths
  Z := phi
  loop:
    Z_new := Z ∪ (Pre(Z) ∩ fair_states)
    if Z_new = Z: break
    Z := Z_new

  return Z
```

#example(name: "Fair Mutual Exclusion")[
  System: Two processes with mutual exclusion protocol

  Fairness: $op("GF") "run"_1 and op("GF") "run"_2$ (both processes run infinitely often)

  Property: $op("AG") ("request"_1 => op("AF") "grant"_1)$

  *Without fairness*: Fails (P2 can run forever)
  *With fairness*: Holds (P1 must run infinitely often, so eventually gets grant)
]

#note[
  *Fairness Complexity*:
  - Fair CTL model checking is more expensive than standard CTL
  - Each fairness constraint adds nested fixpoint computations
  - But essential for realistic verification of concurrent systems
  - Most practical model checkers support fairness constraints
]

== Programming Example: Pseudocode for Model Checking

Let's see how model checking can be implemented using BDDs.
This pseudocode demonstrates building a transition system and verifying CTL properties.

#note[
  The `bdd-rs` library in this repository provides BDD data structures and operations.
  This example shows the conceptual structure; actual implementation would use the library's API.
]

```rust
use std::collections::HashMap;

/// A model checking framework using BDDs (pseudocode)
struct ModelChecker {
    // BDD manager for creating and manipulating BDDs
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

This example demonstrates the conceptual structure of model checking:
- Declaring state variables with present/next-state pairs
- Building transition relations symbolically
- Implementing image/preimage operations
- Computing fixpoints for temporal operators
- Verifying properties from initial states

#note[
  The `bdd-rs` library provides the core BDD data structure and operations needed to implement these algorithms.
  See the library documentation for the specific API.
]

= Linear Temporal Logic (LTL) and CTL Comparison

While this document focuses on CTL, it's important to understand how it relates to Linear Temporal Logic (LTL), another major temporal logic for verification.

== LTL: Path-Based Logic

LTL expresses properties of *individual paths* (linear sequences of states).

#definition(name: "LTL Syntax")[
  $ phi ::= p | not phi | phi_1 and phi_2 | op("X") phi | phi_1 rel("U") phi_2 $

  Where:
  - $p$: atomic proposition
  - $op("X") phi$: *next* --- $phi$ holds in next state
  - $phi_1 rel("U") phi_2$: *until* --- $phi_1$ holds until $phi_2$ holds

  Derived operators:
  - $op("F") phi equiv "true" rel("U") phi$ (eventually/finally)
  - $op("G") phi equiv not op("F") not phi$ (globally/always)
]

#definition(name: "LTL Semantics")[
  LTL formulas are evaluated on *infinite paths* $pi = s_0 arrow s_1 arrow s_2 arrow ...$

  - $pi models p$ iff $p in L(s_0)$
  - $pi models op("X") phi$ iff $pi^1 models phi$ (where $pi^i$ is path starting at $s_i$)
  - $pi models phi_1 rel("U") phi_2$ iff $exists i >= 0 . (pi^i models phi_2 and forall j < i . pi^j models phi_1)$
  - $pi models op("F") phi$ iff $exists i >= 0 . pi^i models phi$
  - $pi models op("G") phi$ iff $forall i >= 0 . pi^i models phi$
]

== CTL: State-Based Logic

CTL expresses properties about *sets of states* and quantifies over paths from each state.

*Key difference*: In CTL, path quantifiers (E, A) must be immediately followed by temporal operators (X, F, G, U).

== Expressiveness Comparison

*Neither logic subsumes the other* --- they are incomparable.

=== Properties CTL Can Express But LTL Cannot

#example(name: "Potential to Reach")[
  CTL: $op("AG") op("EF") "restart"$

  "From every reachable state, there *exists* a path to restart"

  This cannot be expressed in LTL because LTL quantifies over individual paths, not over existence of alternative paths from a state.
]

#example(name: "Inevitable on Some Branch")[
  CTL: $op("EF") op("AG") "stable"$

  "There exists a path leading to a state from which 'stable' holds on all continuations"

  LTL cannot express this alternation of quantifiers (E followed by A).
]

=== Properties LTL Can Express But CTL Cannot

#example(name: "Fairness")[
  LTL: $op("GF") "request" => op("GF") "grant"$

  "If request holds infinitely often, then grant holds infinitely often"

  This *infinitely often* property cannot be expressed in CTL.
  CTL's $op("AG") op("EF") "grant"$ is weaker --- it only says grant is *reachable* infinitely many times, not that it actually *occurs* infinitely often on the path.
]

#example(name: "Eventual Persistence")[
  LTL: $op("F") op("G") "stable"$

  "Eventually, stable holds forever"

  CTL's $op("AF") op("AG") "stable"$ is different --- it means "on all paths, eventually all continuations are stable," which is stronger (requires all paths to converge).
]

=== Properties Both Can Express

#example(name: "Common Ground")[
  - $op("AG") p equiv op("G") p$ (safety)
  - $op("AF") p equiv op("A") op("F") p$ (inevitability on all paths)
  - $op("EF") p$ has no LTL equivalent (but $op("F") p$ is weaker)
  - $op("EG") p$ has no LTL equivalent
]

== CTL\*: The Unified Logic

#definition(name: "CTL*")[
  CTL\* allows arbitrary mixing of path quantifiers and temporal operators.

  - CTL $subset.eq$ CTL\*
  - LTL $subset.eq$ CTL\*
  - CTL\* is strictly more expressive than both
]

*Example CTL\* property*: $op("A") (op("G") op("F") "request" => op("G") op("F") "grant")$

This combines CTL's universal path quantifier with LTL's fairness pattern.

== Model Checking Complexity

#table(
  columns: 3,
  align: (left, center, center),
  stroke: (x, y) => if y == 0 { (bottom: 0.8pt) },
  [*Logic*], [*Complexity*], [*Approach*],
  [CTL], [$O(|M| times |phi|)$], [Fixpoint computation],
  [LTL], [$O(|M| times 2^(|phi|))$], [Automata-theoretic],
  [CTL\*], [$O(|M| times 2^(|phi|))$], [Automata-theoretic],
)

*Key insights*:
- CTL is faster to check (linear in formula size)
- LTL requires translating formula to Büchi automaton (exponential)
- But LTL can express fairness directly

== When to Use Which Logic?

#table(
  columns: 2,
  align: (left, left),
  stroke: (x, y) => if y == 0 { (bottom: 0.8pt) },
  [*Use CTL when:*], [*Use LTL when:*],
  [• Checking branching properties], [• Checking linear properties],
  [• "Some path exists" reasoning], [• Fairness constraints],
  [• Speed is critical], [• Path-specific behavior],
  [• Bounded path quantification], [• "Infinitely often" patterns],
  [• Small formulas], [• Composition of properties],
)

#note[
  *Practical Consideration*:
  - Most industrial model checkers support both CTL and LTL
  - For LTL, they typically convert to CTL\* or use automata-theoretic methods
  - Choice often depends on property being verified rather than performance
  - Symbolic (BDD-based) methods work best for CTL
  - Explicit-state methods often preferred for LTL
]

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

== BDD Operations

BDDs support efficient operations for manipulating Boolean functions.
All operations maintain the canonical form through reduction and hash consing.

=== Apply Operation

The *apply* operation combines two BDDs using a Boolean operator ($and$, $or$, $xor$, etc.).

#definition(name: "Apply Operation")[
  Given BDDs $f$ and $g$ and binary operator $op in {and, or, xor, =>}$:

  $ "apply"(f, g, "op") = h "where" h(x_1, ..., x_n) = f(x_1, ..., x_n) space "op" space g(x_1, ..., x_n) $
]

*Algorithm* (recursive with memoization):

```
apply(f, g, op):
  // Base cases
  if f is terminal and g is terminal:
    return op(f, g)

  // Check cache
  if (f, g, op) in cache:
    return cache[(f, g, op)]

  // Recursive case: split on top variable
  let v = min(var(f), var(g))

  let f_low = (var(f) = v) ? low(f) : f
  let f_high = (var(f) = v) ? high(f) : f
  let g_low = (var(g) = v) ? low(g) : g
  let g_high = (var(g) = v) ? high(g) : g

  let h_low = apply(f_low, g_low, op)
  let h_high = apply(f_high, g_high, op)

  let result = make_node(v, h_low, h_high)
  cache[(f, g, op)] = result
  return result
```

#example(name: "Apply AND")[
  Computing $f and g$ where $f = x$ and $g = y$:

  - $f$ is the BDD with root $x$: low→0, high→1
  - $g$ is the BDD with root $y$: low→0, high→1

  Apply proceeds:
  - Top variable: $x$ (assuming $x < y$ in ordering)
  - Low branch: $"apply"(0, g, and) = 0$ (since $0 and "anything" = 0$)
  - High branch: $"apply"(1, g, and) = g$ (since $1 and g = g$)
  - Result: BDD with root $x$, low→0, high→$g$

  This represents $x and y$ ✓
]

*Complexity*: $O(|f| times |g|)$ in worst case, but caching makes it efficient in practice.

=== Restrict Operation

The *restrict* operation fixes the value of a variable.

#definition(name: "Restrict")[
  $ "restrict"(f, x_i, b) = f[x_i arrow b] $

  Returns a BDD representing $f$ with variable $x_i$ set to boolean value $b in {0,1}$.
]

*Algorithm*:
```
restrict(f, var, value):
  if f is terminal:
    return f

  if var(f) < var:  // haven't reached var yet
    return make_node(var(f),
      restrict(low(f), var, value),
      restrict(high(f), var, value))

  if var(f) = var:  // found the variable
    return value = 0 ? low(f) : high(f)

  // var(f) > var: variable doesn't appear
  return f
```

#example[
  Given $f = x and y$ (BDD: root $x$, low→0, high→(root $y$, low→0, high→1)):

  $"restrict"(f, x, 1)$ eliminates $x$ node, returns the high branch:
  - Result: BDD for $y$ (since $1 and y = y$)

  $"restrict"(f, x, 0)$ returns the low branch:
  - Result: terminal 0 (since $0 and y = 0$)
]

=== Existential Quantification

Eliminating a variable by quantifying it out:

#definition(name: "Existential Quantification")[
  $ exists x_i . f = f[x_i arrow 0] or f[x_i arrow 1] $

  The result is true if $f$ is true for *any* value of $x_i$.
]

*Algorithm*:
```
exists(f, var):
  f0 = restrict(f, var, 0)
  f1 = restrict(f, var, 1)
  return apply(f0, f1, OR)
```

#example[
  Given $f = x and y$:

  $exists x . (x and y)$:
  - $f[x arrow 0] = 0 and y = 0$
  - $f[x arrow 1] = 1 and y = y$
  - Result: $0 or y = y$

  This makes sense: "there exists an $x$ such that $x and y$" is equivalent to just $y$ (choosing $x=1$ works iff $y=1$).
]

*Universal quantification* is dual:
$ forall x_i . f = f[x_i arrow 0] and f[x_i arrow 1] $

=== Compose Operation

Substitute a variable with a function:

#definition(name: "Compose")[
  $ "compose"(f, x_i, g) = f[x_i arrow g] $

  Replace all occurrences of $x_i$ in $f$ with the function $g$.
]

This is crucial for variable renaming in model checking (e.g., $x' arrow x$).

*Algorithm*:
```
compose(f, var, g):
  if f is terminal:
    return f

  if var(f) < var:
    return make_node(var(f),
      compose(low(f), var, g),
      compose(high(f), var, g))

  if var(f) = var:
    // Replace this node: compute f[var←g]
    // This is: (¬g ∧ low(f)) ∨ (g ∧ high(f))
    return ite(g, high(f), low(f))

  // var(f) > var: doesn't depend on var
  return f
```

=== ITE (If-Then-Else) Operation

The fundamental BDD operation from which all others can be derived:

#definition(name: "ITE Operation")[
  $ "ite"(f, g, h) = (f and g) or (not f and h) $

  "If $f$ then $g$ else $h$"
]

#note[
  *Why ITE is universal:*
  - $not f = "ite"(f, 0, 1)$
  - $f and g = "ite"(f, g, 0)$
  - $f or g = "ite"(f, 1, g)$
  - $f xor g = "ite"(f, not g, g)$
]

*Algorithm* (similar to apply but with three arguments):
```
ite(f, g, h):
  // Terminal cases
  if f = 1: return g
  if f = 0: return h
  if g = h: return g
  if g = 1 and h = 0: return f

  // Check cache
  if (f, g, h) in cache:
    return cache[(f, g, h)]

  // Recursive case
  let v = min(var(f), var(g), var(h))

  let f_v = cofactor(f, v)
  let g_v = cofactor(g, v)
  let h_v = cofactor(h, v)

  let low = ite(f_v.low, g_v.low, h_v.low)
  let high = ite(f_v.high, g_v.high, h_v.high)

  let result = make_node(v, low, high)
  cache[(f, g, h)] = result
  return result
```

=== Operation Complexity Summary

#table(
  columns: 3,
  stroke: (x, y) => if y == 0 { (bottom: 0.8pt) },
  [*Operation*], [*Time Complexity*], [*Note*],
  [`apply(f, g, op)`], [$O(|f| times |g|)$], [With caching],
  [`restrict(f, x, b)`], [$O(|f|)$], [Single pass],
  [`exists(f, x)`], [$O(|f|^2)$], [Two restricts + OR],
  [`compose(f, x, g)`], [$O(|f| times |g|)$], [Like apply],
  [`ite(f, g, h)`], [$O(|f| times |g| times |h|)$], [Universal operation],
)

All operations produce canonical results automatically through the BDD construction primitives.

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

== Image and Preimage Implementation

The image and preimage operations (detailed in earlier sections) are implemented using BDD operations:

```rust
fn image(&self, from: Ref) -> Ref {
    let conj = self.bdd.apply_and(from, self.transition);
    let mut result = conj;
    for var in &self.present_vars {
        result = self.exists(result, *var);
    }
    self.rename(result, &self.next_vars, &self.present_vars)
}

fn preimage(&self, to: Ref) -> Ref {
    let to_next = self.rename(to, &self.present_vars, &self.next_vars);
    let conj = self.bdd.apply_and(self.transition, to_next);
    let mut result = conj;
    for var in &self.next_vars {
        result = self.exists(result, *var);
    }
    result
}

fn exists(&self, f: Ref, var: usize) -> Ref {
    let f0 = self.bdd.compose(f, var, self.bdd.zero);
    let f1 = self.bdd.compose(f, var, self.bdd.one);
    self.bdd.apply_or(f0, f1)
}

fn rename(&self, f: Ref, from_vars: &[usize], to_vars: &[usize]) -> Ref {
    let mut result = f;
    for (from_var, to_var) in from_vars.iter().zip(to_vars) {
        let to_bdd = self.bdd.mk_var(*to_var);
        result = self.bdd.compose(result, *from_var, to_bdd);
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

The size of a BDD is *extraordinarily sensitive* to the ordering of variables.
To understand why, consider a simple function that checks if two bit-vectors are equal: $f(x_1, ..., x_n, y_1, ..., y_n) = (x_1 equiv y_1) and ... and (x_n equiv y_n)$.

With a poor ordering that groups all $x$ variables together before the $y$ variables --- say $(x_1, ..., x_n, y_1, ..., y_n)$ --- the BDD must "remember" all $n$ bits of $x$ before it can start comparing them with $y$.
This creates an exponentially large BDD with $Theta(2^n)$ nodes, making verification impossible for even moderate $n$.

But with a clever ordering that interleaves corresponding variables --- $(x_1, y_1, x_2, y_2, ..., x_n, y_n)$ --- each pair can be checked immediately and the result propagated forward.
The BDD collapses to just $O(n)$ nodes!
Same function, thousand-fold difference in representation size.

For model checking, this insight translates directly: interleave present and next-state variables.
Instead of ordering all present-state variables $x, y, z, ...$ before their next-state counterparts $x', y', z', ...$, use the pattern $x, x', y, y', z, z', ...$
This keeps related variables close together in the decision tree, dramatically reducing BDD size for typical transition relations where each next-state variable depends primarily on its corresponding present-state variable.

=== When BDDs Work Well

BDDs achieve dramatic compression on systems with exploitable structure.
The key patterns that BDDs handle efficiently are:

*Regular structure*:
- Counters, shift registers, state machines with repeating patterns
- Hardware control logic with systematic transitions
- Protocols with symmetric processes

#example[
  A 32-bit hardware counter has over 4 billion states, yet its transition relation --- flip the low bit, propagate carries predictably --- compresses to a BDD with just hundreds of nodes.
  The regularity makes the difference.
]

*Local transitions*:
- Changes affect only a few variables at each step
- Sparse dependency graphs (each variable depends on few others)
- Most variables remain unchanged, enabling massive subgraph sharing

#example[
  A sliding window protocol moves packets sequentially.
  Transitioning from state $i$ to $i+1$ might update only 2-3 variables out of dozens.
  BDDs automatically share the unchanged portions.
]

*Symmetry and invariants*:
- Symmetric processes (multiple identical components)
- Properties with high symmetry across the state space
- Regular constraints that affect many states uniformly

*Real-world impact*:

Symbolic model checking has enabled verification of cache coherence protocols with more than $10^120$ distinct states.
For perspective, the observable universe contains merely $10^80$ atoms.
The protocol's structure --- symmetric processes, local interactions, regular transitions --- aligned perfectly with BDD strengths, making the impossible routine.
In modern protocol verification, handling $10^20$ states is standard practice.

=== When BDDs Struggle

BDDs can blow up exponentially for certain problem classes:

*Arithmetic operations*:
- Integer multiplication: BDD size is $Theta(2^n)$ for $n$-bit operands
- Division, modulo, and complex arithmetic circuits
- Datapath logic with wide bit-vectors

#note[
  *Why multiplication is hard:* Computing $z = x times y$ creates global dependencies --- every output bit potentially depends on every input bit in complex ways.
  There's no local structure to exploit, no subformulas to share.
  The BDD explodes with decision paths.
]

*Irregular patterns*:
- Random logic without exploitable structure
- Cryptographic hash functions (designed to destroy regularity)
- Operations intentionally creating non-local dependencies

*Poor variable ordering*:
- Suboptimal ordering causes exponential blowup
- Finding optimal ordering is NP-complete
- Even sophisticated heuristics fail on irregular circuits

#example[
  The equality function $f(x_1, ..., x_n, y_1, ..., y_n) = (x_1 equiv y_1) and ... and (x_n equiv y_n)$:

  / Bad ordering $(x_1, ..., x_n, y_1, ..., y_n)$: $Theta(2^n)$ nodes
  / Good ordering $(x_1, y_1, x_2, y_2, ..., x_n, y_n)$: $O(n)$ nodes

  Same function, thousand-fold difference!
]

*Mitigation strategies*:

When BDDs struggle, modern verification adapts rather than gives up:

- *Abstraction*: Simplify the model by hiding irrelevant details (e.g., abstract away data values when verifying control logic)
- *Compositional verification*: Break the system into components, verify separately, reason about composition
- *Hybrid approaches*: Use BDDs for control logic, SAT solvers for datapaths
- *Alternative methods*: Switch to SAT-based bounded model checking or IC3/PDR when appropriate

The portfolio approach --- applying each technique where it excels --- dominates modern verification practice.

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

This hash consing technique provides three crucial guarantees.

First, _sharing_: identical subgraphs are never duplicated.
If two different parts of a BDD reach a node representing "$x_5 = 1 arrow.r.double f$", both simply point to the same shared node.
This sharing is automatic and pervasive, often reducing memory usage by orders of magnitude.

Second, _canonicity_: given a fixed variable ordering, every Boolean function has exactly one BDD representation.
Two BDDs represent the same function if and only if they are pointer-identical.
This makes equivalence checking instantaneous --- just compare pointers!
In practice, this means BDD operations can detect fixpoints in constant time, crucial for efficient model checking.

Third, _efficiency_: because of sharing, BDD operations are polynomial in the size of the BDD, not exponential in the number of variables.
Combining two BDDs with a million nodes each might produce a result with two million nodes (in the worst case), not $2^1000000$ nodes.
This polynomial scaling --- combined with aggressive sharing --- is what makes symbolic model checking tractable.

== Optimization Techniques

Practical symbolic model checking requires numerous optimizations to handle large state spaces efficiently.

=== Early Termination

Many fixpoint computations can terminate early when the answer is known.

#example(name: "Early Termination in EF")[
  When checking $op("EF") phi$:

  ```
  EF(phi):
    Z := SAT(phi)
    if Z ∩ initial ≠ ∅:  // Found a path immediately!
      return true

    loop:
      Z_new := Z ∪ Pre(Z)
      if Z_new ∩ initial ≠ ∅:  // Found a path!
        return true
      if Z_new = Z: break
      Z := Z_new

    return false  // No path exists
  ```

  Instead of computing entire fixpoint, stop as soon as we reach initial states.
]

#example(name: "Early Termination in AG")[
  When checking $op("AG") phi$:

  ```
  AG(phi):
    Z := SAT(phi)
    if initial ⊈ Z:  // Violation found immediately!
      return false

    loop:
      Z_new := Z ∩ AX(Z)
      if initial ⊈ Z_new:  // Found violation!
        return false
      if Z_new = Z: break
      Z := Z_new

    return true
  ```
]

=== Partitioned Transition Relations

Instead of monolithic $T(v,v')$, use conjunctive partitioning.

#definition(name: "Conjunctive Partitioning")[
  Express transition relation as:
  $ T(v,v') = T_1(v,v') and T_2(v,v') and ... and T_n(v,v') $

  Where each $T_i$ depends on only a few variables.
]

*Advantage*: Smaller BDDs, more efficient operations.

#example(name: "Variable-Based Partitioning")[
  For system with variables $x_1, ..., x_n$:

  $ T(v,v') = and.big_(i=1)^n T_i(x_i, x'_i, x_1, ..., x_(i-1)) $

  Each $T_i$ defines next value of $x'_i$ in terms of current state.

  For image computation:
  ```
  Img(S):
    result := S
    for i := 1 to n:
      result := result ∧ T_i
      result := ∃x_i. result  // Eliminate as soon as possible
    // Rename all x'_i to x_i
    return rename(result)
  ```

  Early quantification keeps BDD sizes small.
]

=== Dynamic Variable Reordering

BDD size is *critically* sensitive to variable ordering.

#example(name: "Ordering Impact")[
  Function: $f(x_1, ..., x_n, y_1, ..., y_n) = (x_1 and y_1) or ... or (x_n and y_n)$

  *Bad ordering* $x_1, x_2, ..., x_n, y_1, ..., y_n$:
  - BDD size: $O(2^n)$ (exponential!)

  *Good ordering* $x_1, y_1, x_2, y_2, ..., x_n, y_n$:
  - BDD size: $O(n)$ (linear)
]

*Dynamic reordering*: Automatically adjust variable order during computation.

*Heuristics*:
- *Sifting*: Try moving each variable to different positions, keep best
- *Window permutation*: Optimize small windows of adjacent variables
- *Genetic algorithms*: Evolve good orderings over time

*Trigger conditions*:
- Reorder when BDD size exceeds threshold
- Reorder periodically during long computations
- Reorder on memory pressure

#note[
  Dynamic reordering can be expensive (minutes for large BDDs).
  But it's often essential --- without it, model checking may fail entirely.
]

=== Garbage Collection

BDDs require careful memory management.

*Reference counting*:
- Each BDD node tracks how many other nodes/roots reference it
- When count reaches 0, node can be reclaimed

*Mark and sweep*:
- Periodically mark all reachable nodes from roots
- Sweep and free unmarked nodes

*Practical strategy*:
```
after_operation():
  if nodes_allocated > threshold:
    garbage_collect()

  if nodes_allocated > critical_threshold:
    force_reordering()
```

=== Caching and Memoization

Most BDD operations use *computed tables* (caches).

#definition(name: "Computed Table")[
  Hash table mapping $("op", "arg1", "arg2") arrow "result"$

  Before computing operation:
  - Check if result is already cached
  - If yes, return cached result immediately
  - If no, compute, cache, and return
]

*Example*: Computing $f and g$:
```
and(f, g):
  // Check cache
  if ("and", f, g) in computed_table:
    return computed_table[("and", f, g)]

  // Base cases
  if f = 0 or g = 0: return 0
  if f = 1: return g
  if g = 1: return f

  // Recursive case
  var := top_var(f, g)
  low := and(f|_var=0, g|_var=0)
  high := and(f|_var=1, g|_var=1)
  result := make_node(var, low, high)

  // Cache and return
  computed_table[("and", f, g)] := result
  return result
```

*Cache management*:
- Flush when too large (keep only recent entries)
- Preserve entries for common subexpressions

=== Frontier Simplification

During fixpoint computation, simplify intermediate BDDs.

#example(name: "Approximate Reachability")[
  Standard: $R_0, R_1, R_2, ...$ where $R_(i+1) = R_i union "Img"(R_i)$

  Problem: $R_i$ BDDs grow large quickly

  Solution: *Restrict* intermediate results to relevant regions:
  ```
  reach():
    R := initial
    loop:
      R_new := R ∪ Img(R)

      // Simplification: restrict to care set
      R_new := R_new ∩ care_set

      if R_new = R: break
      R := R_new
  ```

  Where `care_set` might be:
  - States satisfying certain invariants
  - States within bounded depth
  - States with specific properties
]

=== Abstraction and Refinement

For very large systems, use abstraction.

#definition(name: "Counterexample-Guided Abstraction Refinement (CEGAR)")[
  1. *Abstract* the system (reduce state space)
  2. *Model check* the abstraction
  3. If property holds: done (holds in concrete system too)
  4. If property fails:
    - Check if counterexample is *spurious*
    - If real: done (found bug)
    - If spurious: *refine* abstraction, go to 2
]

*Abstraction techniques*:
- *Predicate abstraction*: Track only selected predicates
- *Localization reduction*: Consider only relevant variables
- *Cone of influence*: Ignore variables not affecting property

=== Compositional Verification

Verify components separately, then compose results.

#theorem(name: "Assume-Guarantee Reasoning")[
  To verify $M_1 parallel M_2 models phi$:

  1. Find assumption $A$ on $M_2$
  2. Verify $M_1$ under assumption $A$ satisfies $phi$
  3. Verify $M_2$ guarantees $A$

  Then $M_1 parallel M_2 models phi$
]

*Benefit*: Avoid composing full state spaces.

#note[
  *Tool Support*:
  - Most modern BDD packages include these optimizations
  - Dynamic reordering is nearly universal
  - Partitioned transition relations in tools like NuSMV, VIS
  - CEGAR in tools like BLAST, CPAchecker
  - User typically configures thresholds and heuristics
]

= Conclusion

Symbolic model checking using BDDs represents one of the great success stories in formal methods and automated verification.

== Key Takeaways

Symbolic model checking revolutionized formal verification through several key insights:

*Symbolic representation over enumeration*:

The central insight is deceptively simple: don't enumerate states, _describe_ them.
By representing state sets as Boolean formulas encoded in BDDs, we can reason about exponentially large sets --- $10^20$, even $10^100$ states --- using compact data structures that fit in ordinary computer memory.
What seemed impossible for explicit enumeration becomes routine.

*Image and preimage operations*:

These fundamental operations --- computing successors and predecessors symbolically --- form the computational heart of the technique.
Built from BDD conjunction and existential quantification, they perform set-level computation that would require billions of individual state transitions if done explicitly.
This enables reachability analysis and temporal logic model checking on massive state spaces.

*Fixpoint computation for temporal logic*:

CTL model checking reduces to fixpoint computation, iteratively expanding or contracting state sets until stabilization.
The finite state space guarantees termination.
The canonical BDD representation makes fixpoint detection instantaneous --- just compare pointers.
This combination makes the algorithm both theoretically elegant and practically efficient.

*Practical impact*:

Symbolic model checking has proven effective for:
- *Hardware verification*: Cache coherence protocols, processor designs
- *Safety-critical systems*: Control systems where failure has severe consequences
- *Concurrent systems*: Distributed algorithms, protocols, concurrent programs where testing struggles with combinatorial state explosion
- *Bug detection*: Finding subtle corner cases that testing would miss

== The Power of BDDs

BDDs achieve their remarkable compression through the interplay of two simple ideas.

_Sharing_ means that common subformulas appear only once in the graph, automatically reused wherever needed.
Imagine a transition relation where a hundred different transitions all check "is the buffer full?" before proceeding differently.
In an explicit representation, you'd check this condition a hundred times.
In a BDD, that test appears once; all hundred branches simply share the same node.
The more regular your system, the more opportunities for sharing, the more dramatic the compression.

_Reduction_ eliminates redundancy at the node level.
If a decision node's two branches lead to the same outcome regardless of the test, why test at all?
The reduction rules automatically bypass such pointless decisions.
Combined with sharing, this produces _canonical_ minimal representations --- the smallest possible BDD for a given function and variable ordering.

When these mechanisms align with problem structure --- regular patterns in the system, local transitions that affect few variables, a well-chosen variable ordering --- BDDs can represent exponentially large sets with polynomial-sized graphs.
A perfect storm of structure exploitation.
This is why BDDs revolutionized hardware verification: digital circuits are full of regular, local patterns just begging to be compressed.

== Limitations and Extensions

No tool is universal, and understanding BDD limitations is as important as knowing their strengths.
The difference between success and failure often hinges on recognizing when BDDs are the right tool and when to reach for alternatives.

=== When BDDs Excel

BDDs thrive on structure.
Regular, predictable patterns in your system translate directly to compression in the BDD.
Counters, shift registers, and finite state machines --- systems built from repeating units with local connections --- compress beautifully.
A 64-bit counter has $2^64$ states but needs only a few hundred BDD nodes to represent its transition relation.

Control logic, especially in hardware, exhibits the kind of regularity BDDs love.
Instruction decoders, protocol state machines, arbiter circuits --- these follow regular patterns with clear structure.
Symmetric protocols, where multiple processes execute identical code, create natural opportunities for sharing: the BDD for one process is automatically reused for all others.

Locality is the other key.
When transitions affect only a handful of variables --- a counter incrementing, a buffer inserting an element, a state machine changing mode --- the BDD stays compact because most variables remain unchanged and their sub-BDDs are shared.
Sparse dependency graphs, where each variable depends on few others, maintain this locality and keep BDDs manageable.

And of course, variable ordering matters enormously:
- Related variables should be placed nearby
- Interleave present/next-state variables
- Follow natural ordering from system structure

*Characteristic examples*:
- Cache coherence protocols with $10^20$+ states
- Communication protocols (sliding window, alternating bit)
- Hardware control units (instruction decoders, FSMs)
- Mutual exclusion algorithms

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
- Trade-off: Incomplete (may miss bugs beyond bound $k$) but very effective in practice

*IC3/PDR (Property Directed Reachability)*:
- Incrementally constructs inductive invariants
- Avoids explicit BDD representation or bounded unrolling
- Represents states using CNF clauses
- Effective for safety properties
- Represents a major algorithmic advance beyond BDDs
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

=== Choosing the Right Approach

*Use BDDs when*:
- System has regular structure (protocols, control logic)
- Properties involve reachability, CTL model checking
- Need canonical representation for equivalence checking
- Transitions are local and symbolic operations are efficient

*Use SAT/BMC when*:
- System has irregular structure or arithmetic
- Bug-finding is primary goal (completeness not required)
- Need to handle large bit-vectors or complex datapaths
- Bounded analysis is sufficient

*Use IC3/PDR when*:
- Verifying safety properties
- Need complete verification without fixed bounds
- BDD variable ordering is problematic

*Use abstraction when*:
- System is too large for direct verification
- Can identify relevant variables automatically
- Iterative refinement is feasible

#note[
  In practice, modern verification tools often combine multiple techniques, leveraging the strengths of each.
  The choice depends on the system structure, property type, and available computational resources.
]
