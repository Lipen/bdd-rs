#import "@preview/cetz:0.4.2"
#import "@preview/fletcher:0.5.8" as fletcher: diagram, edge, node
#import "@preview/lovelace:0.3.0"

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

_Model checking_ is an automated formal verification technique that exhaustively explores all possible behaviors of a system to determine whether it satisfies specified properties.
Unlike _testing_, which examines selected execution scenarios, or _theorem proving_, which requires manual proof construction, model checking provides a fully automated "push-button" approach to verification.

Model checking provides: *given a model of your system and a specification of desired behavior, the model checker will automatically determine whether the specification holds*.
If the property holds, you get a _proof_ of correctness.
If it fails, you get a _counterexample_ --- a concrete execution trace demonstrating the violation.

This makes model checking particularly valuable for:

- *Finding subtle bugs* that testing might miss (rare interleavings, corner cases)
- *Proving correctness* rather than merely building confidence through testing
- *Understanding failures* through concrete counterexamples
- *Exhaustive exploration* without writing test cases

== The Challenge: State Explosion

The main challenge in model checking is the *state explosion problem*.
For a system with $n$ boolean variables, the state space size grows as:

$ |S| = 2^n $

This exponential growth makes exhaustive enumeration quickly infeasible.
Consider how rapidly the numbers escalate:
- 10 variables $=>$ 1,024 states (trivial)
- 20 variables $=>$ 1,048,576 states (still manageable)
- 30 variables $=>$ 1,073,741,824 states (over a billion --- getting difficult)
- 100 variables $=>$ $1.27 times 10^30$ states (more states than atoms in a trillion universes)

To put this in perspective: if you could check one billion states per second, verifying a 100-variable system would take longer than the age of the universe --- multiplied by $10^21$.

Traditional _explicit-state_ model checking stores and manipulates each state individually.
Even with optimizations like hash tables and efficient graph algorithms, this approach hits a wall around $10^7$ to $10^8$ states.
Yet real systems routinely have $10^20$ states or more.

Real systems easily exceed these limits:
- A simple mutual exclusion protocol with 10 processes: $> 10^10$ states
- A processor cache coherence protocol: $> 10^20$ states
- A distributed system with modest parallelism: $> 10^30$ states

The state explosion problem threatened to limit model checking to toy examples.
Symbolic model checking provides the solution.

== The Solution: Symbolic Representation

_Symbolic model checking_ uses Boolean formulas to represent _sets of states_ rather than enumerating them individually.
This simple idea leads to significant improvements in scalability.

#definition[
  A set of states $S subset.eq {0,1}^n$ can be represented by its *characteristic function* $chi_S : {0,1}^n -> {0,1}$ where:
  $
    chi_S (s) = cases(
      1 "if" s in S,
      0 "if" s in.not S
    )
  $

  For brevity, we often write $S(v_1, ..., v_n)$ instead of $chi_S(v_1, ..., v_n)$ when the context is clear.
  This notation treats the set $S$ as a Boolean function: $S(s) = 1$ if and only if $s in S$.
]

Using *Binary Decision Diagrams (BDDs)*, we can represent these characteristic functions _compactly_ and perform operations _efficiently_.

#example(name: "The Power of Symbolic Representation")[
  Consider representing all even numbers from 0 to $2^100 - 1$ (i.e., all 100-bit numbers with least significant bit = 0):

  - *Explicit representation*: Store $2^99$ individual numbers
    - Memory required: $2^99 times 100$ bits $approx 10^29$ GB (utterly impossible)
    - Time to check membership: $O(2^99)$ comparisons in worst case

  - *Symbolic representation*: Encode the formula "last bit = 0"
    - BDD representation: Single node testing bit $x_0$
    - Memory required: $approx$ 100 bytes
    - Time to check membership: $O(1)$ --- traverse one node

  The characteristic function is $chi_"even" (x_0, x_1, ..., x_99) = overline(x_0)$ where $x_0$ is the least significant bit.

  This *exponential compression* --- representing $2^99$ states with a constant-sized BDD --- exemplifies why symbolic model checking enables verification of systems with $10^20$+ states.
]

This compression makes it possible to verify systems with $10^20$ states or more --- systems that were intractable with explicit-state methods.

Why does this compression work so well in practice?
The answer lies in the inherent _regularity_ of engineered systems.
Real hardware and software aren't random --- they're designed with regular patterns:
- Counters increment predictably
- Buses transfer data according to fixed protocols
- Control logic follows structured state machines
- Parallel components often behave symmetrically

BDDs exploit this structure through two mechanisms.
First, _sharing_: when multiple parts of the system check "is the buffer full?" or "is the counter zero?", the BDD represents that test once and all components share it.
Second, _reduction_: redundant decisions ("does this matter?") are eliminated automatically.

The result: regular structure in the system translates directly to compact BDD representation.
The more regular your system, the better the compression.
We'll see the precise mechanics of how this works in the Implementation section (Section 7).

= Preliminaries

Before diving into symbolic model checking algorithms, we need to establish the mathematical foundations.
This section introduces the core concepts you'll use throughout: how we represent systems, what states and transitions mean formally, and the key idea of characteristic functions.

Don't worry if these seem abstract at first --- we'll see concrete examples immediately after each definition, and everything will come together when we build the model checking algorithms in later sections.

Let's start with the most basic question: what exactly do we mean by a "state" in a system?

== States and State Spaces

#definition(name: "State")[
  A *state* is a complete assignment of values to all system variables.
  For a system with variables $V = {v_1, v_2, ..., v_n}$ where each $v_i in {0,1}$, a state is an element $s in {0,1}^n$.
]

#example(name: "Two-Bit Counter")[
  Consider a counter with two bits: $x$ (high bit) and $y$ (low bit).

  #table(
    columns: 4,
    stroke: (x, y) => if y == 0 { (bottom: 0.8pt) },
    [*State*], [*$x$*], [*$y$*], [*Value*],
    [$s_0$], [0], [0], [0],
    [$s_1$], [1], [0], [1],
    [$s_2$], [0], [1], [2],
    [$s_3$], [1], [1], [3],
  )

  Each row represents one complete assignment of values to all system variables.
]

== Sets of States: Symbolic Representation

In symbolic model checking, we work with *sets of states* rather than individual states.
A set $S subset.eq {0,1}^n$ is represented by its characteristic function as a Boolean formula.

#definition(name: "Symbolic State Set Notation")[
  A set $S$ is represented by a Boolean formula $phi(v_1, ..., v_n)$ (or simply $S(v_1, ..., v_n)$) such that:

  $ S = {s in {0,1}^n | S(s) = 1} $

  This formula evaluates to 1 for states in $S$ and 0 for states not in $S$.
]

#example(name: "State Set")[
  For the two-bit counter, consider the set of "odd" states:

  $ S_"odd" = {s_1, s_3} = {(1,0), (1,1)} $

  This can be represented by the formula $phi_"odd" (x,y) = x$, i.e., the set ${(x,y) | x = 1}$.

  We can verify:
  - $phi_"odd" (0,0) = 0$ → $s_0 in.not S_"odd"$ #YES
  - $phi_"odd" (1,0) = 1$ → $s_1 in S_"odd"$ #YES
  - $phi_"odd" (0,1) = 0$ → $s_2 in.not S_"odd"$ #YES
  - $phi_"odd" (1,1) = 1$ → $s_3 in S_"odd"$ #YES
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

  $ T(x, x') = x xor x' = (x and overline(x)') or (overline(x) and x') $

  Let's verify all possible transitions:

  #table(
    columns: 5,
    stroke: (x, y) => if y == 0 { (bottom: 0.8pt) },
    [*Current ($x$)*], [*Next ($x'$)*], [*$T(x,x')$*], [*Legal?*], [*Meaning*],
    [0], [0], [0], [No], [Can't stay at 0],
    [0], [1], [1], [Yes], [From 0 to 1 #YES],
    [1], [0], [1], [Yes], [From 1 to 0 #YES],
    [1], [1], [0], [No], [Can't stay at 1],
  )
]

== Two-Bit Counter: Complete Example

Let's build a complete transition system for a 2-bit counter that increments modulo 4.

#example(name: "Two-Bit Counter Transition System")[

  *Variables*: $x$ (low bit), $y$ (high bit)

  *States*: $S = {(0,0), (1,0), (0,1), (1,1)}$ representing binary values 00, 01, 10, 11 (decimal 0, 1, 2, 3)

  *Initial state*: $I = {(0,0)}$, represented by formula $overline(x) and overline(y)$

  *Transitions*: Increment by 1 (mod 4):
  - $(0,0) -> (1,0)$ (binary 00 $=>$ 01, i.e., 0 $=>$ 1)
  - $(1,0) -> (0,1)$ (binary 01 $=>$ 10, i.e., 1 $=>$ 2)
  - $(0,1) -> (1,1)$ (binary 10 $=>$ 11, i.e., 2 $=>$ 3)
  - $(1,1) -> (0,0)$ (binary 11 $=>$ 00, i.e., 3 $=>$ 0)

  *Transition relation*: How do we encode this symbolically?

  Observe the pattern of binary increment:
  - Low bit $x$ always toggles: $x' = overline(x)$
  - High bit $y$ flips when low bit $x$ was 1 (carry): $y' = y xor x$

  Therefore:
  $ T(x, y, x', y') = (x' equiv overline(x)) and (y' equiv y xor x) $

  where $equiv$ denotes logical equivalence (XNOR).

  Verification:
  - $(0,0)$: $x'=1$, $y'=0 xor 0=0$ → $(1,0)$ #YES
  - $(1,0)$: $x'=0$, $y'=0 xor 1=1$ → $(0,1)$ #YES
  - $(0,1)$: $x'=1$, $y'=1 xor 0=1$ → $(1,1)$ #YES
  - $(1,1)$: $x'=0$, $y'=1 xor 1=0$ → $(0,0)$ #YES

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
      content((0, -1.5), [$x -> 1$], anchor: "east", padding: 0.2)

      line("s1.east", "s2.west", mark: (end: ">"), stroke: 1pt)
      content((1.5, -3), [$x -> 0,\ y -> 1$], anchor: "south", padding: 0.2)

      line("s2.north", "s3.south", mark: (end: ">"), stroke: 1pt)
      content((3, -1.5), [$x -> 1$], anchor: "west", padding: 0.2)

      line("s3.west", "s0.east", mark: (end: ">"), stroke: 1pt)
      content((1.5, 0), [$x -> 0,\ y -> 0$], anchor: "south", padding: 0.2)
    })
  ]
]

= Symbolic State Space Exploration

With symbolic representations of states and transitions in hand, we can now ask: how do we actually _explore_ the state space?

Model checking requires answering reachability questions:
- "Can the system reach an error state?"
- "From these states, where can execution go?"
- "Which states can lead to this condition?"

In explicit-state model checking, we'd iterate through states one at a time, following transitions.
But with symbolic representation, we can do something far more powerful: compute the successors (or predecessors) of _millions of states simultaneously_ using Boolean operations.

This requires two dual operations: *image* (forward reachability --- "where can we go?") and *preimage* (backward reachability --- "how did we get here?").
These are the workhorses of symbolic model checking.

== Image: Forward Reachability

#definition(name: "Image Operation")[
  Given a set of states $S$ and a transition relation $T$, the *image* of $S$ under $T$ is the set of all states reachable from $S$ in one transition:

  $ "Img"(S, T) = {s' | exists s in S : (s, s') in T} $

  In logical notation (using characteristic functions):
  $ "Img"(S, T)(v'_1, ..., v'_n) = exists v_1, ..., v_n . thin S(v_1, ..., v_n) and T(v_1, ..., v_n, v'_1, ..., v'_n) $

  Here $S(v)$ denotes the characteristic function of set $S$ (equals 1 for $v in S$), and $T(v, v')$ is the characteristic function of the transition relation (equals 1 when $(v, v')$ is a valid transition).
]

Intuitively, the image operation answers the question: "Where can I go in one step from these states?"

Recall from the definition above that $S(v)$ denotes the characteristic function of set $S$.

=== Computing the Image

The image computation might seem abstract at first, but it's performing a simple conceptual operation: finding all successors.
Let's break down how this works symbolically.

The computation proceeds in three steps:

+ *Conjunction*: $S(v) and T(v, v')$

  This combines the current states with the transition relation.
  Think of it as saying: "Consider all valid transitions $(v, v')$ where the source $v$ is in our current set $S$."
  The result is a Boolean function that's true for pairs $(v, v')$ representing valid transitions from $S$.

+ *Existential quantification*: $exists v . thin (S(v) and T(v, v'))$

  This eliminates the current-state variables $v = (v_1, ..., v_n)$, leaving only the next-state variables $v'$.
  Conceptually: "For each potential successor $v'$, is there _some_ state in $S$ that can transition to it?"
  If yes, include $v'$ in the result; if no, exclude it.

+ *Variable renaming*: Rename next-state variables $v' => v$

  This is bookkeeping: we rename the primed variables back to unprimed so the result is expressed in the same variable space as the input.

The result is a Boolean formula representing exactly the set of all states reachable in one step from $S$.

The beauty of this approach: we compute successors for _all states in $S$ simultaneously_ using Boolean operations, never enumerating individual states.

#note[
  *Understanding Existential Quantification*:

  The operation $exists v . thin f(v, w)$ eliminates variable $v$ by computing $f(0, w) or f(1, w)$ (Shannon expansion).
  This gives us all values of $w$ for which $f$ can be true for *some* value of $v$.

  In image computation, $exists v . thin (S(v) and T(v, v'))$ finds all $v'$ such that *some* state in $S$ can transition to $v'$.
]#example(name: "Image of Toggle System")[
  Consider the toggle system with $T(x, x') = x xor x'$.

  *Question*: From state $s_0$ (where $x=0$), what states can we reach?

  $S = {s_0}$ is represented by $overline(x)$.

  *Step 1: Conjunction*

  $
    S(x) and T(x, x') & = overline(x) and (x xor x') \
                      & = overline(x) and ((x and overline(x)') or (overline(x) and x')) \
                      & = overline(x) and x'
  $

  (The term $x and overline(x)'$ vanishes because $x = 0$)

  *Step 2: Existential Quantification*

  $ exists x . thin (overline(x) and x') = x' $

  We eliminate $x$ by computing:
  $ (overline(x) and x')[x -> 0] or (overline(x) and x')[x -> 1] = (1 and x') or (0 and x') = x' $

  *Step 3: Rename*

  Rename $x'$ to $x$: result is $x$, which represents state $s_1$ where $x=1$. #YES

  *Conclusion*: From $x=0$, we can reach $x=1$ in one step.
]

=== Reachability Analysis

The image operation enables us to compute *all* reachable states through iterative fixpoint computation:

#theorem(name: "Reachable States")[
  The set of all states reachable from initial states $I$ is the least fixpoint:

  $ R^* = mu Z. thin I or "Img"(Z, T) $

  *Algorithm* for computing reachable states:
  #v(-1em)
  #lovelace.pseudocode-list(hooks: 0.5em)[
    + $R := I$
    + *loop*
      + $R_"new" := R union "Img"(R, T)$
      + *if* $R_"new" = R$ *then* *break*
      + $R := R_"new"$
    + *return* $R$
  ]
  #v(-1em)
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

  Fixpoint reached!
  All four states are reachable.
]

#note[
  *Pause and Predict:* Before reading on, try this thought experiment.

  Imagine a 3-bit counter (states 0 through 7) that increments modulo 8.
  Starting from state 0, how many iterations would you need to reach the fixpoint?

  Think about it for a moment...

  *Answer:* Just 3 iterations! Why?
  Because each iteration doesn't just add the next state --- it adds _all states reachable in one step_ from the current set.

  - $R_0 = {0}$
  - $R_1 = {0, 1}$ (gained 1 state)
  - $R_2 = {0, 1, 2}$ (gained 1 state)
  - $R_3 = {0, 1, 2, 3}$ (gained 1 state)

  Wait, that's linear!
  But symbolic methods should be better...

  The key insight: for a simple counter, reachability _is_ linear in the state space because we can only reach one new state per step.
  The power of symbolic model checking shows up when the transition relation allows reaching _many_ states simultaneously --- like in systems with parallelism, non-determinism, or broadcast communication.

  *Self-check:* Can you think of a system where one image operation would add 1000 states at once?
  (Hint: think about parallel processes or broadcast protocols.)
]

== Preimage: Backward Reachability

The *preimage* (or *predecessor*) operation computes states that can reach a given set in one step.
This is the dual of the image operation, working backwards through the transition relation.

#definition(name: "Preimage Operation")[
  Given a set of states $S$ and transition relation $T$, the *preimage* of $S$ under $T$ is:

  $ "Pre"(S, T) = {s | exists s' : (s, s') in T and s' in S} $

  In logical notation, using characteristic functions:
  $ "Pre"(S, T)(v_1, ..., v_n) = exists v'_1, ..., v'_n . thin T(v_1, ..., v_n, v'_1, ..., v'_n) and S(v'_1, ..., v'_n) $

  Here we first rename $S(v) => S(v')$ to express target states in next-state variables, then eliminate $v'$ after conjoining with $T$.
]Intuitively, preimage answers: "From which states can I reach $S$ in one step?"

=== Computing the Preimage

The preimage computation symbolically computes predecessor states using three steps (dual to image):

+ *Variable renaming*: Rename $S(v) => S(v')$ to express target states in next-state variables
+ *Conjunction*: $S(v') and T(v, v')$ --- combine renamed target states with transition relation
+ *Existential quantification*: $exists v' . thin (S(v') and T(v, v'))$ --- eliminate next-state variables $v'$

The result is a Boolean formula in variables $v$ representing the set of predecessor states.

#example(name: "Preimage of Toggle System")[
  Recall the toggle system with $T(x, x') = x xor x'$.

  *Question*: From which states can we reach $s_1$ (where $x=1$)?

  Let $S = {s_1} = {x = 1}$, represented by formula $x$.

  *Step 1: Rename* $S(x) => S(x')$

  $ S(x') = x' $

  *Step 2: Conjunction*

  $
    S(x') and T(x, x') & = x' and (x xor x') \
                       & = x' and ((x and overline(x)') or (overline(x) and x')) \
                       & = x' and (overline(x) and x') quad "(since" x' "is true, first term vanishes)" \
                       & = overline(x) and x'
  $

  *Step 3: Existential Quantification*

  $ exists x' . thin (overline(x) and x') = overline(x) $

  We eliminate $x'$ by computing:
  $ (overline(x) and x')[x' <- 0] or (overline(x) and x')[x' <- 1] = 0 or overline(x) = overline(x) $

  *Conclusion*: From state $s_0$ (where $x=0$), we can reach state $s_1$ in one step. #YES
]

#example(name: "Preimage in Two-Bit Counter")[
  For the counter, find predecessors of state $(1,1)$ (binary 11, value 3).

  Target set: $S = {(1,1)}$, represented by $x and y$.

  Transition: $x' = overline(x)$, $y' = y xor x$

  After renaming $S$: $x' and y'$

  Transition relation:
  $ T(x, y, x', y') = (x' equiv overline(x)) and (y' equiv y xor x) $

  Conjunction:
  $ x' and y' and (x' equiv overline(x)) and (y' equiv y xor x) $

  From $x' = 1$ and $x' equiv overline(x)$, we get $overline(x) = 1$, so $x = 0$.
  From $y' = 1$ and $y' equiv y xor x$, we get $y xor x = 1$.
  With $x = 0$: $y xor 0 = 1$, so $y = 1$.

  After eliminating $x', y'$: result is $(overline(x) and y)$, representing state $(0,1)$ (binary 10, value 2).

  *Conclusion*: State $(0,1)$ can reach $(1,1)$ in one step. #YES
]

=== Backward Reachability Analysis

Just as image enables forward reachability, preimage enables *backward reachability*:

#theorem(name: "Backward Reachable States")[
  The set of states that can reach a target set $T$ is:

  $ R^*_"back" (T) = mu Z. thin T or "Pre"(Z, T_"rel") $

  *Algorithm* for computing backward reachable states:
  #v(-1em)
  #lovelace.pseudocode-list(hooks: 0.5em)[
    + $R := T$
    + *loop*
      + $R_"new" := R union "Pre"(R, T)$
      + *if* $R_"new" = R$ *then* *break*
      + $R := R_"new"$
    + *return* $R$
  ]
  #v(-1em)
]

This is useful for:
- *Safety checking*: Can initial states reach bad states? $I inter R^*_"back" ("Bad") eq.not emptyset$?
- *Invariant checking*: Working backwards from violations
- *Goal-directed search*: Start from targets, work backwards

#note[
  *Forward vs Backward*:
  - Forward reachability: $R^* = mu Z. thin I or "Img"(Z)$ --- starts from initial states
  - Backward reachability: $R^*_"back" = mu Z. thin T or "Pre"(Z)$ --- starts from target states

  Choose based on problem:
  - Use forward if initial states are small/simple
  - Use backward if target states are small/simple
  - Sometimes one direction has much smaller BDDs.
]

#note[
  *Checkpoint:* We now have the core operations for symbolic exploration:
  - *Image*: compute successors symbolically
  - *Preimage*: compute predecessors symbolically
  - Both use the same pattern: conjoin with transition relation, then eliminate variables

  These operations are the workhorses of symbolic model checking.
  Every algorithm we'll see builds on these primitives.
]

= The Modal Mu-Calculus: Foundation of Fixpoints

*Why are we suddenly talking about fixpoints?*

You might wonder why we're introducing abstract mathematical machinery when we just learned practical operations like image and preimage.
Here's why: the temporal properties we want to verify ("eventually", "always", "until") all reduce to computing _fixpoints_ of set-valued functions.

The mu-calculus provides the theoretical foundation that makes this reduction precise.
Understanding fixpoints --- even at a basic level --- will make the CTL model checking algorithms that follow completely natural.
Think of this section as learning the theory behind a magic trick before we perform it.

== Why Fixpoints?

Many temporal properties are inherently _recursive_: determining whether a property holds requires checking both the current state and future states, which themselves require checking their futures, and so on.
Fixpoints provide a mathematical mechanism to handle this recursion.

#definition(name: "Fixpoint")[
  Let $f: 2^S -> 2^S$ be a _monotone_ function on sets of states (i.e., $X subset.eq Y => f(X) subset.eq f(Y)$).

  - A set $X subset.eq S$ is a *fixpoint* of $f$ if $f(X) = X$
  - The *least fixpoint* $mu Z. thin f(Z)$ is the smallest set $X$ such that $f(X) = X$
  - The *greatest fixpoint* $nu Z. thin f(Z)$ is the largest set $X$ such that $f(X) = X$
]

#theorem(name: "Knaster-Tarski")[
  For any monotone function $f: 2^S -> 2^S$ on a finite lattice:

  - The least fixpoint exists and equals: $mu Z. thin f(Z) = inter.big {X | f(X) subset.eq X}$
  - The greatest fixpoint exists and equals: $nu Z. thin f(Z) = union.big {X | X subset.eq f(X)}$

  Moreover, these can be computed iteratively:
  - $mu Z. thin f(Z) = union.big_(i=0)^infinity f^i (emptyset) = emptyset union f(emptyset) union f(f(emptyset)) union ...$
  - $nu Z. thin f(Z) = inter.big_(i=0)^infinity f^i (S) = S inter f(S) inter f(f(S)) inter ...$
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

  *Least fixpoint* $mu Z. thin f(Z)$:

  $
    Z_0 & = emptyset \
    Z_1 & = T union "Pre"(emptyset) = T \
    Z_2 & = T union "Pre"(T) = {s | s "reaches" T "in" <= 1 "step"} \
    Z_3 & = T union "Pre"(Z_2) = {s | s "reaches" T "in" <= 2 "steps"} \\ & dots.v
  $

  Converges to _all_ states that can _eventually_ reach $T$.
]

#example(name: "Fixpoint Intuition: Invariants")[
  Consider computing states from which property $P$ _always_ holds.

  Define $f(Z) = P inter "Pre"(Z)$ ("$P$ holds and all successors in $Z$").

  *Greatest fixpoint* $nu Z. thin f(Z)$:

  $
    Z_0 & = S "  (all states)" \
    Z_1 & = P inter "Pre"(S) = P "  (states satisfying" P "with any successor)" \
    Z_2 & = P inter "Pre"(Z_1) = {s in S | P(s) and forall s' . T(s,s') => P(s')} \
    Z_3 & = P inter "Pre"(Z_2) = {s | P "holds along all paths of length" >= 2} \
        & dots.v
  $

  Converges to states from which $P$ holds on _all_ future paths forever.
]

== Why Is This Confusing?

The mu-calculus notation can be initially perplexing for several reasons:

+ *Variable binding*: The $Z$ in $mu Z. thin f(Z)$ is a bound variable ranging over _sets of states_, not individual states
+ *Monotonicity requirement*: Functions must be monotone for fixpoints to exist
+ *Nested fixpoints*: Complex properties involve alternating $mu$ and $nu$, creating intricate recursive structures
+ *Dual nature*: $mu$ computes from below (pessimistic), $nu$ from above (optimistic)

#note[
  Think of $mu$ as "prove by construction" (build up the set) and $nu$ as "prove by elimination" (remove counterexamples).

  - $mu Z. thin phi or op("EX") Z$: Start with $phi$, expand to states reaching $phi$
  - $nu Z. thin phi and op("AX") Z$: Start with all states, keep only those satisfying $phi$ with all successors good
]

= CTL Model Checking

CTL (Computation Tree Logic) provides a formal language for specifying properties about how systems evolve over time.
Why do we need such a logic?
Because the properties we care about in verification are inherently _temporal_:
- "The system never reaches a deadlock state" (safety)
- "Every request eventually receives a response" (liveness)
- "If the alarm triggers, the system must eventually reset" (response)
- "The mutex is never held by two processes simultaneously" (mutual exclusion)

Ordinary propositional logic can express properties of individual states ("the light is green") but cannot express how states relate across time ("the light is _eventually_ green" or "the light is green _until_ a car arrives").

CTL provides operators that quantify over possible execution paths.
Building on the fixpoint foundations established in Section 4, CTL model checking reduces these temporal properties to iterative set computations.
Every CTL operator corresponds directly to a fixpoint computation, making the logic both mathematically precise and computationally tractable with BDDs.

== The Computation Tree

From any state, multiple futures may be possible due to non-determinism --- different scheduling choices, environment inputs, or random events.
This creates a tree structure where each node is a state and each path represents one possible execution sequence.
The tree _branches_ at points where the system has choices.

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
  From $s_0$, the system can move to either $s_1$ or $s_2$ (non-deterministic choice).
  From $s_1$, there are again two possibilities.
  From $s_2$, only one transition is possible.

  When we verify a property, we need to specify: do we require the property to hold on _all_ paths, or is it sufficient that it holds on _some_ path?
  This is where CTL's path quantifiers (*A* = "for all paths", *E* = "there exists a path") become essential.
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
  Think: "tomorrow"

- *F* (Finally): Property eventually becomes true (in the Future)
  Think: "sometime in the future" --- we don't know when, but it happens

- *G* (Globally): Property remains true forever (Always)
  Think: "always" --- now and for all time to come

- *U* (Until): First property holds until second becomes true
  Think: "I'll keep working _until_ I finish" --- the first condition persists up to the moment the second occurs

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

CTL formulas typically express either _safety_ or _liveness_ properties --- the two main classes of system requirements.

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

Let's work through a complete example to see how CTL properties capture real system requirements.

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

  Recall: $op("AG") phi = nu Z. thin phi and op("AX") Z$

  $
    Z_0 & = S quad "(all states)" \
    Z_1 & = (not "bad") and op("AX") Z_0 \
        & = (not "bad") and S = (not "bad") \
        & = "states where not both green" \
    Z_2 & = (not "bad") and op("AX") Z_1 \
        & = (not "bad") and "all successors also satisfy" (not "bad")
  $

  If the transition relation is correctly designed (never transitions to both-green state), then $Z_2 = Z_1$ and the property holds.

  *Step 3: Check initial states*

  If $I subset.eq Z_"final"$, property is verified #YES

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

  Using $op("AF") phi = mu Z. thin phi or op("AX") Z$:  $ Z_0 & = emptyset \
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

  Using $op("AG") phi = nu Z. thin phi and op("AX") Z$:

  $
    W_0 & = S \
    W_1 & = phi_"rr" and op("AX") W_0 = phi_"rr" \
    W_2 & = phi_"rr" and op("AX") W_1 \
        & = phi_"rr" and "Pre"(phi_"rr") \
        & dots.v
  $

  If $I subset.eq W_"final"$, the property holds: every request gets a response. #YES

  *Counterexample scenario:*
  If the server has a bug where it sometimes ignores requests, there might be a path:

  $ s_0 ("no request") -> s_1 ("request sent") -> s_2 ("stuck, no response") -> s_2 -> s_2 -> ... $

  State $s_2$ would _not_ be in $R$ (response inevitable), so $s_1 in.not W_"final"$, and the model checker would report this path as a counterexample.
]

#note[
  *Test Your Understanding: CTL Property Puzzle*

  Consider a system where a process can be in states: `idle`, `waiting`, `running`, `done`.

  For each property below, predict: Does it hold?

  + $op("AG") op("EF") "idle"$ --- "Always eventually return to idle"
    - What if `done` is a terminal state (no transitions out)?
    - Answer: *No* --- once in `done`, we can never return to `idle`

  + $op("EF") op("AG") "done"$ --- "Eventually reach done and stay there"
    - What if `done` is terminal?
    - Answer: *Yes* --- we eventually reach `done` and remain there forever

  + $op("AG") ("waiting" => op("EF") "running")$ --- "Every wait eventually runs"
    - What if the scheduler is unfair (can ignore waiting processes)?
    - Answer: *Depends on system* --- true for fair schedulers, false otherwise

  + $op("AG") ("running" => op("EX") not "running")$ --- "Running immediately stops"
    - What does this say about the transition relation?
    - Answer: *Strong constraint* --- no state can transition to itself while running

  *Key insight:* Small differences in CTL structure express fundamentally different properties. The nesting of quantifiers and operators matters critically.
]

=== The Model Checking Workflow

Putting it all together, model checking a CTL property $phi$ proceeds as follows:

+ *Build the transition system*: Encode the system as $(S, I, T, L)$ with BDDs
+ *Parse the property*: Break $phi$ into subformulas, identify which fixpoint computations are needed
+ *Compute bottom-up*: Evaluate subformulas from atomic propositions up to the full formula, each via fixpoint iteration
+ *Check initial states*: Verify whether $I subset.eq [[ phi ]]$ (all initial states satisfy $phi$)
+ *Generate counterexample* (if needed): If property fails, extract a witness path showing the violation

Each fixpoint iteration uses image/preimage operations (Section 3) on BDD representations.
The finite state space guarantees termination.
The canonical BDD representation makes fixpoint detection trivial --- just compare node pointers.

This is the heart of symbolic CTL model checking: temporal logic reduces to iterated Boolean operations on compact representations.

== Fixpoint Characterization

The key insight for symbolic model checking is that CTL operators can be computed as fixpoints of monotone functions over sets of states.
This connection transforms temporal questions ("will $phi$ eventually hold?") into iterative set computations ("keep expanding until we include all relevant states").

Let's understand _why_ these fixpoint characterizations make sense intuitively:

- $op("EF") phi = mu Z. thin phi or op("EX") Z$: "Eventually $phi$" means either $phi$ holds now, or we can reach a state where "eventually $phi$" holds. Start with states satisfying $phi$, then add states that can reach them in one step, repeat.

- $op("EG") phi = nu Z. thin phi and op("EX") Z$: "Always $phi$" means $phi$ holds now _and_ we can stay in states where "always $phi$" holds. Start with all states, keep only those satisfying $phi$ with good successors.

- $op("E")[phi rel("U") psi] = mu Z. thin psi or (phi and op("EX") Z)$: "$phi$ until $psi$" means either $psi$ holds now (done!), or $phi$ holds now and we can reach a state where "$phi$ until $psi$" holds.

The pattern: least fixpoints ($mu$) for "eventually" properties (build up from goals), greatest fixpoints ($nu$) for "always" properties (maintain invariants).

#theorem(name: "CTL Fixpoint Characterization")[
  The CTL temporal operators have the following fixpoint characterizations:

  $
                  op("EF") phi & = mu Z. thin phi or op("EX") Z \
                  op("AF") phi & = mu Z. thin phi or op("AX") Z \
                  op("EG") phi & = nu Z. thin phi and op("EX") Z \
                  op("AG") phi & = nu Z. thin phi and op("AX") Z \
    op("E") [phi rel("U") psi] & = mu Z. thin psi or (phi and op("EX") Z) \
    op("A") [phi rel("U") psi] & = mu Z. thin psi or (phi and op("AX") Z)
  $

  where:
  - $mu Z. thin f(Z)$ denotes the least fixpoint (smallest set satisfying $Z = f(Z)$)
  - $nu Z. thin f(Z)$ denotes the greatest fixpoint (largest set satisfying $Z = f(Z)$)
]

=== Understanding Through Iteration

Let's see how $op("EF") "error"$ computes by examining the iteration:

#example(name: "Iterative Computation of EF")[
  Computing $op("EF") "error"$ asks: "Which states can possibly reach an error state?"

  Using $op("EF") "error" = mu Z. thin "error" or op("EX") Z$:

  $
    Z_0 & = emptyset quad                          &                      "(start with empty set)" \
    Z_1 & = "error" or op("EX") Z_0 = "error" quad &              "(states where error holds now)" \
    Z_2 & = "error" or op("EX") Z_1 quad           &       "(add states reaching error in 1 step)" \
    Z_3 & = "error" or op("EX") Z_2 quad           & "(add states reaching error in" <= 2 "steps)" \
  $

  This continues, expanding the set backward through the transition relation.
  At each iteration, we add states that can reach the previous set in one step.

  *Termination*: Eventually $Z_k = Z_(k+1)$ because:
  - State space is finite
  - Set sequence is monotonically increasing: $Z_0 subset.eq Z_1 subset.eq Z_2 subset.eq ...$
  - Cannot grow indefinitely

  When iteration stabilizes, we've found _all_ states that can possibly reach an error.
  If the initial state is in this set, the system has a path to error.

  The formula shows:
  - $mu Z. thin f(Z)$ denotes the *least fixpoint* (start from $emptyset$, iterate)
  - $nu Z. thin f(Z)$ denotes the *greatest fixpoint* (start from $S$, iterate)
]

=== Least Fixpoint ($mu$)

For formulas like *EF* $phi$ (exists eventually), we compute the *least fixpoint*:

#v(-1em)
#lovelace.pseudocode-list(hooks: 0.5em)[
  + $Z_0 := emptyset$
  + $Z_1 := phi or op("EX") Z_0 = phi$
  + $Z_2 := phi or op("EX") Z_1$  $quad slash.double$ (states reaching $phi$ in $<=$ 1 step)
  + $Z_3 := phi or op("EX") Z_2$  $quad slash.double$ (states reaching $phi$ in $<=$ 2 steps)
  + $dots$
]
#v(-1em)

Iteration continues until $Z_(i+1) = Z_i$ (fixpoint reached).

#example(name: "EF Computation")[
  Consider checking $op("EF") ("x" = 1)$ on the two-bit counter starting from $(0,0)$.

  Let $phi = (x = 1)$, i.e., ${(1,0), (1,1)}$ (the set of states satisfying $x = 1$).

  $
    Z_0 & = emptyset \
    Z_1 & = phi or op("EX") Z_0 = {(1,0), (1,1)} or emptyset = {(1,0), (1,1)} \
    Z_2 & = phi or op("EX") Z_1 = {(1,0), (1,1)} or "Pre"({(1,0), (1,1)}) \
        & = {(1,0), (1,1)} or {(0,0), (0,1)} = {(0,0), (1,0), (0,1), (1,1)} \
    Z_3 & = phi or op("EX") Z_2 = {(1,0), (1,1)} or "Pre"({(0,0), (1,0), (0,1), (1,1)}) \
        & = {(0,0), (1,0), (0,1), (1,1)} = Z_2
  $

  Fixpoint.
  All states satisfy $op("EF") ("x" = 1)$, meaning $x = 1$ is reachable from all states.
]

=== Greatest Fixpoint ($nu$)

For formulas like *AG* $phi$ (always globally), we compute the *greatest fixpoint*:

#v(-1em)
#lovelace.pseudocode-list(hooks: 0.5em)[
  + $Z_0 := S$  $quad slash.double$ (all states)
  + $Z_1 := phi and op("AX") Z_0 = phi$
  + $Z_2 := phi and op("AX") Z_1$  $quad slash.double$ (states where $phi$ holds and all successors in $Z_1$)
  + $dots$
]
#v(-1em)

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
  Property fails.
]

== Symbolic CTL Model Checking Algorithm

#theorem(name: "Symbolic Model Checking")[
  Given a transition system $M$ and CTL formula $phi$, we can compute the set of states satisfying $phi$ by:

  $ "SAT"(phi) = {s in S | M, s models phi} $

  as a BDD in time polynomial in $|phi|$ and the BDD sizes.
]

The algorithm proceeds by structural induction on $phi$:

/ Base case ($phi = p$):
  (given by labeling function $L$)
  $ "SAT"(p) = {s | p in L(s)} $

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
  #v(-1em)
  #lovelace.pseudocode-list(hooks: 0.5em)[
    + $Z := "SAT"(phi)$
    + *loop*
      + $Z_"new" := Z union "Pre"(Z, T)$
      + *if* $Z_"new" = Z$ *then* *break*
      + $Z := Z_"new"$
    + *return* $Z$
  ]
  #v(-1em)

/ AG operator (greatest fixpoint):
  #v(-1em)
  #lovelace.pseudocode-list(hooks: 0.5em)[
    + $Z := S$
    + *loop*
      + $Z_"new" := "SAT"(phi) inter "Pre"(Z, T)$
      + *if* $Z_"new" = Z$ *then* *break*
      + $Z := Z_"new"$
    + *return* $Z$
  ]
  #v(-1em)

#example(name: "Complete Verification")[
  Let's verify mutual exclusion in a simple protocol.

  *System*: Two processes, each with three control states

  *Property*: $op("AG") (not ("critical"_1 and "critical"_2))$

  *Steps*:
  1. Encode system as BDD transition relation
  2. Compute $"SAT"("critical"_1 and "critical"_2)$ = bad states
  3. Compute $"SAT"(op("AG") (not "bad"))$ via greatest fixpoint
  4. Check if initial state $in "SAT"(op("AG") (not "bad"))$

  If yes: property holds #YES \
  If no: counterexample exists (extract witness path)
]

=== Worked Example: Mutex Protocol Verification

Let's walk through a complete verification from start to finish.
This example demonstrates every step: system specification, BDD encoding, property formulation, algorithm execution, and result interpretation.

*The System: Peterson's Mutual Exclusion Protocol*

Peterson's algorithm solves mutual exclusion for two processes using only shared memory.
Each process has a flag and there's a shared "turn" variable.

*Process structure*:
```
Process i:
  loop forever:
    [Non-Critical Section]
    flag[i] := true          // Announce intent
    turn := j                // Give priority to other
    await (!flag[j] or turn == i)  // Wait if needed
    [Critical Section]
    flag[i] := false         // Release
```

*State Variables*:
- $"flag"_1, "flag"_2 in {0,1}$: Process flags
- $"turn" in {1,2}$: Whose turn it is
- $"pc"_1, "pc"_2 in {"idle", "want", "crit"}$: Program counters (3 states each)

*State Space Size*:
$
  |S| = 2 times 2 times 2 times 3 times 3 = 72 "states"
$

Small enough to verify by hand, but we'll use symbolic model checking to demonstrate the technique.

*Encoding as BDDs*:

We need 5 boolean variables to encode the state:
- $f_1$: flag[1]
- $f_2$: flag[2]
- $t$: turn (0 = process 1, 1 = process 2)
- $p_1^0, p_1^1$: pc[1] encoded as 2 bits (00=idle, 01=want, 10=crit)
- $p_2^0, p_2^1$: pc[2] encoded as 2 bits

Total: 7 boolean variables (5 + 2 for encoding 3-state PCs)

*Transition Relation*:

The transition relation $T(v, v')$ encodes both processes' possible moves:

For Process 1's transition from idle to want:
$
  T_1^("idle"→"want") =
  ("pc"_1 = "idle") and
  ("pc"'_1 = "want") and
  ("flag"'_1 = 1) and
  ("turn"' = 2) and
  ("unchanged"("pc"_2, "flag"_2))
$

For Process 1's transition from want to crit:
$
  T_1^("want"→"crit") =
  ("pc"_1 = "want") and
  (not "flag"_2 or "turn" = 1) and
  ("pc"'_1 = "crit") and
  ("unchanged"("flag"_1, "flag"_2, "turn"))
$

Similar transitions for Process 2, plus exit from critical section.

The complete transition relation is the disjunction of all individual transitions:
$
  T = T_1^("idle"→"want") or T_1^("want"→"crit") or T_1^("crit"→"idle") or
  T_2^("idle"→"want") or T_2^("want"→"crit") or T_2^("crit"→"idle")
$

*Property to Verify*:

*Mutual Exclusion*: Never both in critical section
$
  phi_"mutex" = op("AG") (not ("pc"_1 = "crit" and "pc"_2 = "crit"))
$

*Verification Algorithm*:

We compute the greatest fixpoint:
$
  op("AG") psi = nu Z. thin psi and op("AX") Z
$

Starting from all states, we iteratively remove states that violate $psi$ or can reach violation states.

*Step-by-Step Execution*:

- Iteration 0:
  - $Z_0 = S$ (all 72 states)
  - Start optimistically: assume property holds everywhere

- Iteration 1:
  - $"bad" = {"pc"_1 = "crit" and "pc"_2 = "crit"}$ (states violating mutual exclusion)
  - $Z_1 = Z_0 and not "bad" and op("AX") Z_0$
  - Remove bad states and their predecessors
  - $|Z_1| = 71$ (removed 1 state where both in critical section)
  - But wait --- can such a state actually be reached?

- Iteration 2:
  - $Z_2 = Z_1 and not "bad" and op("AX") Z_1$
  - Compute predecessors of removed states
  - If any predecessors exist in reachable states, remove them too
  - $|Z_2| = 71$ (no change!)

- Fixpoint Reached:
  - $Z_2 = Z_1$, so we've reached fixpoint
  - $[[ op("AG") phi_"mutex" ]] = Z_2$

*Checking the Property*:

Does the property hold from initial states?
$
  I subset.eq [[ op("AG") phi_"mutex" ]] thin ?
$

Initial state: $I = {"pc"_1 = "idle" and "pc"_2 = "idle" and "flag"_1 = 0 and "flag"_2 = 0}$

Check: Is $I subset.eq Z_2$?

*Result*: #YES --- The initial state is in the set of states satisfying the property.

*Conclusion*: Peterson's algorithm satisfies mutual exclusion!

*Key Insights from this Example*:

+ *Symbolic representation*: 72 states represented with just 7 boolean variables
+ *Fixpoint converged quickly*: Just 2 iterations to prove correctness
+ *BDD operations*: Each iteration performs image/preimage on sets, not individual states
+ *Automatic proof*: No manual reasoning needed --- the algorithm mechanically verified correctness

*What if it failed?*

If the property had failed (e.g., with a buggy protocol), the model checker would:
1. Identify $I subset.eq.not Z_k$ (initial state not in safe set)
2. Extract a path: $s_0 -> s_1 -> ... -> s_k$ where $s_k models "pc"_1 = "crit" and "pc"_2 = "crit"$
3. Present this as a counterexample showing exactly how both processes enter critical section

This complete worked example demonstrates the full power of symbolic model checking: from system specification to verified correctness, all mechanically checked by BDD operations.

== Counterexample Generation

When a property fails, the model checker should produce a *counterexample* --- a concrete execution trace demonstrating the violation.
This is one of model checking's most valuable features: not just "property fails," but "here's exactly how it fails."
Counterexamples help developers understand bugs and guide debugging efforts.

=== What is a Counterexample?

#definition(name: "Counterexample")[
  For a property $phi$ that fails from initial state $s_0$:
  - A *counterexample* is a path $pi = s_0 -> s_1 -> s_2 -> ... -> s_k$ where $s_k models not phi$
  - For liveness properties (e.g., $op("AG") op("EF") p$), may need an infinite path (lasso-shaped)
]

=== Extracting Counterexamples

During fixpoint computation, *predecessor information* can be recorded to reconstruct paths.

*Algorithm for Safety Property* $op("AG") phi$:
#v(-1em)
#lovelace.pseudocode-list(hooks: 0.5em)[
  *function* check_AG(phi):
  + $Z := S$
  + $"pred" := "empty_map"()$  $quad slash.double$ (maps state to predecessor)

  + *loop*:
    + $Z_"old" := Z$
    + $Z := "SAT"(phi) inter op("AX") (Z)$

    + // Record predecessors for states leaving Z
    + *for each* state $s$ in $Z_"old" without Z$:
      + *for each* $s'$ such that $(s, s') in T$ and $s' in.not Z$:
        + $"pred"[s'] := s$  $quad slash.double$ ($s$ can reach bad state $s'$)

    + *if* $Z = Z_"old"$ *then* *break*

  + // Check if property holds
  + *if* $"initial" subset.eq Z$:
    + *return* "Property holds"
  + *else*:
    + // Extract counterexample
    + *return* $"extract_path"("initial", "pred")$
]
#v(-1em)
#lovelace.pseudocode-list(hooks: 0.5em)[
  *function* $"extract_path"(s, "pred")$:
  + $"path" := [s]$
  + *while* $s in "pred"$:
    + $s := "pred"[s]$
    + Add $s$ to $"path"$
  + *return* $"path"$
]

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
  s₄: (crit₁, crit₂)        // P2 enters - VIOLATION
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

  The loop $s_3 -> s_4 -> s_3$ repeats forever without granting the request.
]=== Symbolic Counterexample Extraction

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

Realistic systems often require *fairness assumptions* to exclude unrealistic behaviors.
Without fairness, model checking might report spurious counterexamples corresponding to executions that, while technically possible, would never occur in practice.
For example: a scheduler that never schedules a particular process, or a communication protocol in which messages are delayed indefinitely.
Fairness constraints formalize the assumption that certain events occur infinitely often.

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

  $
    op("EF")_F phi = mu Z. thin phi or (op("EX") Z and op("EX") (op("EF")_F f_1) and ... and op("EX") (op("EF")_F f_n))
  $
]

*Intuition*: To reach $phi$ fairly, each step must be on a path that visits each $f_i$ infinitely often.

#theorem(name: "Fair AG")[
  For fairness $F = op("GF") f_1 and ... and op("GF") f_n$:

  $ op("AG")_F phi = nu Z. thin phi and op("AX") (Z or not op("EF")_F "true") $
]

*Algorithm for Fair Reachability*:
#v(-1em)
#lovelace.pseudocode-list(hooks: 0.5em)[
  *function* $"fair_EF"(phi, "fairness_constraints")$:
  + $"fair_states" := S$
  + *for each* $f$ in $"fairness_constraints"$:
    + $"fair_inf" := nu Z. thin f and op("EX") Z or op("EX") (op("EF") f)$
    + $"fair_states" := "fair_states" inter "fair_inf"$
  + $Z := phi$
  + *loop*:
    + $Z_"new" := Z union (op("Pre")(Z) inter "fair_states")$
    + *if* $Z_"new" = Z$ *then* *break*
    + $Z := Z_"new"$
  + *return* $Z$
]
#v(-1em)

#example(name: "Fair Mutual Exclusion")[
  System: Two processes with mutual exclusion protocol

  Fairness: $op("GF") "run"_1 and op("GF") "run"_2$ (both processes run infinitely often)

  Property: $op("AG") ("request"_1 => op("AF") "grant"_1)$

  - *Without fairness*: Fails (P2 can run forever)
  - *With fairness*: Holds (P1 must run infinitely often, so eventually gets grant)
]

#note[
  *Fairness Complexity*:
  - Fair CTL model checking is more expensive than standard CTL
  - Each fairness constraint adds nested fixpoint computations
  - Needed for realistic verification of concurrent systems
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

    // Property 1: AG(count < 4)  --- always true (trivial)
    let always_valid = mc.bdd.constant(true);
    assert!(mc.check(mc.always(always_valid)));
    println!("✓ Property 1: Always valid (count < 4)");

    // Property 2: AG EF(odd)  --- can always reach odd states
    let odd = mc.labels["odd"];
    let ef_odd = mc.eventually(odd);
    let ag_ef_odd = mc.always(ef_odd);
    assert!(mc.check(ag_ef_odd));
    println!("✓ Property 2: Can always eventually reach odd state");

    // Property 3: AG(even → AF odd)  --- from even, eventually odd
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

Temporal logics come in multiple flavors, each with distinct strengths.
While this document focuses on CTL, understanding how it relates to Linear Temporal Logic (LTL) --- another major temporal logic for verification --- provides valuable perspective on expressiveness trade-offs and practical verification choices.

The fundamental difference: LTL reasons about individual execution paths ("on this particular run..."), while CTL reasons about the tree of all possible executions ("on all branches..." or "on some branch...").
This leads to complementary strengths:
- LTL naturally expresses fairness and liveness properties ("infinitely often")
- CTL efficiently computes using fixpoints and handles branching-time properties ("on all paths eventually, there exists a path")

In practice, neither subsumes the other --- each can express properties the other cannot.
This section compares the two logics and explains when to use each.

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
  LTL formulas are evaluated on *infinite paths* $pi = s_0 -> s_1 -> s_2 -> ...$

  - $pi models p$ iff $p in L(s_0)$
  - $pi models op("X") phi$ iff $pi^1 models phi$ (where $pi^i$ is path starting at $s_i$)
  - $pi models phi_1 rel("U") phi_2$ iff $exists i >= 0 . thin (pi^i models phi_2 and forall j < i . thin pi^j models phi_1)$
  - $pi models op("F") phi$ iff $exists i >= 0 . thin pi^i models phi$
  - $pi models op("G") phi$ iff $forall i >= 0 . thin pi^i models phi$
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
  [• Performance is important], [• Path-specific behavior],
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

*From theory to code.*

Having established the theoretical foundations of symbolic model checking (Sections 1-6), you're probably wondering: "How do I actually _build_ this?"
This section bridges that gap.

We'll examine how the elegant theory translates into efficient software implementations.
You'll see the actual data structures (BDDs with hash consing), the algorithmic patterns (recursive operations with caching), and the design decisions that make or break performance.

The code examples use Rust and reference the `bdd-rs` library, but the principles apply to any implementation.
By the end of this section, you'll understand not just _what_ symbolic model checking does, but _how_ to build it yourself.

== BDD Representation

Binary Decision Diagrams (BDDs) are the key data structure enabling symbolic model checking.
A BDD is a directed acyclic graph representing a Boolean function.

#definition(name: "Binary Decision Diagram")[
  A BDD is a rooted, directed acyclic graph representing a Boolean function, with the following properties:
  - Each non-terminal node is labeled with a Boolean variable
  - Each non-terminal node has exactly two outgoing edges: *low* (dashed, for variable=0) and *high* (solid, for variable=1)
  - There are exactly two terminal nodes: *0* (false) and *1* (true)
  - All paths from root to terminals follow a fixed variable ordering (no variable appears twice on any path)
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
  - Result: $0 xor 1 = 1$ #YES
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

#note[
  *Visualizing BDD Evolution: The Apply Operation*

  Understanding how BDDs combine is crucial for intuition. Let's trace through applying AND to two simple BDDs.

  *Input BDDs*:
  - $f = x$: Just variable $x$ (returns 1 if $x=1$, else 0)
  - $g = y$: Just variable $y$ (returns 1 if $y=1$, else 0)

  *Operation*: Compute $h = f and g = x and y$

  *Step-by-step evolution*:

  1. *Start*: Two single-node BDDs
    ```
    f:   x → (0, 1)        g:   y → (0, 1)
    ```

  2. *Recursive descent*: Process from root (top variable $x$ in ordering $x < y$)
    - For $x=0$ case: Compute $f|_(x=0) and g = 0 and y = 0$
    - For $x=1$ case: Compute $f|_(x=1) and g = 1 and y = y$

  3. *Build result*: Create node for $x$ with:
    - Low edge ($x=0$) → terminal 0
    - High edge ($x=1$) → sub-BDD for $y$

  4. *Final BDD*:
    ```
    h: x → (0, y)
             ↓
           y → (0, 1)
    ```

  *Key insights*:
  - The algorithm traverses both input BDDs in *parallel*, following the variable ordering
  - Base cases (terminals) stop recursion immediately
  - Caching prevents recomputation: if we see $(f, g, "op")$ again, return cached result
  - The result automatically shares structure (e.g., both branches might point to same subgraph)

  *What makes this efficient?*

  Compare to truth table approach:
  - Truth table for 2 variables: 4 rows
  - Truth table for 10 variables: 1,024 rows
  - Truth table for 20 variables: 1,048,576 rows

  BDD approach:
  - Processes nodes, not truth table rows
  - With sharing, $|h| <= |f| times |g|$ nodes (often much less)
  - For 20 variables with structure: maybe 100 nodes total

  *Try this*: On paper, trace $f = (x and y)$ OR $(not x and not y)$ (equality check).
  Notice how the BDD captures the pattern without enumerating all 4 input combinations.
]

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

  This represents $x and y$ #YES
]

*Complexity*: $O(|f| times |g|)$ in worst case, but caching makes it efficient in practice.

=== Restrict Operation

The *restrict* operation fixes the value of a variable.

#definition(name: "Restrict")[
  $ "restrict"(f, x_i, b) = f[x_i <- b] $

  Returns a BDD representing $f$ with variable $x_i$ set to boolean value $b in {0,1}$.
]

*Algorithm* for Restrict operation:
// ```
// restrict(f, var, value):
//   if f is terminal:
//     return f

//   if var(f) < var:  // haven't reached var yet
//     return make_node(var(f),
//       restrict(low(f), var, value),
//       restrict(high(f), var, value))

//   if var(f) = var:  // found the variable
//     return value = 0 ? low(f) : high(f)

//   // var(f) > var: variable doesn't appear
//   return f
// ```
#v(-1em)
#lovelace.pseudocode-list(hooks: 0.5em)[
  *function* $"restrict"(f, v, b)$:
  + *if* $f$ is terminal: *return* $f$
  + *if* $"var"(f) < v$:  $quad slash.double$ have not reached $v$ yet
    + $l := "restrict"("low"(f), v, b)$
    + $h := "restrict"("high"(f), v, b)$
    + *return* $"mk_node"("var"(f), l, h)$
  + *elif* $"var"(f) = v$:  $quad slash.double$ found the variable
    + *return* $b = 0$ ? $"low"(f)$ : $"high"(f)$
  + *else*: $quad slash.double$ $"var"(f) > v$; variable doesn't appear
    + *return* $f$
]

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
  $ exists x_i . thin f = f[x_i <- 0] or f[x_i <- 1] $

  The result is true if $f$ is true for *any* value of $x_i$.
]

*Algorithm* for Existential Quantification:
#v(-1em)
#lovelace.pseudocode-list(hooks: 0.5em)[
  *function* $"exists"(f, v)$:
  + $f_0 := "restrict"(f, v, 0)$
  + $f_1 := "restrict"(f, v, 1)$
  + *return* $"apply"(f_0, f_1, or)$
]

#example[
  Given $f = x and y$, we compute $exists x . thin (x and y)$:
  - $f[x <- 0] = 0 and y = 0$
  - $f[x <- 1] = 1 and y = y$
  - Result: $0 or y = y$

  This makes sense: "there exists an $x$ such that $x and y$" is equivalent to just $y$ (choosing $x=1$ works iff $y=1$).
]

*Universal quantification* is dual:
$ forall x_i . thin f = f[x_i <- 0] and f[x_i <- 1] $

=== Compose Operation

Substitute a variable with a function:

#definition(name: "Compose")[
  $ "compose"(f, x_i, g) = f[x_i <- g] $

  Replace all occurrences of $x_i$ in $f$ with the function $g$.
]

This is used for variable renaming in model checking (e.g., $x' => x$).

*Algorithm* for Compose operation:
#v(-1em)
#lovelace.pseudocode-list(hooks: 0.5em)[
  *function* $"compose"(f, v, g)$:
  + *if* $f$ is terminal: *return* $f$
  + *if* $"var"(f) < v$:
    + $l := "compose"("low"(f), v, g)$
    + $h := "compose"("high"(f), v, g)$
    + *return* $"mk_node"("var"(f), l, h)$
  + *if* $"var"(f) = v$:
    + *return* $"ite"(g, "high"(f), "low"(f))$
  + *else*:
    + *return* $f$
]

=== ITE (If-Then-Else) Operation

The ITE (if-then-else) operation is the core BDD operation from which all others can be derived:

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

*Algorithm* for ITE operation:
#v(-1em)
#lovelace.pseudocode-list(hooks: 0.5em)[
  *function* $"ite"(f, g, h)$:
  + *if* $f = 1$: *return* $g$
  + *if* $f = 0$: *return* $h$
  + *if* $g = h$: *return* $g$
  + *if* $g = 1$ and $h = 0$: *return* $f$
  + *if* $(f, g, h)$ in cache: *return* cached result
  + $v := min("var"(f), "var"(g), "var"(h))$
  + $f_v := "cofactor"(f, v)$
  + $g_v := "cofactor"(g, v)$
  + $h_v := "cofactor"(h, v)$
  + $"low" := "ite"("low"(f_v), "low"(g_v), "low"(h_v))$
  + $"high" := "ite"("high"(f_v),"high"( g_v),"high"( h_v))$
  + $"result" := "mk_node"(v, "low", "high")$
  + $"cache"[(f, g, h)] := "result"$
  + *return* result
]

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

Reachability analysis answers the question: "Starting from the initial states, which states can the system reach through any sequence of transitions?"
This is perhaps the most fundamental analysis in model checking.

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

The algorithm is beautifully simple:
- Start with initial states
- Repeatedly compute successors and add them to the reached set
- Stop when no new states are found (fixpoint)

The loop terminates because:
+ The state space $S$ is finite
+ Each iteration either adds new states or reaches a fixpoint
+ Monotonicity: $R_i subset.eq R_(i+1)$ (the reached set only grows)
+ Eventually $R_k = S$ or we reach all reachable states

*Convergence rate*: In practice, convergence is often remarkably fast --- typically logarithmic in the diameter of the state graph.
Why? Because BDD operations work on large sets at once.
Each iteration doesn't add just one state; it might add millions.
A system with a billion reachable states might converge in 30-40 iterations.

*Key insight*: Symbolic reachability avoids enumerating individual states.
Instead of iterating over billions of states, we perform a handful of BDD operations, each manipulating sets containing millions of states.

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

#note[
  *Try This Yourself: Build a Mini Model Checker*

  Ready to implement model checking yourself? Here's a hands-on exercise using `bdd-rs`.

  *Goal*: Build a simple reachability checker for a 2-bit counter.

  *Starting code*:
  ```rust
  use bdd::BddBuilder;

  fn main() {
      // Step 1: Create BDD manager
      let mut builder = BddBuilder::new();

      // Step 2: Declare variables (present and next state)
      // TODO: Create variables x0, x0', x1, x1'

      // Step 3: Build transition relation
      // Counter increments: (x1,x0) -> (x1,x0) + 1 mod 4
      // TODO: Express as BDD formula

      // Step 4: Define initial state (0,0)
      // TODO: Create BDD for initial state

      // Step 5: Compute reachability fixpoint
      // TODO: Implement the loop from Section 4

      // Step 6: Check if all states reachable
      println!("Reachable states: check output");
  }
  ```

  *Hints*:
  1. For transition relation, think about when each bit flips:
    - Bit 0 always flips
    - Bit 1 flips when bit 0 is 1

  2. The image computation needs:
    - Conjunction with transition relation
    - Existential quantification over present variables
    - Renaming next' to present

  3. Fixpoint detection: `if new_reach == reach { break; }`

  *Expected output*: All 4 states (00, 01, 10, 11) should be reachable.

  *Solution*: Check `examples/simple.rs` in the `bdd-rs` repository for a complete implementation.

  *Extension challenges*:
  - Add a property check: "Does counter ever reach (1,1)?" (use $op("EF")$)
  - Implement deadlock detection: find states with no successors
  - Build a 3-bit counter --- how does performance scale?
]

== Performance Considerations

=== BDD Variable Ordering

The size of a BDD is *extraordinarily sensitive* to the ordering of variables.
To understand why, consider a simple function that checks if two bit-vectors are equal: $f(x_1, ..., x_n, y_1, ..., y_n) = (x_1 equiv y_1) and ... and (x_n equiv y_n)$.

With a poor ordering that groups all $x$ variables together before the $y$ variables --- say $(x_1, ..., x_n, y_1, ..., y_n)$ --- the BDD must "remember" all $n$ bits of $x$ before it can start comparing them with $y$.
This creates an exponentially large BDD with $Theta(2^n)$ nodes, making verification impossible for even moderate $n$.

But with a clever ordering that interleaves corresponding variables --- $(x_1, y_1, x_2, y_2, ..., x_n, y_n)$ --- each pair can be checked immediately and the result propagated forward.
The BDD collapses to just $O(n)$ nodes.
Same function, thousand-fold difference in representation size.

For model checking, this insight translates directly: interleave present and next-state variables.
Instead of ordering all present-state variables $x, y, z, ...$ before their next-state counterparts $x', y', z', ...$, use the pattern $x, x', y, y', z, z', ...$
This keeps related variables close together in the decision tree, reducing BDD size for typical transition relations where each next-state variable depends primarily on its corresponding present-state variable.

=== When BDDs Work Well

BDDs achieve good compression on systems with exploitable structure.
For example, a 32-bit counter (with $2^32 approx 4$ billion states) can be represented with a BDD of just a few hundred nodes.
A cache coherence protocol with $10^20$ states might need only $10^6$ BDD nodes --- a compression factor of $10^14$.
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

  - Bad ordering $(x_1, ..., x_n, y_1, ..., y_n)$: $Theta(2^n)$ nodes
  - Good ordering $(x_1, y_1, x_2, y_2, ..., x_n, y_n)$: $O(n)$ nodes

  Same function, thousand-fold difference.
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

This hash consing technique provides three important guarantees that make symbolic model checking tractable.

First, *sharing*: identical subgraphs are never duplicated.
If two different parts of a BDD reach a node representing "$x_5 = 1 -> f$", both simply point to the same shared node.
This sharing is automatic and pervasive, often reducing memory usage by orders of magnitude.

Second, *canonicity*: given a fixed variable ordering, every Boolean function has exactly one BDD representation.
Two BDDs represent the same function if and only if they are pointer-identical.
This makes equivalence checking instantaneous --- just compare pointers.
In practice, this means BDD operations can detect fixpoints in constant time, which is important for efficient model checking.

Third, *efficiency*: because of sharing, BDD operations are polynomial in the size of the BDD, not exponential in the number of variables.
Combining two BDDs with a million nodes each might produce a result with two million nodes (in the worst case), not $2^1000000$ nodes.
This polynomial scaling --- combined with aggressive sharing --- is what makes symbolic model checking tractable.

== Optimization Techniques

While the basic algorithms are conceptually straightforward, practical symbolic model checking demands sophisticated optimizations.
The difference between verifying a system in seconds versus hours --- or between success and failure --- often lies in these optimizations.
Modern model checkers incorporate numerous techniques to improve performance and scalability.
This section covers the most important optimizations used in practice.

=== Early Termination

Many fixpoint computations can terminate early when the answer is known.
This seemingly simple optimization can provide orders of magnitude speedup.

Why? Consider checking if an error is reachable.
If the error is reachable in just 5 steps, why compute the full fixpoint that might take 50 iterations?
Early termination recognizes when we've found the answer and stops immediately.

#example(name: "Early Termination in EF")[
  When checking $op("EF") phi$:

  #v(-1em)
  #lovelace.pseudocode-list(hooks: 0.5em)[
    + $Z := "SAT"(phi)$
    + *if* $Z inter "initial" != emptyset$:  $quad slash.double$ Found a path immediately!
      + *return* true
    + loop:
      + $Z_"new" := Z union "Pre"(Z)$
      + *if* $Z_"new" inter "initial" != emptyset$:  $quad slash.double$ Found a path!
        + *return* true
      + *if* $Z_"new" = Z$: *break*  $quad slash.double$ Fixpoint reached
      + $Z := Z_"new"$
    + *return* false  $quad slash.double$ No path exists
  ]

  Instead of computing the entire fixpoint, we stop as soon as we reach initial states.

  *Practical impact*: For a bug reachable in 10 steps on a system with diameter 100, this provides a 10× speedup.
  For safety-critical systems where errors should be rare (or absent), early termination when finding bugs is particularly valuable for debugging.
]

#example(name: "Early Termination in AG")[
  When checking $op("AG") phi$:
  #v(-1em)
  #lovelace.pseudocode-list(hooks: 0.5em)[
    + $Z := "SAT"(phi)$
    + *if* $"initial" not subset.eq Z$:  $quad slash.double$ Violation found immediately!
      + *return* false
    + loop:
      + $Z_"new" := Z inter "AX"(Z)$
      + *if* $"initial" not subset.eq Z_"new"$:  $quad slash.double$ Found violation!
        + *return* false
      + *if* $Z_"new" = Z$: *break*
      + $Z := Z_"new"$
    + *return* true $quad slash.double$ No violations found
  ]

  Stop as soon as we find initial states outside the safe set.
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
  #v(-1em)
  #lovelace.pseudocode-list(hooks: 0.5em)[
    + $"result" := S$
    + *for* $i := 1$ *to* $n$:
      + $"result" := "result" and T_i$
      + $"result" := "exists"("result", x_i)$  $quad slash.double$ Eliminate early
    + *return* $"rename"("result")$  $quad slash.double$ Rename all $x'_i$ to $x_i$
  ]

  Early quantification keeps BDD sizes small.
]

=== Dynamic Variable Reordering

BDD size is highly sensitive to variable ordering.
The same Boolean function can require 40 nodes with a good ordering but over 1 million nodes with a poor ordering.
This isn't just a performance issue --- it's often the difference between success and failure.

What makes an ordering "good"?
Generally, grouping related variables together.
Variables that frequently interact in the system logic should be close in the ordering to maximize structural sharing.
For example, in a circuit with multiple identical modules, the variables for each module should be grouped together.

#example(name: "Ordering Impact")[
  Function: $f(x_1, ..., x_n, y_1, ..., y_n) = (x_1 and y_1) or ... or (x_n and y_n)$

  *Bad ordering* $x_1, x_2, ..., x_n, y_1, ..., y_n$:
  - BDD size: $O(2^n)$ (exponential!)
  - For $n=20$: over 1 million nodes

  *Good ordering* $x_1, y_1, x_2, y_2, ..., x_n, y_n$:
  - BDD size: $O(n)$ (linear)
  - For $n=20$: about 40 nodes

  This $25000$-times difference illustrates the dramatic impact of variable ordering.
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
  But it's often necessary --- without it, model checking may fail entirely.
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
  Hash table mapping $("op", "arg1", "arg2") -> "result"$

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

== Limitations and Extensions

*When to use BDDs --- and when to look elsewhere.*

By now, you've seen the power of BDD-based symbolic model checking: systems with $10^20$ states verified in seconds, elegant fixpoint algorithms, practical industrial applications.
You might be tempted to think BDDs are the answer to all verification problems.

They're not.

Like any technique, BDDs have strengths and weaknesses.
Knowing when they excel --- and crucially, when they struggle --- is essential for effective verification engineering.
This isn't a limitation of the theory; it's the nature of computational complexity meeting real-world problem structure.

This section will help you develop intuition for:
1. *Recognizing* when BDDs are the right tool (and when they're not)
2. *Understanding* why certain problems resist BDD representation
3. *Choosing* alternative or complementary techniques when needed
4. *Combining* methods to get the best of multiple worlds

Let's start with the good news: understanding what makes BDDs work well.

=== When BDDs Excel

*What makes a problem "BDD-friendly"?*

Think about the compression mechanisms we discussed: sharing and reduction.
For these to work effectively, your problem needs certain characteristics.
Let's explore what those are through concrete examples.
Regular, predictable patterns in your system translate directly to compression in the BDD.
Counters, shift registers, and finite state machines --- systems built from repeating units with local connections --- compress well.
A 64-bit counter has $2^64$ states but needs only a few hundred BDD nodes to represent its transition relation.

Control logic, especially in hardware, exhibits the kind of regularity BDDs love.
Instruction decoders, protocol state machines, arbiter circuits --- these follow regular patterns with clear structure.
Symmetric protocols, where multiple processes execute identical code, create natural opportunities for sharing: the BDD for one process is automatically reused for all others.

Locality is the other key.
When transitions affect only a handful of variables --- a counter incrementing, a buffer inserting an element, a state machine changing mode --- the BDD stays compact because most variables remain unchanged and their sub-BDDs are shared.
Sparse dependency graphs, where each variable depends on few others, maintain this locality and keep BDDs manageable.

Variable ordering significantly affects BDD efficiency.
Related variables should be grouped together to exploit correlation, and present-state and next-state variables should be interleaved to minimize intermediate BDD sizes during image computation.
Following the natural ordering suggested by the system's structure often yields good results.

BDDs have proven remarkably successful for cache coherence protocols with over $10^20$ states, communication protocols like sliding window and alternating bit, hardware control units including instruction decoders and finite state machines, and mutual exclusion algorithms with multiple competing processes.

#note[
  *Success stories --- when BDDs shine:*
  - Intel's formal verification of Pentium floating-point unit (post-FDIV bug)
  - IBM's verification of cache coherence protocols for Power processors
  - Model checking of communication protocols (TCP, sliding window)
  - Verification of hardware arbiters and bus controllers
  - Safety properties in concurrent mutex algorithms

  The common thread: regular control logic with local state changes.
]

=== When BDDs Struggle

*Now for the reality check: when do BDDs fail?*

Understanding BDD limitations isn't just academic --- it can save you weeks of frustration.
If you're fighting with exploding BDD sizes, the problem might not be your implementation or variable ordering.
It might be that you've hit a fundamental limitation of the BDD representation.

Let's explore the three main problem classes where BDDs struggle, and more importantly, _why_ they struggle.

*Problem Class 1: Arithmetic-Heavy Computations*

Arithmetic operations --- multiplication, division, modulo --- are BDD's nemesis.
This isn't a minor inconvenience; it's a fundamental mismatch between the operation's structure and BDD's compression mechanisms.

Consider multiplication: $z = x times y$ for $n$-bit numbers.
Every output bit of $z$ potentially depends on _every_ input bit of both $x$ and $y$.
This creates a dense web of dependencies that destroys the locality BDDs need for compression.

#note[
  *Why multiplication is hard:* The function $z = x times y$ (for $n$-bit numbers) requires BDD with $Theta(2^n)$ nodes for most variable orderings.

  The problem: In a 32-bit multiplication, bit 31 of the result depends on all 64 input bits through the carry chain.
  The BDD must track all possible carry states, leading to exponential explosion.

  No local structure to exploit $arrow.r.double$ no compression possible.
]

*What this means in practice:*
- A 16-bit multiplier might produce a BDD with 65,000+ nodes
- A 32-bit multiplier is essentially impossible with BDDs
- If your verification problem involves significant arithmetic, BDDs are likely the wrong tool

*Problem Class 2: Irregular and Random Logic*

BDDs compress structure.
If there's no structure, there's nothing to compress.

*Hash functions* are a perfect example.
They're _designed_ to destroy regularity --- to take structured input and produce apparently random output.
That's exactly what makes them good hash functions and terrible for BDDs.
A hash function on 32-bit inputs might produce a BDD with millions of nodes because there are no patterns to exploit.

*Cryptographic operations* present similar challenges.
Encryption algorithms like AES intentionally create complex, non-linear relationships between input and output bits.
This complexity (which provides security) simultaneously prevents BDD compression.

*Random logic* --- circuits generated without regard for structure --- similarly resist BDD representation.
With no regularity to exploit, you get roughly one BDD node per distinct subcircuit, leading to very large BDDs.

*Problem Class 3: Variable Ordering Sensitivity*

Here's a frustrating reality: even for problems that _should_ work well with BDDs, choosing a poor variable ordering can make them fail catastrophically.

#example(name: "Variable Ordering Sensitivity")[
  Consider checking bit-wise equality:
  $
    f(x_1, y_1, ..., x_n, y_n) = (x_1 equiv y_1) and ... and (x_n equiv y_n)
  $

  With poor ordering $(x_1, ..., x_n, y_1, ..., y_n)$, the BDD requires $Theta(2^n)$ nodes.
  The problem: when processing $x_i$, the BDD must \"remember\" its value until reaching $y_i$ much later.
  All possible assignments to intermediate variables $x_(i+1), ..., x_n$ must be tracked, causing exponential blowup.

  With optimal ordering $(x_1, y_1, x_2, y_2, ..., x_n, y_n)$, the BDD needs only $O(n)$ nodes.
  Here, each pair $(x_i, y_i)$ can be resolved immediately: the BDD branches to 1 if $x_i = y_i$, and to 0 otherwise.
  No intermediate state tracking is necessary.

  This exponential difference --- from $Theta(2^n)$ to $O(n)$ --- illustrates why variable ordering is critically important.
  Finding optimal orderings is NP-complete, but heuristics based on system structure often work well in practice.

  *The lesson:* For structured problems, good heuristics find good orderings.
  For irregular problems, even the best heuristics may fail, and you might watch your BDD sizes explode from thousands to millions of nodes with seemingly minor reorderings.
]

=== Troubleshooting Guide: When BDDs Explode

*Practical debugging strategies for BDD blowup.*

You're running model checking and suddenly: "Out of memory" or "BDD size exceeded 10 million nodes."
What now? Here's a systematic debugging approach.

*Symptom 1: BDD Sizes Grow Without Bound*

- Possible causes:
  - Poor variable ordering
  - Arithmetic operations in your model
  - Irregular transition structure

- Debugging steps:
  + *Profile BDD operations*: Which operation creates the largest BDD?
    - Log BDD sizes after each operation
    - Identify the culprit: transition relation build? Image computation? Property check?

  + *Check variable ordering*:
    - Are present/next variables interleaved? (Should be: $x, x', y, y'$, not $x, y, x', y'$)
    - Are related variables grouped? (Cache index bits should be consecutive)
    - Try manual reordering based on system structure

  + *Examine transition relation*:
    - Is $T(v, v')$ huge even before model checking?
    - If so: Try partitioned transition relations (split into $T_1 and T_2 and ...$)
    - Use early quantification in image computation

  + *Look for arithmetic*:
    - Does your model include multiplication, division, modulo?
    - If yes: Consider abstracting arithmetic away (predicate abstraction)
    - Or switch to SAT-based model checking

*Symptom 2: Fixpoint Computation Never Converges*

- Possible causes:
  - Bug in transition relation (livelock)
  - Property is actually infinite (liveness without fairness)
  - BDDs too large to iterate effectively

- Debugging steps:
  + *Check for termination*:
    - Add iteration limit: stop after 100 iterations
    - Log how many new states each iteration adds
    - If adding states linearly forever: likely a bug

  + *Verify transition relation*:
    - Print a few example transitions
    - Check: Does every state have at least one successor?
    - Look for unintended non-determinism

  + *Simplify the property*:
    - Try simpler property first (e.g., $op("EF") "error"$ before complex $op("AG") op("EF")$)
    - Check if problem is with model or property

  + *Use bounded model checking*:
    - Instead of full fixpoint, check depth-limited: "Can error be reached in 50 steps?"
    - If BMC finds nothing, gradually increase bound

*Symptom 3: Dynamic Reordering Takes Forever*

- Possible causes:
  - Reordering triggered too frequently
  - BDD already very large when reordering starts
  - No good ordering exists (irregular structure)

- Debugging steps:
  + *Adjust reordering parameters*:
    - Increase threshold: reorder less frequently
    - Use cheaper heuristics (window permutation instead of sifting)
    - Disable reordering initially to see if it helps or hurts

  + *Force a good initial ordering*:
    - If you know system structure, specify ordering manually
    - Use domain knowledge: interleave related variables
    - Once set, disable dynamic reordering

  + *Accept BDD limitations*:
    - If reordering doesn't help: problem might not be BDD-friendly
    - Try alternative techniques (see next section)

*Symptom 4: Memory Exhausted Despite Small State Space*

- Possible causes:
  - Intermediate BDDs much larger than final result
  - Garbage collection not running
  - Cache taking too much memory

- Debugging steps:
  + *Improve garbage collection*:
    - Call GC more frequently
    - Use reference counting to identify dead nodes
    - Clear operation caches between phases

  + *Reduce intermediate BDD sizes*:
    - Use early quantification: $exists x . (f and g)$ often smaller than $(exists x . f) and g$
    - Partition operations: compute in smaller pieces
    - Minimize simultaneous live BDDs

  + *Check for leaks*:
    - Are you keeping references to old BDDs?
    - Clear caches after major operations
    - Profile memory usage over time

*Quick Decision Tree*:

```
BDD exploding?
├─ Transition relation huge?
│  ├─ YES → Try partitioning, early quantification
│  └─ NO → Continue
├─ Contains arithmetic (multiply/divide)?
│  ├─ YES → Switch to SAT/BMC or abstract arithmetic
│  └─ NO → Continue
├─ Fixpoint not converging?
│  ├─ YES → Check for bugs, try BMC with bounds
│  └─ NO → Continue
└─ Reordering helps?
   ├─ YES → Use dynamic reordering, tune thresholds
   ├─ NO → Try manual ordering or alternative method
   └─ UNKNOWN → Profile and measure!
```

*The Golden Rule*:

If you've tried reordering, partitioning, and abstraction, and BDDs still explode --- *it's time to try a different approach*.
BDDs are powerful but not universal.
Knowing when to switch techniques is as important as knowing how to optimize them.

=== Practical Guidance: Choosing Your Verification Approach

*A decision guide for verification engineers.*

You have a system to verify.
Should you use BDDs?
Let's work through a decision process.

*Step 1: Characterize Your System*

Ask yourself these questions:

#table(
  columns: 2,
  align: (left, left),
  stroke: (x, y) => if y == 0 { (bottom: 0.8pt) },
  table.header([*Question*], [*BDD-Friendly Answer*]),

  [What dominates: control or arithmetic?], [Control (state machines, protocols)],

  [Are there regular patterns?], [Yes (counters, repeating structures)],

  [How many variables change per transition?], [Few (local state changes)],

  [Are there identical components?], [Yes (symmetry opportunities)],

  [Do you have arithmetic operations?], [Only simple (add/subtract, not multiply)],

  [Is the logic structured or random?], [Structured (designed, not random)],
)

*Step 2: Make Your Decision*

/ BDDs are likely a good fit if:
  - You answered "BDD-friendly" to most questions above
  - Your system is hardware control logic, protocols, or state machines
  - You're verifying CTL properties (especially safety)
  - You need complete reachability analysis

/ Consider alternatives if:
  - Heavy arithmetic dominates your system
  - Logic is irregular or random
  - You're primarily hunting for bugs (not proving correctness)
  - Variable ordering seems intractable

/ Consider hybrid approaches if:
  - Your system mixes control (BDD-friendly) and datapath (arithmetic-heavy)
  - Some components are structured, others irregular
  - You want robustness across different problem instances

*Step 3: Practical Strategies*

If using BDDs:
- Start with natural variable ordering (following system structure)
- Monitor BDD sizes during development --- if they explode, investigate why
- Use dynamic reordering, but understand it's not magic
- Consider abstracting arithmetic (e.g., treat counter as symbolic value, not bit-vector)
- Profile your operations: which ones create large intermediate BDDs?

If BDDs struggle:
- Don't fight it --- recognize when you've hit a fundamental limitation
- Try SAT/BMC for bug-finding (often faster, handles arithmetic better)
- Use IC3/PDR for safety properties (avoids variable ordering issues)
- Consider abstraction-refinement (CEGAR) to reduce state space
- Employ hybrid methods: BDDs for control, alternatives for datapath

If unsure:
- Start simple: try BDDs on a small version of your problem
- Measure and iterate: does BDD size scale reasonably as you grow the system?
- Have a backup plan: don't commit fully to BDDs until you're confident
- Consult the literature: has similar verification been done? What worked?

#note[
  *A pragmatic perspective:*

  In 20+ years of industrial verification, patterns have emerged:
  - BDDs dominate for hardware control verification (protocols, state machines)
  - SAT/BMC is preferred for finding bugs in datapaths and arithmetic-heavy designs
  - IC3/PDR has largely replaced BDDs for safety properties in hardware
  - Hybrid approaches (combining multiple techniques) are increasingly common

  The best verification engineers maintain a toolkit of techniques and choose pragmatically based on problem characteristics.
  Understanding when and why each technique works is more valuable than mastering any single approach.
]

=== Complementary Techniques

Modern verification has moved beyond relying solely on any single technique, instead assembling a diverse toolkit where each method excels in its natural domain.

#definition(name: "SAT-Based Model Checking")[
  SAT-based model checking encodes verification problems as propositional satisfiability instances.
  Modern SAT solvers based on Conflict-Driven Clause Learning (CDCL) excel at handling datapaths, arithmetic circuits, and irregular logic.
  They scale to millions of variables and dynamically learn problem structure during solving, adapting their strategy to the specific instance.

  *Key advantage*: No canonical representation needed --- solvers work directly with clauses.

  *Key limitation*: Properties must be bounded or abstracted since SAT works on finite propositional formulas.
]

*Bounded Model Checking (BMC)* emerged as a pragmatic compromise between completeness and effectiveness.
Rather than attempting unbounded verification, BMC checks whether a property can be violated within $k$ steps:
$
  I(s_0) and T(s_0, s_1) and T(s_1, s_2) and ... and T(s_(k-1), s_k) and not P(s_0, ..., s_k)
$

This formula is satisfiable if and only if a counterexample of length $<=k$ exists.

#example(name: "BMC vs. Symbolic Model Checking")[
  Consider verifying a mutex property on a system with $10^6$ reachable states:

  / BDD approach: Must compute full reachable state set (potentially expensive variable ordering, large intermediate BDDs)
  / BMC with $k=20$: Checks only paths of length 20, typically finds bugs quickly if they exist at shallow depth
  / Trade-off: BMC is incomplete but highly effective --- Intel reports that 90%+ of bugs are found at depth < 50
]

*Property Directed Reachability (IC3/PDR)* represents an algorithmic advance in model checking.
Instead of building BDDs or unrolling circuits, IC3 incrementally constructs inductive invariants represented as CNF clauses.

#example(name: "IC3 Core Algorithm")[
  IC3 maintains a sequence of formula frames $F_0, F_1, ..., F_k$ where each $F_i$ over-approximates states reachable in at most $i$ steps.

  *Initialization*: Let $F_0 = I$, and $F_1 = ... = F_k = top$ for some initial $k$

  *Algorithm*:

  + *Check base case*: If $I and not P$ is satisfiable, return counterexample

  + *Main loop*: For each frame $i$:
    - Try to find state $s$ in $F_i$ that can reach $not P$ in one step
    - If found: Try to block $s$ by adding clause $c$ to earlier frames
    - If blocking fails at $F_0$: Real counterexample found
    - If all states blocked: Try to push clauses forward

  + *Convergence check*: If $F_i = F_(i+1)$, then $F_i$ is inductive invariant $arrow.r.double$ property holds

  The key insight: IC3 works backward from bad states, learning clauses that block dangerous regions.
  These learned clauses form an inductive invariant without ever computing the full reachable state set.
]

IC3 has largely displaced BDDs in industrial hardware verification for safety properties, though BDDs retain advantages for liveness and CTL model checking.

*Counterexample-Guided Abstraction Refinement (CEGAR)* tackles the problem from a different angle entirely.
The key insight: start with a coarse abstraction using only a subset of variables, then refine only when necessary.

#example(name: "CEGAR in Action")[
  Consider a system with 100 boolean variables.

  + *Iteration 1*: Abstract to 10 variables → Model check → Find counterexample
    - *Analysis*: Counterexample is spurious (impossible in system due to missing variable `x_23`)

  + *Iteration 2*: Add `x_23` to abstraction (now 11 variables) → Model check → Find counterexample
    - *Analysis*: Counterexample is still spurious (needs `x_47`)

  + *Iteration 3*: Add `x_47` (now 12 variables) → Model check → Property verified!

  + *Result:* Verified using only 12 variables instead of all 100.
]

*Hybrid approaches* recognize that different system components favor different techniques.
A processor verification might use BDDs for control logic (instruction decoder, pipeline controller) while employing SAT for the datapath (ALU, register file).
Portfolio solvers take this further, running multiple techniques in parallel and reporting the first to finish, effectively hedging against the unpredictability of which method will work best.

=== Choosing the Right Technique

*A quick reference guide.*

Now that you've seen the full landscape of verification techniques, how do you choose?
Here's a practical comparison to guide your decisions:

#table(
  columns: 4,
  align: (left, left, left, left),
  stroke: (x, y) => if y == 0 { (bottom: 0.8pt) },
  table.header([*Technique*], [*Best For*], [*Strengths*], [*Limitations*]),

  [BDDs],
  [Regular control logic, protocols],
  [Canonical form, complete reachability, CTL model checking],
  [Variable ordering sensitivity, poor for arithmetic],

  [SAT/BMC],
  [Bug-finding, irregular logic, datapaths],
  [Handles arithmetic, scales to millions of vars, fast],
  [Incomplete (bounded), no canonical form],

  [IC3/PDR],
  [Safety properties, hardware verification],
  [Complete, no ordering issues, learns invariants],
  [Limited to safety, complex to implement],

  [CEGAR],
  [Large systems, infinite-state],
  [Scales via abstraction, automatic refinement],
  [Overhead from spurious counterexamples],
)

*Quick decision rules:*

/ Choose BDDs when:
  System structure is regular, transitions are local, and you need complete reachability or CTL verification.
  Classic applications: protocol verification, hardware control logic, problems requiring canonical representation for equivalence checking.

/ Choose SAT/BMC when:
  Structure is irregular, arithmetic is involved, or you're hunting for bugs rather than proving correctness.
  The 90%+ bug detection rate at shallow depths makes BMC incredibly practical despite incompleteness.

/ Choose IC3/PDR when:
  Verifying safety properties and BDD variable ordering is problematic, or when you need complete unbounded verification without explicit bounds.
  The clause-based representation sidesteps variable ordering entirely while maintaining completeness.

/ Choose CEGAR when:
  Your system is too large for direct verification, and you can identify which variables matter most.
  Starting coarse and refining only as needed makes CEGAR valuable for managing complexity when the abstraction process can proceed automatically.

*In the real world:*

The most sophisticated verification efforts _combine_ multiple techniques.
Modern tools make pragmatic choices based on problem characteristics:
- Use BDDs for control logic
- Use SAT for datapaths and arithmetic
- Use CEGAR to manage overall complexity
- Run multiple approaches in parallel (portfolio)

#note[
  *The verification engineer's perspective:*

  Choosing verification techniques is part science (understanding complexity and problem structure) and part art (recognizing patterns from experience).

  Start with the technique that matches your problem's dominant characteristics.
  Monitor progress --- if BDD sizes explode or SAT queries time out, understand _why_ and adjust.
  Don't be dogmatic: the goal is verification, not commitment to a particular technique.

  The verification landscape continues to evolve.
  Techniques that seemed impractical decades ago --- SAT solving on millions of variables, IC3's inductive invariant synthesis --- now form the backbone of industrial verification.
  Your toolkit should evolve too.
]

= Conclusion: From Theory to Practice

*Bringing it all together.*

This document has taken you on a journey through symbolic model checking with BDDs --- from the fundamental idea of representing sets as Boolean functions, through the mechanics of image computation and fixpoint iteration, to practical algorithms and real-world applications.

Let's reflect on what makes this technique remarkable.

== The Elegant Theory

The theoretical foundation is beautifully simple:
- *Temporal logic* reduces to *fixpoint computation*
- *Fixpoint computation* reduces to *iterated Boolean operations*
- *Boolean operations* have *efficient BDD implementations*

This chain of reductions transforms an intractable problem (exhaustive exploration of $10^20$ states) into practical verification that completes in seconds.

The key insights:
1. *Symbolic representation supersedes enumeration*: Describe state sets with Boolean formulas rather than listing individual states
2. *Image/preimage operations*: Compute successors and predecessors for millions of states simultaneously
3. *Fixpoint iteration*: CTL operators reduce to iterative set expansion/contraction until stabilization
4. *BDD compression*: Regular structure in systems translates to exponential compression through sharing and reduction

== The Practical Reality

But theory alone isn't enough.
Successful verification requires understanding:

*When BDDs excel:*
- Regular control logic (state machines, protocols)
- Local state transitions
- Hardware verification
- CTL property checking

*When BDDs struggle:*
- Arithmetic-heavy computations (multiplication, division)
- Irregular logic (hash functions, cryptography)
- Variable ordering sensitivity
- Dense dependencies

*What makes the difference:*
- Problem structure (regularity vs. randomness)
- Variable ordering (can change 40 nodes to 1M nodes)
- Hybrid approaches (BDDs for control, SAT for datapath)
- Knowing when to try alternatives

== The Real-World Impact

Symbolic model checking transformed verification from theoretical exercise to industrial practice:

*Success stories:*
- Intel's formal verification (post-FDIV Pentium bug)
- IBM's cache coherence protocol verification
- Hardware verification (processors, buses, controllers)
- Protocol verification (TCP, communication protocols)
- Safety-critical systems (medical devices, automotive, avionics)

The technique has found real bugs in deployed systems --- defects that escaped years of testing, bugs that would have caused system failures, data corruption, or security vulnerabilities in production.

== Your Path Forward: Using bdd-rs

The `bdd-rs` library provides the core building blocks:
- BDD data structure with hash consing (canonical representation)
- Operation caching (efficiency)
- Clean API for composing operations

What you build on top depends on your verification challenges:
- CTL model checker?
- Reachability analyzer?
- Equivalence checker?
- Custom domain-specific verifier?

*The journey from theory to working implementation:*

1. *Understand your system*: Is it regular? Control-dominated? Arithmetic-heavy?
2. *Choose encodings wisely*: Variable ordering matters critically
3. *Implement core algorithms*: Start with image, fixpoint, basic CTL
4. *Add optimizations incrementally*: Early termination, conjunction scheduling, caching
5. *Measure and iterate*: Monitor BDD sizes, identify bottlenecks
6. *Know your limits*: Recognize when BDDs struggle; have alternatives ready

== The Art and Science

Verification is part science (understanding complexity, problem structure) and part art (recognizing patterns from experience).

*Scientific principles:*
- Complexity bounds (what's theoretically possible)
- Algorithm correctness (formal guarantees)
- Performance characteristics (when techniques scale)

*Practical art:*
- Recognizing problem patterns
- Choosing appropriate techniques
- Debugging exploding BDD sizes
- Balancing completeness vs. pragmatism

== Final Thoughts

Symbolic model checking with BDDs represents a remarkable success story: elegant theory yielding practical impact.
The simple idea of manipulating sets symbolically enabled verification of systems once thought intractable.

As you implement verification tools using `bdd-rs`, remember:
- *The algorithms are straightforward* --- fixpoint iteration is just a loop
- *The magic is in the representation* --- BDDs compress exponential into polynomial
- *Success depends on problem structure* --- understand the relationship between your system and BDD performance
- *Be pragmatic* --- use BDDs where they excel, alternatives where they don't
- *Keep learning* --- verification techniques continue to evolve

The goal isn't mastering BDDs specifically --- it's effective verification.
BDDs are a powerful tool in your toolkit, but only one tool.
Understanding when and how to apply each technique is the mark of a skilled verification engineer.

*Welcome to the world of formal verification. Build confidently, verify rigorously, and may your BDDs stay compact.*
