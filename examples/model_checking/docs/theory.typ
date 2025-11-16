#import "@preview/cetz:0.2.2": canvas, draw

#set document(title: "Symbolic Model Checking: Theory and Implementation")
#set page(numbering: "1", number-align: center)
#set text(size: 11pt)
#set par(justify: true)

// Custom theorem environments
#let theorem(body, name: none) = block(
  fill: rgb("#e8f4f8"),
  inset: 10pt,
  radius: 4pt,
  [
    #text(weight: "bold")[
      Theorem#if name != none [ (#name)]
    ]: #body
  ],
)

#let definition(body, name: none) = block(
  fill: rgb("#f0f0f0"),
  inset: 10pt,
  radius: 4pt,
  [
    #text(weight: "bold")[
      Definition#if name != none [ (#name)]
    ]: #body
  ],
)

#let example(body, name: none) = block(
  fill: rgb("#fffacd"),
  inset: 10pt,
  radius: 4pt,
  [
    #text(weight: "bold")[
      Example#if name != none [ (#name)]
    ]: #body
  ],
)

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

#outline(indent: auto, depth: 2)

#pagebreak()

= Introduction

Model checking is an automated formal verification technique that exhaustively explores all possible behaviors of a system to verify whether it satisfies specified properties.
Unlike testing, which examines selected execution scenarios, or theorem proving, which requires manual proof construction, model checking provides a fully automated "push-button" approach to verification.

== The Challenge: State Explosion

The fundamental challenge in model checking is the *state explosion problem*.
Consider a system with $n$ boolean variables:

$ |S| = 2^n $

where $S$ is the set of all possible states.
For even modest systems:
- 10 variables $=>$ 1,024 states
- 20 variables $=>$ 1,048,576 states
- 30 variables $=>$ 1,073,741,824 states
- 100 variables $=>$ $1.27 times 10^30$ states (impossible to enumerate!)

Traditional *explicit-state* model checking stores each state individually, making verification infeasible for systems with more than a few million states.

== The Solution: Symbolic Representation

*Symbolic model checking* uses Boolean formulas to represent sets of states rather than enumerating them individually.
The key insight:

#definition[
  A set of states $S subset.eq {0,1}^n$ can be represented by its *characteristic function* $chi_S : {0,1}^n arrow.r {0,1}$ where:
  $
    chi_S (s) = cases(
      1 "if" s in S,
      0 "if" s in.not S
    )
  $
]

Using *Binary Decision Diagrams (BDDs)*, we can represent these characteristic functions compactly and perform operations efficiently.

#example(name: "Even Numbers")[
  Consider representing all even numbers from 0 to $2^100 - 1$:

  - *Explicit*: Store $2^99$ numbers (impossible!)
  - *Symbolic*: Encode the formula "last bit = 0" (tiny BDD!)

  The characteristic function is simply $chi_"even" (x_0, x_1, ..., x_99) = overline(x_0)$ where $x_0$ is the least significant bit.
]

This dramatic compression makes it possible to verify systems with $10^20$ states or more.

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
    [*State*], [*x*], [*y*], [*Value*],
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
  - $L: S arrow.r 2^("AP")$ is a *labeling function* mapping states to sets of atomic propositions

  We write $s arrow.r s'$ to denote $(s, s') in T$, meaning "there is a transition from state $s$ to state $s'$".
]

#example(name: "Toggle System")[
  A simple system with one boolean variable $x$ that toggles between 0 and 1:

  #table(
    columns: 4,
    [*Component*], [*Symbolic*], [*Explicit*], [*Meaning*],
    [$S$], [${0,1}$], [${s_0, s_1}$], [Two states],
    [$I$], [$overline(x)$], [${s_0}$], [Start with $x=0$],
    [$T$], [$x xor x'$], [${(s_0,s_1), (s_1,s_0)}$], [Toggle],
    [$L$], [$L(s_0) = emptyset$, $L(s_1) = {"on"}$], [], [Label when $x=1$],
  )

  State diagram:
  ```
       ┌───────┐         ┌───────┐
  ────>│  s₀   │────────>│  s₁   │
       │ x=0   │         │ x=1   │
       └───────┘<────────└───────┘
           ↑                 │
           └─────────────────┘
  ```
]== Present and Next State Variables

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
  - $(0,0) arrow.r (1,0)$ (0→1)
  - $(1,0) arrow.r (0,1)$ (1→2)
  - $(0,1) arrow.r (1,1)$ (2→3)
  - $(1,1) arrow.r (0,0)$ (3→0)

  *Transition relation*: How do we encode this symbolically?

  Observe the pattern:
  - $y$ always flips: $y' = overline(y)$
  - $x$ flips when $y = 1$: $x' = x xor y$

  Therefore:
  $ T(x, y, x', y') = (x' equiv x xor y) and (y' equiv overline(y)) $


  where $equiv$ denotes logical equivalence (XNOR).

  State diagram:
  ```
           ┌───────────┐
           │   (0,0)   │<───────────┐
      ────>│   val=0   │            │
           └───────────┘            │
                 │                  │
                 │ y→1              │ y→0, x→0
                 ↓                  │
           ┌───────────┐      ┌───────────┐
           │   (1,0)   │─────>│   (1,1)   │
           │   val=1   │ y→0  │   val=3   │
           └───────────┘ x→0  └───────────┘
                 │                  ↑
                 │ y→1              │
                 │                  │
                 ↓                  │
           ┌───────────┐            │
           │   (0,1)   │────────────┘
           │   val=2   │
           └───────────┘
  ```
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

+ *Conjunction*: $S(v) and T(v, v')$ — combine current states with transition relation
+ *Existential quantification*: $exists v . (S(v) and T(v, v'))$ — eliminate present-state variables
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
  $ (overline(x) and x')[x arrow.r 0] or (overline(x) and x')[x arrow.r 1] = (1 and x') or (0 and x') = x' $

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

= CTL Model Checking

CTL (Computation Tree Logic) is a temporal logic for specifying properties about how systems evolve over time. It allows us to express complex requirements about system behavior in a precise mathematical way.

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
    phi & ::= p | top | bot | not phi | phi and psi | phi or psi | phi arrow.r.double psi \
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
    M, s models "AX" phi & <==> forall s' : (s, s') in T arrow.r.double M, s' models phi \
    M, s models "EF" phi & <==> exists pi = s_0, s_1, ... : s_0 = s and exists i >= 0 : M, s_i models phi \
    M, s models "AF" phi & <==> forall pi = s_0, s_1, ... : s_0 = s arrow.r.double exists i >= 0 : M, s_i models phi
  $
]

== Properties: Safety and Liveness

CTL formulas typically express either *safety* or *liveness* properties.

#definition(name: "Safety Property")[
  A *safety property* asserts that "something bad never happens":

  $ "AG"(not "bad") $

  This means: on all paths, globally (always), the bad condition does not hold.
]

#example(name: "Safety Properties")[
  - *Mutual exclusion*: $"AG"(not ("critical"_1 and "critical"_2))$ \
    "Two processes are never simultaneously in the critical section"

  - *No buffer overflow*: $"AG"("count" <= "capacity")$ \
    "The buffer count never exceeds capacity"

  - *No division by zero*: $"AG"("divisor" != 0)$ \
    "The divisor is always non-zero"
]

#definition(name: "Liveness Property")[
  A *liveness property* asserts that "something good eventually happens":

  $ "AF"("good") $

  This means: on all paths, eventually (in the future), the good condition holds.
]

#example(name: "Liveness Properties")[
  - *Termination*: $"AF"("terminated")$ \
    "The process eventually terminates"

  - *Request-response*: $"AG"("request" arrow.r.double "AF" "response")$ \
    "Every request is eventually responded to"

  - *Fair scheduling*: $"AG"("waiting" arrow.r.double "AF" "granted")$ \
    "Every waiting process is eventually granted access"
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
  The function $f(x,y) = x xor y$ can be represented as:

  ```
          x
         / \
        /   \
       y     y
      / \   / \
     0   1 1   0
  ```

  Reading: If $x=0$, go left to node $y$.
  If then $y=0$, result is 0; if $y=1$, result is 1.
  Hence $x=0 and y=1 arrow.r 1$ (which equals $0 xor 1 = 1$) ✓
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

*Symbolic representation*: By encoding sets of states as Boolean formulas (BDDs) rather than enumerating them explicitly, we can handle systems with $10^20$ or more states—far beyond what explicit-state methods can manage.

*Image and preimage operations*: These fundamental operations—computing successors and predecessors symbolically—are the building blocks for all reachability analysis and temporal logic model checking.

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

While BDDs are powerful, they have limitations:

*Variable ordering sensitivity*: Poor ordering can cause exponential blowup.
Finding optimal orderings is NP-complete, though heuristics often work well in practice.

*Arithmetic operations*: Operations like multiplication produce large BDDs, limiting applicability to purely boolean or control-dominated systems.

*Unbounded data*: BDDs handle finite state spaces.
For infinite-state systems, abstractions or alternative techniques (predicate abstraction, interpolation) are needed.

Modern extensions address these limitations:
- *SAT-based methods*: Complementary to BDDs, excel where BDDs struggle
- *Bounded model checking*: Unroll transition relation to fixed depth, check with SAT
- *IC3/PDR*: Incremental algorithm computing inductive invariants
- *Abstraction-refinement*: Start with coarse abstraction, refine on counterexamples

== Historical Context

BDDs were introduced by Bryant in 1986 as a data structure for Boolean functions.
The application to model checking (by Burch et al., 1990; McMillan, 1993) transformed formal verification from a niche academic pursuit to an industrial practice.

The "10^20 states and beyond" milestone (McMillan, 1993) demonstrated that symbolic methods could verify real hardware designs—systems that were utterly intractable for explicit-state methods.
This breakthrough established model checking as a mainstream verification technique.

Today, every major hardware company uses BDD-based verification tools, and the techniques have spread to software, protocols, and cyber-physical systems.

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

The techniques described in this document—BDDs, image/preimage operations, fixpoint computation, CTL model checking—form the foundation for modern formal verification.
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
