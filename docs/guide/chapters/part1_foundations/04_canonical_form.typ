#import "../../theme.typ": *

= Canonical Form and Uniqueness <ch-canonicity>

Canonicity is the property that sets BDDs apart from other Boolean function representations.
A representation is *canonical* if each function has exactly one representation.
For ROBDDs with a fixed variable ordering, this property holds, enabling constant-time equivalence checking and many other efficient operations.

This chapter proves the canonicity theorem and explores its far-reaching implications.

== The Canonicity Theorem

We state the central theorem precisely before proving it.

#theorem(title: "Canonicity of ROBDDs")[
  Let $pi$ be a fixed variable ordering on ${x_1, ..., x_n}$.
  Then:
  + Every Boolean function $f : BB^n -> BB$ has a unique ROBDD with respect to $pi$
  + Two ROBDDs (with the same ordering) are structurally identical if and only if they represent the same function

  Equivalently: there is a bijection between Boolean functions on $n$ variables and ROBDDs with ordering $pi$.
]

This theorem has two remarkable consequences:
- *Equivalence checking is trivial*: $f equiv g$ if and only if their ROBDDs are identical
- *Satisfiability is trivial*: $f$ is satisfiable if and only if its ROBDD is not the $0$-terminal

Let us build toward the proof.

== Proof of Canonicity

The proof proceeds by structural induction on the number of variables the function depends on.
We show that the reduction rules uniquely determine the ROBDD structure.

=== Preliminaries

#definition(title: "Essential Variables")[
  A variable $x_i$ is *essential* to function $f$ if $f|_(x_i=0) != f|_(x_i=1)$, i.e., the function value changes when $x_i$ changes (for some assignment to other variables).
]

A function depends only on its essential variables.
Non-essential variables can be ignored in the ROBDD (this is what the "no redundant tests" rule achieves).

#lemma(title: "Shannon Expansion Uniqueness")[
  Every Boolean function $f$ can be uniquely decomposed as:
  $
  f = overline(x_i) dot f|_(x_i=0) + x_i dot f|_(x_i=1)
  $
  where $f|_(x_i=0)$ and $f|_(x_i=1)$ are unique subfunctions not depending on $x_i$.
]

#proof[
  The cofactors $f|_(x_i=0)$ and $f|_(x_i=1)$ are defined pointwise and thus unique.
  The expansion follows from the definition of Boolean functions.
]

=== Base Case: Constant Functions

For constant functions $f equiv 0$ and $f equiv 1$:
- They have no essential variables
- Their ROBDD is the respective terminal node ($0$ or $1$)
- These are trivially unique

=== Inductive Step

Assume the theorem holds for all functions with fewer than $k$ essential variables.
Consider a function $f$ with $k$ essential variables.

Let $x_i$ be the smallest essential variable according to ordering $pi$.
By Shannon expansion:
$
f = overline(x_i) dot f|_(x_i=0) + x_i dot f|_(x_i=1)
$

Since $x_i$ is essential, $f|_(x_i=0) != f|_(x_i=1)$.
Both cofactors have at most $k-1$ essential variables (they don't depend on $x_i$).

By the induction hypothesis, $f|_(x_i=0)$ and $f|_(x_i=1)$ have unique ROBDDs, call them $B_0$ and $B_1$.

The ROBDD for $f$ must:
- Have root variable $x_i$ (the smallest essential variable)
- Have low child $B_0$ (unique by induction)
- Have high child $B_1$ (unique by induction)
- Have $B_0 != B_1$ (since $x_i$ is essential)

The "no duplicate nodes" rule ensures this node is unique.
Therefore, the ROBDD for $f$ is unique. $square$

#info-box(title: "Proof Strategy")[
  The proof shows that:
  + The root must test the first essential variable (by ordering + no redundant tests)
  + The children are uniquely determined by the cofactors (by induction)
  + The node itself is unique (by no duplicate nodes)

  Each reduction rule eliminates exactly one degree of freedom, leaving a unique representation.
]

== Consequences of Canonicity

The canonicity theorem enables several operations to be performed in constant time.

=== Equivalence Checking

#theorem(title: "O(1) Equivalence")[
  Given two ROBDDs $B_f$ and $B_g$ for functions $f$ and $g$ (with the same ordering), we can check whether $f equiv g$ in $O(1)$ time.
]

#proof[
  By canonicity, $f equiv g$ if and only if $B_f$ and $B_g$ are structurally identical.
  With hash consing (discussed below), structurally identical means pointer-equal.
  Comparing two pointers takes constant time.
]

This is extraordinary.
In contrast:
- CNF equivalence is coNP-complete
- Truth table comparison takes $O(2^n)$ time
- General circuit equivalence is coNP-complete

=== Satisfiability and Tautology

#theorem(title: "O(1) SAT and Tautology")[
  Given an ROBDD $B_f$:
  - $f$ is satisfiable if and only if $B_f != 0$
  - $f$ is a tautology if and only if $B_f = 1$

  Both checks take $O(1)$ time.
]

#proof[
  By canonicity, the only ROBDD representing the constant-false function is the $0$ terminal.
  Similarly, the only ROBDD for constant-true is the $1$ terminal.
  Checking if a BDD is a terminal is a constant-time operation.
]

#warning-box(title: "Complexity Caveat")[
  These operations are $O(1)$ *given* the BDD.
  Building the BDD may take exponential time and space.
  The complexity is shifted from query time to construction time.
]

=== Solution Counting

#theorem(title: "Linear-Time Counting")[
  Given an ROBDD $B_f$ with $|B_f|$ nodes, the number of satisfying assignments to $f$ can be computed in $O(|B_f|)$ time.
]

The algorithm traverses the BDD bottom-up, computing at each node the number of paths to the $1$ terminal, weighted by the number of variable assignments each path represents.

=== Model Enumeration

We can enumerate all satisfying assignments by traversing all paths from root to the $1$ terminal.
Each path corresponds to a (partial) assignment; variables not on the path can take any value.

== Hash Consing: Implementing Canonicity

The theoretical canonicity theorem becomes practical through *hash consing*, a technique that maintains structural sharing.

#definition(title: "Hash Consing")[
  *Hash consing* is a technique where:
  + Every unique structure is stored exactly once
  + Creating a structure returns a reference to the existing copy if one exists
  + Structural equality reduces to pointer (reference) equality
]

For BDDs, this means maintaining a *unique table* --- a hash table mapping $("var", "low", "high")$ triples to node references.

=== The Unique Table

#definition(title: "Unique Table")[
  The *unique table* is a hash map:
  $
  U : ("Var" times "Node" times "Node") -> "Node"
  $

  For any triple $(x, l, h)$, either:
  - $U(x, l, h)$ is undefined (no such node exists), or
  - $U(x, l, h) = v$ where $v$ is the unique node with $"var"(v) = x$, $"low"(v) = l$, $"high"(v) = h$
]

#algorithm(title: [mk --- Create or Find Node])[
  ```
  function mk(var, low, high):
      // Rule 1: No redundant tests
      if low = high:
          return low

      // Rule 2: No duplicate nodes
      if (var, low, high) in UniqueTable:
          return UniqueTable[(var, low, high)]

      // Create new node
      node = new Node(var, low, high)
      UniqueTable[(var, low, high)] = node
      return node
  ```
]

The `mk` function enforces both reduction rules:
- If $"low" = "high"$, no node is created (Rule 1)
- If an equivalent node exists, it is returned (Rule 2)

#insight-box[
  After every operation, the BDD manager maintains the invariant that structurally equal subgraphs are pointer-equal.
  This invariant is what makes $O(1)$ equivalence checking possible.
]

=== Implications for Operations

With hash consing:
- Creating a node is $O(1)$ amortized (hash table lookup/insert)
- Equivalence checking is $O(1)$ (pointer comparison)
- All operations that produce BDDs automatically produce reduced, canonical results

=== Per-Level vs Global Unique Tables

There are two common implementations:

*Global Unique Table*: One hash table for all nodes.
- Pro: Simple implementation
- Con: May have poor cache behavior

*Per-Level Unique Tables*: One hash table per variable level.
- Pro: Better cache locality during BDD operations
- Pro: Enables efficient variable reordering
- Con: Slightly more complex

Most modern implementations, including `bdd-rs`, use per-level unique tables.

== The Cost of Canonicity

Canonicity is not free.
The unique table and reduction rules impose constraints.

=== Memory Management

Since nodes are shared, we cannot simply delete a node when one reference disappears.
BDD packages must use:
- *Reference counting*: Track how many references point to each node
- *Garbage collection*: Periodically reclaim unreachable nodes
- *Mark-and-sweep*: Identify live nodes from roots, reclaim the rest

=== Global State

The unique table is inherently global.
All BDDs in a manager share the same table, which means:
- Thread safety requires synchronization
- All operations must go through the manager
- Mixing BDDs from different managers is invalid

=== Single Ordering

All BDDs in a manager share the same variable ordering.
This is necessary for canonicity but means:
- You cannot have two BDDs with different orderings
- Changing the ordering requires rebuilding all BDDs
- Operations between BDDs require compatible orderings

=== The Trade-off

#info-box(title: "Canonicity Trade-off")[
  Canonicity trades *construction-time complexity* for *query-time efficiency*.

  - Without canonicity: Construction might be faster, but every equivalence check requires full comparison
  - With canonicity: Construction maintains invariants, but equivalence is free

  For applications that perform many queries (verification, model checking), this trade-off is favorable.
]

== Summary

The canonicity theorem is the foundation of BDD utility:

#info-box(title: "Key Results")[
  - *Theorem*: Every function has exactly one ROBDD (for fixed ordering)
  - *Equivalence*: $f equiv g$ iff their BDDs are pointer-equal --- $O(1)$
  - *SAT*: $f$ is satisfiable iff BDD is not $0$ --- $O(1)$
  - *Tautology*: $f$ is valid iff BDD is $1$ --- $O(1)$
  - *Counting*: Number of solutions in $O(|"BDD"|)$

  Hash consing makes these theoretical results practical.
]

In the next chapter, we see how to build BDDs through Boolean operations, maintaining canonicity at every step.
