#import "../../theme.typ": *

= Algebraic Domain Combinations <ch-domain-combinations>

#reading-path(path: "advanced")

In the previous chapters, we explored individual abstract domains like Intervals and Signs. However, real-world analysis often requires tracking multiple properties simultaneously or capturing relationships between them. This chapter formalizes the algebra of *combining* abstract domains.

We will explore:
- *Direct Products*: Running multiple analyses in parallel.
- *Reduced Products*: Enabling domains to exchange information.
- *Trace Partitioning*: The theoretical foundation for path sensitivity.
- *Relational Domains*: Tracking correlations between variables.

== The Direct Product

The simplest way to combine two domains $A$ and $B$ is the *direct product*. This corresponds to running two independent analyses and pairing their results.

#definition(title: "Direct Product Domain")[
  Given two abstract domains $A$ and $B$, their direct product $A times B$ is defined as:
  - *Elements*: Pairs $(a, b)$ where $a in A$ and $b in B$.
  - *Ordering*: $(a_1, b_1) lle (a_2, b_2) <==> a_1 lle_A a_2 and b_1 lle_B b_2$.
  - *Join*: $(a_1, b_1) ljoin (a_2, b_2) = (a_1 ljoin_A a_2, b_1 ljoin_B b_2)$.
  - *Meet*: $(a_1, b_1) lmeet (a_2, b_2) = (a_1 lmeet_A a_2, b_1 lmeet_B b_2)$.
  - *Concretization*: $gamma((a, b)) = gamma_A (a) inter gamma_B (b)$.
]

The direct product allows us to answer questions that neither domain could answer alone, but it does not allow the domains to *help* each other.

#example-box(title: "Loss of Precision in Direct Product")[
  Consider the product of *Signs* and *Parity* domains. Let $x$ be "Positive" in Signs and "Even" in Parity. State: $(+, "Even")$.

  Now, assume we execute `x = x / 2`.
  - Signs: Positive / 2 $->$ Positive.
  - Parity: Even / 2 $->$ Top (could be even or odd).
  - Result: $(+, top)$.

  We lost the information that $x$ was even! If we knew $x=6$, then $x/2=3$ (odd). The domains operated independently and failed to refine the result.
]

== The Reduced Product

The *reduced product* improves upon the direct product by allowing information exchange (reduction) between domains.

#definition(title: "Reduction Operator")[
  A reduction operator $rho: A times B -> A times B$ transforms a pair $(a, b)$ into a more precise pair $(a', b')$ such that:
  + $gamma(a', b') = gamma(a, b)$ (Soundness: no concrete states lost).
  + $(a', b') lle (a, b)$ (Improvement: result is smaller or equal).
]

The goal of reduction is to propagate constraints discovered by one domain to the other.

#example-box(title: "Reduction Example")[
  *Intervals* $times$ *Congruence*.

  State: $x in [10, 12]$ AND $x equiv 0 mod 5$.

  - Intervals alone: $10, 11, 12$.
  - Congruence alone: $..., 5, 10, 15, ...$.
  - Intersection: ${10}$.

  *Reduction*: The congruence domain tells the interval domain: "The only valid value in $[10, 12]$ is $10$." Refined Interval: $[10, 10]$.

  The interval domain tells the congruence domain: "The value is exactly 10." Refined Congruence: $x equiv 0 mod 10$ (if supported).
]

In practice, computing the *optimal* reduction (the Granger-Cousot reduction) can be expensive. Most analyzers use *local iterations* or specific reduction heuristics (e.g., "Signs refines Intervals").

== Trace Partitioning

*Trace partitioning* is a powerful technique to gain precision by distinguishing execution paths. Instead of merging control flows immediately, we maintain separate abstract states for different history traces.

#definition(title: "Trace Partitioning Domain")[
  Given a set of trace tokens $T$ (representing control paths) and a domain $A$, the trace partitioning domain is the function space:
  $ A_T = T -> A $

  An element $f in A_T$ maps each trace $t in T$ to an abstract state $f(t)$. The concrete meaning is the union of states over all traces:
  $ gamma(f) = union.big_(t in T) gamma_A (f(t)) $
]

This is the theoretical foundation for *path-sensitive analysis*. If $T$ represents the "current basic block" or "last branch taken", we get standard path sensitivity. If $T$ represents "call stack", we get context sensitivity (interprocedural analysis).

#info-box(title: "Partitioning vs. Disjunctive Completion")[
  Trace partitioning is a practical approximation of *disjunctive completion* (the power set domain $P(A)$).

  - $P(A)$ allows *arbitrary* disjunctions: $(x=1) or (x=5)$.
  - Trace partitioning allows disjunctions *aligned with control flow*: $("path"_1 and x=1) or ("path"_2 and x=5)$.

  This structure makes trace partitioning much more efficient than full disjunctive completion.
]

== Relational Domains

So far, we have discussed *non-relational* domains (like Intervals), which track properties of variables independently ($x in [a, b]$). *Relational domains* track relationships *between* variables.

Common relational domains:
- *Octagons*: Constraints of the form $plus.minus x plus.minus y lle c$.
  Efficient ($O(n^3)$), good for array bounds checking ($i < n$).
- *Polyhedra*: Linear inequalities $sum a_i x_i lle c$.
  Very precise, but exponential complexity.
- *Equalities*: $x = y + c$.

#example-box(title: "Why Relational Domains Matter")[
  ```rust
  y = x;
  if x > 0 {
      z = y;
  }
  assert(z > 0);
  ```

  - *Intervals*: $y$ gets range of $x$. `if x > 0` refines $x$, but *not* $y$. Assertion fails (false positive).
  - *Relational*: Knows $y = x$. `if x > 0` implies $y > 0$. Assertion passes.
]

== Widening in Product Domains

When combining domains, the widening operator must also be combined. For a product $A times B$, the standard widening is component-wise: $ (a_1, b_1) widen (a_2, b_2) = (a_1 widen_A a_2, b_1 widen_B b_2) $

However, this can be too aggressive. *Delayed widening* or *widening with thresholds* is often necessary to prevent precision loss in one domain from destabilizing the other.

== Chapter Summary

- *Direct Product*: Combines domains independently.
- *Reduced Product*: Adds communication between domains to recover precision.
- *Trace Partitioning*: Distinguishes abstract states based on execution history (control flow).
- *Relational Domains*: Track correlations between variables ($x < y$).

In the next chapter, we will implement a powerful instance of these concepts: a *Reduced Product of BDDs (Trace Partitioning) and Abstract Domains*. This "Killer Feature" uses BDDs to efficiently manage the trace partition $T$, enabling scalable path-sensitive analysis.
