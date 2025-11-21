#import "../../theme.typ": *

= Path-Sensitive Analysis with BDDs <ch-bdd-path>

#reading-path(path: "advanced") #h(0.7em) #reading-path(path: "implementation")

One of the greatest challenges in static analysis is the "Path Sensitivity Problem".
Consider a simple diamond pattern:
```rust
if x > 0 { y = 1; } else { y = -1; }
// merge point
if x > 0 { assert(y == 1); }
```
A path-insensitive analysis merges the branches at the join point, remembering only that $y in {1, -1}$.
When it reaches the assertion, it has forgotten the correlation between `x` and `y`. It sees `x > 0` but `y` could be `-1`, so it reports a false positive.

To solve this, we need to track *which* path we are on.
Binary Decision Diagrams (BDDs) provide a canonical, compact representation for sets of paths and boolean constraints, enabling scalable path-sensitive abstract interpretation.

== The Control Domain

We model control-state information (guards, predicates, branch conditions) as elements of a boolean algebra.
Let $"Vars" = {1, 2, dots}$ be BDD variable identifiers.
Each predicate instance (e.g., `x > 0`, `mode == Heat`) is mapped to a unique variable $v in "Vars"$.
A control state is a boolean function $f: {0,1}^"Vars" -> {0,1}$ represented canonically by a BDD.

#definition(title: "BDD Control Domain")[
  The control domain $(B, lle)$ is the boolean algebra of formulas over $"Vars"$, ordered by implication: $f lle g$ iff $f => g$.

  - Bottom: $lbot = "false"$ (infeasible path)
  - Top: $ltop = "true"$ (any path)
  - Join: $f ljoin g = f or g$ (union of paths)
  - Meet: $f lmeet g = f and g$ (intersection of paths)
  - Complement: $not f$ (path negation)
]

#info-box(title: "Design Principle: Manager-Centric")[
  In `bdd-rs`, the `Bdd` manager is the single source of truth.
  It owns all nodes and enforces uniqueness (hash-consing).
  `Ref` is just a lightweight, copyable handle (an integer index).
  You never operate on `Ref` directly; you ask the manager: `manager.and(ref1, ref2)`.
]

== Critical Invariants (Canonical Form)

Sound and efficient use of BDDs requires respecting core invariants.
The library enforces most of these, but as a user implementing a domain, you must be aware of them:

- *1-based Indexing:* Variables are 1-indexed. `var = 0` is reserved for internal use.
- *Complemented Edges:* High edges are never negated. Complement edges only appear on low branches. This is crucial for canonicity.
- *Signed Literals:* When enumerating paths, we use `Vec<i32>`. Positive means "true", negative means "false".

#warning-box(title: "Invariant Violations")[
  Violating these invariants breaks canonicity.
  If two logically equivalent formulas have different BDD representations, `f == g` will return false, and the analysis will fail to converge or report spurious differences.
]

== Mapping Predicates to Variables

The bridge between your program and the BDD world is the *Predicate Mapping*.
You need a deterministic way to map `x > 0` to a BDD variable (e.g., $v_1$).

Strategies:
1. *Structural:* Assign IDs based on the AST node ID. Good for static graphs.
2. *Semantic:* Normalize predicates (`x > 0` becomes `0 < x`) and deduplicate.
3. *Dynamic:* Allocate new variables on the fly as new conditions are encountered.

#warning-box(title: "Dynamic Allocation Pitfall")[
  When using dynamic allocation, you must ensure *canonicity*.
  If the program encounters `if x > 0` twice, you must map it to the *same* BDD variable (provided `x` hasn't changed).
  Allocating a fresh variable for every dynamic instance destroys the correlation power of BDDs.
  Use a `ConditionManager` (as seen in @ch-symbolic-executor) to map symbolic conditions to BDD variables.
]

#example-box(title: "Mode Controller Predicates")[
  For a controller with modes `Off`, `Heat`, `Cool`:
  - Allocate three mutually exclusive predicate variables: $v_1 = ("mode"="Off")$, $v_2 = ("mode"="Heat")$, $v_3 = ("mode"="Cool")$.
  - Enforce the invariant: $(v_1 or v_2 or v_3) and not(v_1 and v_2) and dots$
  - Transitions are expressed as BDD constraints on these variables.
]

== The Art of Variable Ordering

BDD size is exponentially sensitive to variable ordering.
A bad ordering can explode the graph size from linear to exponential.

*Rule of Thumb:* Variables that are "related" or "correlated" should be close together in the ordering.

#example-box(title: "Ordering Example")[
  Consider checking equality of two n-bit integers $X$ and $Y$.
  Formula: $(x_1 <=> y_1) and (x_2 <=> y_2) and dots$

  - *Bad Ordering:* $x_1, x_2, dots, x_n, y_1, y_2, dots, y_n$.
    The BDD must "remember" the value of $x_1$ all the way down to $y_1$. Size is $O(2^n)$.
  - *Good Ordering:* $x_1, y_1, x_2, y_2, dots$.
    The BDD checks $x_1=y_1$ immediately and can "forget" them. Size is $O(n)$.
]

== Abstract Transfer: Conditioning and Forgetting

Let $(A, <=_A)$ be a data domain (e.g., intervals), and $B$ the control domain.
We analyze pairs $(b, a) in B times A$.
Control affects data via conditioning; data can also discharge control facts.

- *Assume/Filter:* $(b, a)$ with guard $g$ becomes $(b and g, a|g)$.
- *Join (Product):* $(b_1, a_1) ljoin (b_2, a_2) = (b_1 or b_2, a_1 ljoin a_2)$.
- *Forget:* Existentially abstract $v$ by $(exists v . b, a)$ when predicate $v$ is no longer relevant.

#definition(title: "Existential Abstraction")[
  Given a variable $v$, existential abstraction removes $v$ while preserving satisfiability:
  $ exists v . f := f[v := 0] or f[v := 1] $
  This corresponds to control-flow joins where the precise branching condition no longer matters to downstream facts, preventing the BDD from growing indefinitely with irrelevant history.
]

== Product vs. Disjunctive Domains

The join operation defined above is for a *Product Domain* $(B times A)$.
It merges data states immediately:
$(b_1, x=1) ljoin (b_2, x=-1) => (b_1 or b_2, x in [-1, 1])$
This is efficient but loses the correlation "if $b_1$ then $x=1$".

To maintain full path sensitivity, we use a *Disjunctive Domain* (Power Set Domain), as implemented in @ch-combining-domains:
$ S = { (b_1, a_1), (b_2, a_2), dots } $
Here, the join is just set union (or list concatenation).
We only merge elements if their data states are similar or to prevent explosion.

#table(
  columns: (auto, auto, auto),
  inset: 10pt,
  align: horizon,
  table.header([*Feature*], [*Product Domain* $(B times A)$], [*Disjunctive Domain* $P(B times A)$]),
  [State Size], [Constant (1 pair)], [Linear/Exponential (N pairs)],
  [Precision], [Lower (merges data)], [Higher (keeps paths separate)],
  [Use Case], [Large programs, filtering], [Deep analysis, verification],
)

== Path Enumeration and Explanations

One of the best features of BDDs is that they can *explain* why a bug is possible.
We can enumerate the paths (cubes) that lead to an error state.

With signed literals $l_i in bb(Z)$, positive literal $+k$ means $v_k = "true"$, negative literal $-k$ means $v_k = "false"$.

- *Minimal Cubes:* Enumerate prime implicants to avoid redundant explanations.
- *Ranking:* Present the shortest or most likely counterexamples first.

#example-box(title: "Explaining a Warning")[
  A division-by-zero warning is reported under cubes $[+3, -5, +9]$ and $[+3, -7]$.
  Translation:
  "Error occurs when:
  1. `x > 0` AND `mode != Safe` AND `input_valid`
  2. `x > 0` AND `!system_ready`"
]

== Soundness Sketch

Let $T$ be the combined transfer over $(B times A, <=)$, monotone in both components, and let $W$ be a widening.

#theorem(title: "Soundness of BDD-Conditioned Analysis")[
  Suppose data transformers are sound under conditioning, i.e., for any guard $g$ and concrete semantics $llb - rrb$:
  $ llb "assume"(g); S rrb subset.eq gamma_A (a|g) $ whenever $ llb S rrb subset.eq gamma_A (a) $.

  If $T$ is monotone and iteration uses $W$ on the product lattice, the computed post-fixpoint $(b^*, a^*)$ satisfies:
  All concrete reachable states lie in $gamma_B (b^*) times gamma_A (a^*)$.
]

#proof[
  Follows from product-lattice monotonicity and standard abstract interpretation soundness, with meet-as-conditioning preserving over-approximation.
  The BDD manager’s canonicity ensures equality checks are precise in the control component.
]

== Engineering Checklist

- *Allocate Once:* Allocate BDD variables once; document the mapping.
- *Enforce Invariants:* No negated high edges; 1-indexed vars.
- *Implement Operations:* Provide `assume`, `forget`, and `exists` on the control domain.
- *Co-design:* Data transfer functions must accept guards for refinement.
- *Order Matters:* Choose and document a variable ordering rationale.

#chapter-summary[
  BDDs provide a canonical, compact control domain for path-sensitive analysis.
  By respecting invariants and adopting deliberate variable ordering, we can scale path sensitivity to large control spaces, solving the "diamond problem" efficiently.
]

#pagebreak()
