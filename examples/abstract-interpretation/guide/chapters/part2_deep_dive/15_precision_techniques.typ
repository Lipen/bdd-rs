#import "../../theme.typ": *

= Precision Techniques and Design Patterns <ch-precision-techniques>

#reading-path(path: "advanced")

Improving precision without sacrificing termination is the central craft of abstract interpretation.
This chapter catalogs practical techniques and patterns for building precise, scalable analyzers.

== Reduced Product Patterns

#definition(title: "Reduced Product")[
  Given domains $A$ and $B$, the reduced product is $(A times B, rho)$ where $rho$ reduces $(a, b)$ to $(a', b')$ such that $gamma(a', b') = gamma(a, b)$ and $a' lle a$, $b' lle b$.
]

Patterns:
- Mutual refinement loop with budgets
- On-demand reduction triggered by joins at hot spots
- Domain-aware reductions (e.g., length trims automata)

== Partitioning and Trace Sensitivity

- Path partitioning by predicates (coincides with BDD control domain)
- Trace partitioning: differentiate by bounded histories (e.g., last-k branches or events)
- Disjunctive completion with budgets

== Predicate Abstraction and CEGAR

- Use boolean predicates over states; abstract transformers are boolean transformers
- Counterexample-guided refinement: when proof fails, add new predicates
- Hybrid with interval/numeric domains: use predicates to split unstable joins

== Widening/Narrowing Design

- Thresholded widening (delayed application, per-variable counters)
- Extrapolation with history (widen by stable strides)
- Narrowing schedules (bounded descending iterations)

== Heuristics that Matter

- Iteration order (RPO/LIFO) and worklist prioritization
- Variable ordering for BDDs
- Context keys for interprocedural sensitivity
- Resource budgets (states, determinization depth, reduction iterations)

#insight-box[
  The best analyzers are architected around explicit precision/performance knobs with telemetry: track iteration counts, lattice heights, BDD sizes, and reduction effectiveness.
]

== Explainers and UX

- Minimal counterexamples: shortest path cubes, shortest strings in DFA
- Trace slicing: report only the predicates relevant to a warning
- Suggest repairs: indicate which guard or normalization would discharge the warning

#chapter-summary[
  Precision arises from principled products, partitioning, refinement, and carefully designed widenings.
  Engineering choices (orders, budgets, telemetry) determine practical success.
]
