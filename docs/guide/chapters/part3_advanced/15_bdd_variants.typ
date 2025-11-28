#import "../../theme.typ": *

= BDD Variants <ch-bdd-variants>

// PLAN: ZDDs, ADDs, MTBDDs, and other extensions.
// Target length: 10-12 pages

== Beyond Binary Decisions

// Content to cover:
// - Standard BDDs: Boolean functions
// - Extensions for other domains
// - Trade-offs in expressiveness vs. efficiency
// - When to use variants

== Zero-Suppressed BDDs (ZDDs)

// Content to cover:
// - Optimized for sparse sets / combinatorial objects
// - Different reduction rule: skip nodes where high = 0
// - Excellent for set families, hypergraphs
// - Knuth's extensive treatment in TAOCP

#definition(title: "Zero-Suppressed Decision Diagram")[
  A *ZDD* differs from a BDD in its reduction rule:
  - BDD: eliminate node if low = high
  - ZDD: eliminate node if high = 0 (and redirect incoming edges to low)

  This makes ZDDs compact for sparse set families where most elements are absent.
]

== Algebraic Decision Diagrams (ADDs)

// Content to cover:
// - Terminal values beyond {0, 1}
// - Represent functions f: B^n → D for arbitrary D
// - Applications: probability, costs, multi-valued logic
// - Also called MTBDDs (Multi-Terminal BDDs)

== Edge-Valued BDDs (EVBDDs)

// Content to cover:
// - Values on edges, single terminal
// - Compact for arithmetic functions
// - Linear functions have small EVBDDs
// - Relationship to ADDs

== Chain-Reduced BDDs

// Content to cover:
// - Alternative reduction strategy
// - Different space-time trade-offs
// - Specialized applications

== Free BDDs (FBDDs)

// Content to cover:
// - Relax ordering constraint
// - Each path can have different order
// - More compact but lose canonicity
// - Read-once BDDs as special case

== Hybrid Approaches

// Content to cover:
// - BDD + SAT combinations
// - BDDs for reachable states, SAT for BMC
// - When to switch representations
// - Modern verification frameworks
