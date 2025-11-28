#import "../../theme.typ": *

= Variable Ordering <ch-variable-ordering>

// PLAN: The critical factor in BDD size.
// Target length: 12-15 pages

== Why Ordering Matters

// Content to cover:
// - Same function, different orderings → vastly different sizes
// - Classic example: interleaved vs. grouped variables
// - Exponential vs. linear for symmetric functions
// - No universal best ordering

#warning-box(title: "Ordering Can Make or Break Performance")[
  A bad variable ordering can cause exponential blowup.
  For example, the function $(x_1 and y_1) or (x_2 and y_2) or ... or (x_n and y_n)$:
  - Ordering $x_1 < y_1 < x_2 < y_2 < ...$: linear size $O(n)$
  - Ordering $x_1 < x_2 < ... < y_1 < y_2 < ...$: exponential size $O(2^n)$
]

== Static Ordering Heuristics

// Content to cover:
// - DFS ordering from circuit structure
// - Fanin/fanout based heuristics
// - FORCE algorithm
// - Domain-specific knowledge

== Dynamic Variable Reordering

// Content to cover:
// - Sifting algorithm (Rudell)
// - Window permutation
// - Symmetric sifting
// - When to trigger reordering

#algorithm(title: "Sifting")[
  ```
  Sifting():
    for each variable v in some order:
      // Try all positions for v
      best_pos = current_position(v)
      best_size = total_bdd_size()

      // Move v down through all levels
      while v not at bottom:
        swap(v, next_level(v))
        if total_bdd_size() < best_size:
          best_pos = current_position(v)
          best_size = total_bdd_size()

      // Move v to best position found
      move_to(v, best_pos)
  ```
]

== Level Swapping

// Content to cover:
// - Swapping adjacent levels
// - Local operation on affected nodes
// - Complexity of a single swap
// - Implementation considerations

== Reordering in bdd-rs

// Content to cover:
// - Current capabilities and limitations
// - API for manual reordering
// - Automatic reordering triggers
// - Future directions

== Ordering for Specific Domains

// Content to cover:
// - Circuits: follow signal flow
// - Transition relations: interleave state bits
// - Arithmetic: MSB vs. LSB ordering
// - Feature models: respect hierarchy
