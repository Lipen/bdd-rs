#import "../../theme.typ": *

= Design Trade-offs <ch-design-tradeoffs>

// PLAN: Engineering decisions in BDD library design.
// Target length: 10-12 pages

== Memory vs. Time

// Content to cover:
// - More cache → fewer recomputations
// - More nodes → more memory pressure
// - Cache sizing heuristics
// - Adaptive strategies

== Node Representation Choices

// Content to cover:
// - Pointer-based vs. index-based
// - Inline children vs. separate arrays
// - Compression techniques
// - Cache line optimization

#comparison-table(
  [Approach], [Pros], [Cons],
  [Pointer-based], [Direct access], [64-bit overhead, GC complexity],
  [Index-based], [Compact (32-bit)], [Extra indirection],
  [Array-of-structs], [Cache-friendly traversal], [Fragmentation],
  [Struct-of-arrays], [SIMD potential], [Scattered access],
)

== Complement Edge Trade-offs

// Content to cover:
// - Space savings (up to 2x fewer nodes)
// - O(1) negation
// - Complexity in algorithms
// - Normalization overhead

== Unique Table Design

// Content to cover:
// - Global table vs. per-level tables
// - Hash function selection
// - Collision resolution
// - Resize policies

== Cache Strategies

// Content to cover:
// - Single cache vs. multiple caches
// - Cache associativity
// - Eviction policies
// - Cache warmth preservation across GC

== Garbage Collection Approaches

// Content to cover:
// - Manual vs. automatic
// - Reference counting vs. mark-sweep
// - Incremental collection
// - GC-triggered reordering

== API Design Philosophy

// Content to cover:
// - Safety vs. flexibility
// - Zero-cost abstractions in Rust
// - Hiding vs. exposing internals
// - Error handling approaches
