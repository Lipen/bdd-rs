#import "../../theme.typ": *

= Garbage Collection <ch-garbage-collection>

// PLAN: Memory management for BDD nodes.
// Target length: 8-10 pages

== The Memory Problem

// Content to cover:
// - BDD operations create intermediate nodes
// - Many nodes become unreachable ("garbage")
// - Without cleanup: unbounded memory growth
// - Challenge: determine what's reachable

== What Counts as Garbage?

// Content to cover:
// - Roots: BDDs explicitly kept by user
// - Reachable: nodes reachable from roots
// - Garbage: allocated but unreachable nodes
// - Shared nodes: reachable from multiple roots

== Mark-and-Sweep Collection

// Content to cover:
// - Phase 1: Mark all reachable nodes from roots
// - Phase 2: Sweep and reclaim unmarked nodes
// - Update unique table during sweep
// - Cache invalidation

#algorithm(title: "Mark-and-Sweep GC")[
  ```
  collect_garbage(roots):
    // Mark phase
    marked = empty_set()
    for root in roots:
      mark_reachable(root, marked)

    // Sweep phase
    for node_id in all_nodes():
      if node_id not in marked:
        remove_from_unique_table(node_id)
        add_to_free_list(node_id)

    // Clear caches (entries may reference freed nodes)
    clear_computed_caches()
  ```
]

== Reference Counting Alternative

// Content to cover:
// - Count references to each node
// - Decrement on dereference, free at zero
// - Pros: immediate reclamation, incremental
// - Cons: cycle issues (less relevant for DAGs), overhead

== GC in bdd-rs

// Content to cover:
// - Manual GC trigger via collect_garbage
// - User specifies root set
// - Free set tracks available slots
// - Performance considerations

```rust
// User triggers GC explicitly
bdd.collect_garbage(&[result, constraint]);
```

== When to Collect

// Content to cover:
// - Memory pressure thresholds
// - After bulk operations
// - Periodic collection
// - Avoiding GC in tight loops

#performance-note[
  Garbage collection is expensive — it requires traversing all reachable nodes and clearing caches.
  Call it between major computation phases, not inside inner loops.
]
