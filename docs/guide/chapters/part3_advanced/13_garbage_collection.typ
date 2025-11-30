#import "../../theme.typ": *

= Garbage Collection <ch-garbage-collection>

BDD operations create nodes.
Lots of nodes.
An operation like `f AND g` may produce thousands of intermediate nodes, only to discard most of them when the final result emerges.
Without cleanup, memory consumption grows without bound.

This chapter covers garbage collection --- the art of reclaiming dead nodes while preserving live ones.

== The Memory Problem

Every `mk` call potentially allocates a new node.
Every Apply operation recursively calls `mk` many times.
Consider this innocent-looking code:

```rust
let a = bdd.and(x, y);
let b = bdd.and(a, z);
let c = bdd.or(b, w);   // We only care about c
```

What happens to the intermediate nodes created for `a` and `b`?
If `c` shares structure with them, they're still needed.
If not, they're *garbage* --- consuming memory but serving no purpose.

#figure(
  cetz.canvas(length: 1cm, {
    import cetz.draw: *

    // Memory growth visualization
    content((6, 6.5), text(weight: "bold", size: 1em)[Memory Growth Without GC])

    // Time axis
    line((1, 1), (11, 1), stroke: 1pt + colors.line, mark: (end: ">"))
    content((11.5, 1), text(size: 0.8em)[Time])

    // Memory axis
    line((1, 1), (1, 5.5), stroke: 1pt + colors.line, mark: (end: ">"))
    content((1, 6), text(size: 0.8em)[Memory])

    // Operations
    for (i, op) in ((2, "op₁"), (4, "op₂"), (6, "op₃"), (8, "op₄"), (10, "op₅")).enumerate() {
      content((op.at(0), 0.5), text(size: 0.7em, fill: colors.text-muted)[#op.at(1)])
    }

    // Memory line - growing
    line(
      (1, 1.5),
      (2, 2.3),
      (3, 2.1),
      (4, 3.2),
      (5, 3.0),
      (6, 4.1),
      (7, 3.9),
      (8, 4.8),
      (9, 4.6),
      (10, 5.3),
      stroke: 2pt + colors.error,
    )

    // Live memory (lower, stable-ish)
    line(
      (1, 1.3),
      (2, 1.8),
      (3, 1.6),
      (4, 2.0),
      (5, 1.8),
      (6, 2.2),
      (7, 2.0),
      (8, 2.3),
      (9, 2.1),
      (10, 2.4),
      stroke: 2pt + colors.success,
    )

    // Legend
    line((7.5, 5.5), (8.5, 5.5), stroke: 2pt + colors.error)
    content((9.5, 5.5), text(size: 0.7em)[Allocated], anchor: "west")
    line((7.5, 5), (8.5, 5), stroke: 2pt + colors.success)
    content((9.5, 5), text(size: 0.7em)[Actually live], anchor: "west")

    // Gap annotation
    content((5, 3.5), text(size: 0.8em, fill: colors.error)[Garbage!])
  }),
  caption: [Without garbage collection, allocated memory grows far beyond what's actually needed.],
)

#warning-box(title: "The Danger of Unbounded Growth")[
  A verification run might perform millions of BDD operations.
  Without GC, you'll run out of memory long before finding the bug you're looking for.
]

== What Counts as Garbage?

#definition(title: "Reachability")[
  A node is *live* (reachable) if:
  + It's a *root* --- a BDD the user explicitly keeps, or
  + It's reachable from a root via low/high edges

  Everything else is *garbage*.
]

#figure(
  cetz.canvas(length: 1cm, {
    import cetz.draw: *

    content((6, 7), text(weight: "bold", size: 1em)[Live vs. Garbage Nodes])

    // Root pointer
    content((3, 6.2), text(size: 0.8em, weight: "semibold")[Root])
    line((3, 6), (3, 5.5), stroke: 1.5pt + colors.primary, mark: (end: ">", fill: colors.primary))

    // Live nodes (green background)
    rect((1.5, 1.5), (4.5, 5.5), fill: colors.box-example.lighten(60%), stroke: none, radius: 8pt)
    content((3, 5.2), text(size: 0.7em, fill: colors.success)[LIVE])

    bdd-decision-node((3, 4.5), $x$, name: "x-live")
    bdd-decision-node((2.2, 3), $y$, name: "y-live")
    bdd-terminal-node((3.8, 3), $1$, name: "one-live")
    bdd-terminal-node((2.2, 1.8), $0$, name: "zero-live")

    bdd-low-edge("x-live", "y-live")
    bdd-high-edge("x-live", "one-live")
    bdd-low-edge("y-live", "zero-live")
    line((2.5, 2.6), (3.5, 2.6), stroke: 1pt + colors.line)

    // Garbage nodes (red background, no root)
    rect((6, 1.5), (10.5, 5.5), fill: colors.box-warning.lighten(60%), stroke: none, radius: 8pt)
    content((8.25, 5.2), text(size: 0.7em, fill: colors.error)[GARBAGE])

    bdd-decision-node((7, 4.5), $a$, name: "a-garbage")
    bdd-decision-node((9.5, 4.5), $b$, name: "b-garbage")
    bdd-terminal-node((7, 3), $0$, name: "zero-garbage")
    bdd-terminal-node((9.5, 3), $1$, name: "one-garbage")

    line((6.7, 4.1), (6.7, 3.4), stroke: (dash: "dashed", paint: colors.line, thickness: 1pt))
    line((7.3, 4.1), (7.3, 3.4), stroke: 1pt + colors.line)
    line((9.2, 4.1), (9.2, 3.4), stroke: (dash: "dashed", paint: colors.line, thickness: 1pt))
    line((9.8, 4.1), (9.8, 3.4), stroke: 1pt + colors.line)

    // No root pointer - X marks
    content((7, 5.8), text(size: 1em, fill: colors.error)[✗])
    content((9.5, 5.8), text(size: 1em, fill: colors.error)[✗])

    // Explanation
    content((6, 0.5), align(center)[
      #set text(size: 0.8em)
      No root points to these nodes $=>$ they can be reclaimed
    ])
  }),
  caption: [Live nodes are reachable from a root; garbage nodes have no path from any root.],
)

#insight-box[
  Shared structure complicates things.
  A node might be reachable from *multiple* roots.
  We can only reclaim it when *all* roots that could reach it are gone.
]

== Mark-and-Sweep Collection

The classic garbage collection algorithm has two phases:

#figure(
  cetz.canvas(length: 1cm, {
    import cetz.draw: *

    // Phase 1: Mark
    content((3, 7), text(weight: "bold", fill: colors.primary)[Phase 1: Mark])

    rect(
      (0.5, 3.5),
      (5.5, 6.5),
      fill: colors.box-definition.lighten(50%),
      stroke: 1pt + colors.primary.lighten(30%),
      radius: 4pt,
    )

    content((3, 6), text(size: 0.8em)[Start from roots])
    content((3, 5.3), text(size: 0.8em)[Traverse all edges])
    content((3, 4.6), text(size: 0.8em)[Mark visited nodes])
    content((3, 3.9), text(size: 0.8em, fill: colors.success)[Marked = Live ✓])

    // Arrow
    line((5.8, 5), (7, 5), stroke: 2pt + colors.text-muted, mark: (end: ">"))

    // Phase 2: Sweep
    content((9.5, 7), text(weight: "bold", fill: colors.warning)[Phase 2: Sweep])

    rect(
      (7, 3.5),
      (12, 6.5),
      fill: colors.box-warning.lighten(50%),
      stroke: 1pt + colors.warning.lighten(30%),
      radius: 4pt,
    )

    content((9.5, 6), text(size: 0.8em)[Scan all nodes])
    content((9.5, 5.3), text(size: 0.8em)[Unmarked? Reclaim!])
    content((9.5, 4.6), text(size: 0.8em)[Update unique table])
    content((9.5, 3.9), text(size: 0.8em, fill: colors.error)[Garbage freed ✗])

    // Additional step
    content((6.25, 2.5), text(weight: "bold", fill: colors.info)[Also: Clear Caches])
    rect(
      (3.5, 1.5),
      (9, 2.2),
      fill: colors.box-insight.lighten(50%),
      stroke: 1pt + colors.info.lighten(30%),
      radius: 4pt,
    )
    content((6.25, 1.85), text(size: 0.8em)[Cached results may reference freed nodes!])
  }),
  caption: [Mark-and-sweep GC: mark what's live, sweep away the rest.],
)

#algorithm(title: "Mark-and-Sweep GC")[
  ```
  collect_garbage(roots):
    // === MARK PHASE ===
    marked = empty_bitset(num_nodes)
    for root in roots:
      mark_recursive(root, marked)

    // === SWEEP PHASE ===
    for node_id in 1..num_nodes:  // Skip terminal at 0
      if not marked[node_id]:
        // Remove from unique table
        level = get_level(node_id)
        subtables[level].remove(node_id)
        // Add to free list for reuse
        free_set.insert(node_id)

    // === CACHE INVALIDATION ===
    operation_cache.clear()
    size_cache.clear()

  mark_recursive(ref, marked):
    if ref.is_terminal() or marked[ref.id()]:
      return
    marked[ref.id()] = true
    node = nodes[ref.id()]
    mark_recursive(node.low, marked)
    mark_recursive(node.high, marked)
  ```
]

=== Why Clear Caches?

The operation cache stores entries like `(AND, f, g) → h`.
If node `h` gets garbage-collected, this cache entry becomes *dangling* --- it points to freed memory.

#warning-box(title: "Dangling Cache Entries")[
  If we don't clear caches after GC:
  + A future operation looks up `(AND, f, g)`
  + Cache returns stale reference `h`
  + The slot for `h` might now hold a completely different node!
  + Result: silent corruption, wrong answers

  Always invalidate caches after garbage collection.
]

== Reference Counting Alternative

Instead of periodic mark-and-sweep, we could track references to each node:

#comparison-table(
  [*Aspect*],
  [*Mark-and-Sweep*],
  [*Reference Counting*],
  [When reclaimed],
  [During GC pauses],
  [Immediately when count hits 0],
  [Overhead],
  [None between GCs],
  [Every reference update],
  [Pause times],
  [Can be long],
  [None (incremental)],
  [Cycles],
  [Handles fine],
  [Problematic (but DAGs don't cycle)],
  [Implementation],
  [Simpler],
  [Pervasive ref management],
)

#info-box(title: "Why bdd-rs Uses Mark-and-Sweep")[
  BDDs are DAGs (no cycles), so reference counting *would* work.
  However:
  - Reference count updates add overhead to *every* operation
  - BDD operations are cache-bound; extra memory traffic hurts
  - Batch GC integrates well with explicit root management

  Most BDD libraries, including CUDD, use mark-and-sweep.
]

== GC in bdd-rs

`bdd-rs` uses *explicit* garbage collection --- you decide when to collect and what to keep:

```rust
// Build some BDDs
let formula1 = bdd.and(x, y);
let formula2 = bdd.or(y, z);
let combined = bdd.and(formula1, formula2);

// We only need 'combined' going forward
bdd.collect_garbage(&[combined]);

// Now formula1 and formula2 may have been freed
// (unless 'combined' shares structure with them)
```

The `free_set` tracks which node slots are available for reuse:

```rust
pub struct Bdd {
    nodes: RefCell<Vec<Node>>,
    free_set: RefCell<HashSet<NodeId>>,  // Available slots
    // ...
}

fn allocate_node(&self, node: Node) -> NodeId {
    let mut free_set = self.free_set.borrow_mut();
    if let Some(&id) = free_set.iter().next() {
        // Reuse freed slot
        free_set.remove(&id);
        self.nodes.borrow_mut()[id.raw()] = node;
        id
    } else {
        // Allocate new slot
        let id = NodeId::new(self.nodes.borrow().len() as u32);
        self.nodes.borrow_mut().push(node);
        id
    }
}
```

== When to Collect

#insight-box[
  GC is expensive --- it touches *all* live nodes and clears *all* caches.
  Time it wisely.
]

Good times to collect:
+ *After major phases*: Finished building a transition relation? Collect before model checking.
+ *When memory is tight*: Monitor allocation and trigger GC at thresholds.
+ *Before long-running operations*: A clean heap means better cache behavior.

Bad times to collect:
- *Inside tight loops*: The overhead dominates.
- *Mid-computation*: You might need those "intermediate" results!
- *Without knowing your roots*: You'll lose data.

```rust
// Good: collect between phases
let transition_rel = build_transition_relation(&bdd);
bdd.collect_garbage(&[transition_rel]);

let reachable = compute_reachability(&bdd, transition_rel);
bdd.collect_garbage(&[reachable]);

// Bad: collect inside a loop
for i in 0..1000 {
    let step = bdd.and(current, constraint);
    bdd.collect_garbage(&[step]);  // DON'T DO THIS!
    current = step;
}
```

#performance-note[
  As a rule of thumb: if your BDD manager has grown to 2× the live node count, it's time to collect.
  Many libraries trigger automatic GC at such thresholds.
]
