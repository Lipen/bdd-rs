#import "../../theme.typ": *

= Performance & Debugging <ch-performance>

#reading-path(path: "implementation")

Building a correct abstract interpreter is hard; building a *fast* one is even harder.
When using BDDs for program analysis, performance cliffs are steep: a good variable ordering runs in milliseconds, while a bad one might never terminate.
This chapter provides a survival guide for tuning and debugging your BDD-based analyzer.

== The Three Pillars of BDD Performance

=== Variable Ordering

We cannot stress this enough: *Variable ordering is the single most important factor.*

- *Heuristic:* Group related variables together.
- *Data Structures:* Keep bits of the same variable adjacent (e.g., `x[0]`, `x[1]`, ...).
- *Interleaving:* For relational properties (e.g., checking `x == y`), interleave the variables: `x[0], y[0], x[1], y[1], ...`.

#warning-box(title: "The Symptom")[
  If your analysis hangs on a simple program or consumes gigabytes of RAM suddenly, it is almost always a variable ordering issue.
]

=== Garbage Collection

`bdd-rs` uses a unique memory model.
Nodes are stored in a large `Vec`.
Operations like `apply_and` create new nodes but do not automatically delete old ones (because they might be shared).

You *must* call `collect_garbage` periodically.

```rust
// In your analysis loop:
if iteration % 100 == 0 {
    // You must provide the 'roots' (nodes you want to keep)
    let roots = vec![current_state.control];
    bdd.collect_garbage(&roots);
}
```

=== Caching (Memoization)

Abstract transfer functions are often called repeatedly with the same arguments.
The BDD manager caches low-level operations (`and`, `or`), but your domain logic is not cached by default.

*Strategy:* Cache the result of `transfer(stmt, state)`.
Since `Bdd` nodes are canonical integers (`Ref`), they make excellent hash map keys!

```rust
struct CacheKey {
    stmt_id: StmtId,
    bdd_ref: Ref,
    data_hash: u64,
}
```

== Debugging Techniques

=== Visualizing BDDs

When a BDD grows unexpectedly, visualize it.
`bdd-rs` can export to DOT format.

```rust
use std::fs::File;
use bdd::dot;

let mut file = File::create("debug.dot")?;
dot::write(&bdd, node, &mut file)?;
```

Render it with Graphviz: `dot -Tpng debug.dot -o debug.png`.
Look for:
- *Long chains:* Indicates bad ordering.
- *Redundant subgraphs:* Maybe you missed a reduction opportunity?

=== The "Explain" Feature

If your analysis reports a false positive (e.g., "Assertion failed!"), ask the BDD *why*.
Enumerate the paths (cubes) in the error state.

```rust
let cubes = bdd.sat_cubes(error_state);
for cube in cubes {
    println!("Failure possible when:");
    for lit in cube {
        println!("  {} = {}", var_name(lit.var), lit.val);
    }
}
```

This often reveals that the analyzer thinks a path is possible when it shouldn't be (e.g., `x = 1` AND `x = 2`), indicating a missing `assume` or reduction.

== Profiling

Use standard Rust profiling tools.

- *`perf` / `flamegraph`*: Check if time is spent in `bdd::apply` (normal) or in your domain logic (optimize your domain).
- *`counts`*: The `bdd` manager tracks operation counts.
  Print `bdd.node_count()` to monitor growth.

== Tuning Widening

If the analysis is slow to converge:
+ *Check Widening:* Are you widening too late? Try reducing the delay.
+ *Check Stability:* Is your `widen` operator actually ensuring termination? (e.g., does it cycle between two values?)
+ *BDD Widening:* For control flow, force the BDD to `true` (top) if it grows too large.

```rust
fn widen_control(bdd: &Bdd, f1: Ref, f2: Ref) -> Ref {
    if bdd.size(f2) > THRESHOLD {
        bdd.one // Give up on tracking exact control flows
    } else {
        f2
    }
}
```

== Chapter Summary

- *Order variables* carefully; it's the difference between $O(n)$ and $O(2^n)$.
- *Collect garbage* to manage memory usage.
- *Visualize* BDDs to understand their structure and debug ordering.
- *Profile* to find bottlenecks in domain operations vs. BDD operations.
- *Widen aggressively* if convergence is too slow.

