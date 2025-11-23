#import "../../theme.typ": *

= Performance & Debugging <ch-performance>

#reading-path(path: "implementation")

Building a correct abstract interpreter is hard; building a *fast* one is even harder.
When using BDDs for program analysis, performance cliffs are steep: good variable ordering runs in milliseconds, bad ordering might never terminate.
This chapter provides a survival guide for tuning and debugging your BDD-based analyzer.

== The Three Pillars of BDD Performance

=== Variable Ordering

*Variable ordering is the single most important factor.*

- *Heuristic:* Group related variables together.
- *Data Structures:* Keep bits of the same variable adjacent (e.g., `x[0]`, `x[1]`, ...).
- *Interleaving:* For relational properties (e.g., checking `x == y`), interleave the variables: `x[0], y[0], x[1], y[1], ...`.

#figure(
  caption: [Variable ordering impact on BDD size],

  cetz.canvas({
    import cetz: draw

    // Good Order: Interleaved
    draw.content((0, 4), text(weight: "bold")[Good Order])
    draw.content((0, 3.5), text(size: 9pt)[$x_1, y_1, x_2, y_2$])

    draw.circle((0, 2.5), radius: 0.3, name: "g1", stroke: colors.success + 1pt)
    draw.circle((0, 1.5), radius: 0.3, name: "g2", stroke: colors.success + 1pt)
    draw.circle((0, 0.5), radius: 0.3, name: "g3", stroke: colors.success + 1pt)

    draw.line("g1.south", "g2.north", stroke: colors.text-light + 0.8pt)
    draw.line("g2.south", "g3.north", stroke: colors.text-light + 0.8pt)

    draw.content((0, -0.5), text(size: 9pt)[Linear Size])

    // Bad Order: Blocked
    draw.content((4, 4), text(weight: "bold")[Bad Order])
    draw.content((4, 3.5), text(size: 9pt)[$x_1, x_2, y_1, y_2$])

    draw.circle((4, 2.5), radius: 0.3, name: "b1", stroke: colors.error + 1pt)

    draw.circle((3, 1.5), radius: 0.3, name: "b2l", stroke: colors.error + 1pt)
    draw.circle((5, 1.5), radius: 0.3, name: "b2r", stroke: colors.error + 1pt)

    draw.circle((2.5, 0.5), radius: 0.3, name: "b3ll", stroke: colors.error + 1pt)
    draw.circle((3.5, 0.5), radius: 0.3, name: "b3lr", stroke: colors.error + 1pt)
    draw.circle((4.5, 0.5), radius: 0.3, name: "b3rl", stroke: colors.error + 1pt)
    draw.circle((5.5, 0.5), radius: 0.3, name: "b3rr", stroke: colors.error + 1pt)

    draw.line("b1.south-west", "b2l.north", stroke: colors.text-light + 0.8pt)
    draw.line("b1.south-east", "b2r.north", stroke: colors.text-light + 0.8pt)

    draw.line("b2l.south-west", "b3ll.north", stroke: colors.text-light + 0.8pt)
    draw.line("b2l.south-east", "b3lr.north", stroke: colors.text-light + 0.8pt)
    draw.line("b2r.south-west", "b3rl.north", stroke: colors.text-light + 0.8pt)
    draw.line("b2r.south-east", "b3rr.north", stroke: colors.text-light + 0.8pt)

    draw.content((4, -0.5), text(size: 9pt)[Exponential Size])
  }),
)

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

#chapter-summary[
  This chapter revealed that abstract interpretation performance often hinges on implementation details rather than algorithmic complexity alone.

  *Variable ordering* is paramount for BDD efficiency.
  Poor ordering can inflate BDD size from $O(n)$ to $O(2^n)$ nodes, transforming tractable problems into intractable ones.
  Place variables that appear together in Boolean expressions adjacent in the ordering to maximize sharing.

  *Garbage collection* becomes critical for long-running analyses.
  BDD nodes accumulate during exploration, and without periodic cleanup, memory exhaustion occurs even when the final result is small.
  Trigger collection when node count exceeds thresholds or at natural analysis boundaries.

  *Visualization* provides invaluable debugging insight.
  Rendering BDDs graphically exposes structural problems like poor ordering, excessive node duplication, or unexpected BDD growth.
  Tools that export to DOT format enable inspecting symbolic states that would be opaque in textual form.

  *Profiling* distinguishes between domain operation costs and BDD manipulation overhead.
  If BDD operations dominate, consider variable reordering or simplification.
  If domain operations dominate, consider faster abstract domains or reduced product optimizations.

  *Aggressive widening* trades precision for convergence speed.
  If fixpoint iteration stalls, applying widening earlier or with coarser thresholds sacrifices some accuracy to ensure termination.
]

