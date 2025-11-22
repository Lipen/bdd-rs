#import "../../theme.typ": *

= Fixpoint Algorithms <ch-fixpoint-algorithms>

#reading-path(path: "advanced")

While Tarski's theorem guarantees fixpoint existence and Kleene's theorem provides a basic iteration method, practical program analysis requires more sophisticated algorithms.
This chapter explores chaotic iteration, worklist algorithms, and strategies for computing fixpoints efficiently.

== From Kleene to Chaotic Iteration

Kleene iteration computes $f^0(bot), f^1(bot), f^2(bot), dots$ sequentially.
For compositional problems (multiple equations), we can interleave updates.
This is *chaotic iteration*.

#definition(title: "Equation System")[
  A *system of equations* over a complete lattice $L$ consists of:
  - Variables $X = {x_1, dots, x_n}$.
  - Equations $x_i = f_i(x_1, dots, x_n)$ where $f_i: L^n -> L$ are monotone.

  A *solution* is an assignment $sigma: X -> L$ satisfying all equations.
  The *least solution* is the least fixpoint of the combined function $F: L^n -> L^n$ defined by $F(accent(x, arrow)) = (f_1(accent(x, arrow)), dots, f_n(accent(x, arrow)))$.
]

#example-box[
  *Reaching definitions dataflow equations:*

  For each program point $p$, let $"RD"[p]$ be the set of reaching definitions.

  $ "RD"[p] = union.big_(q in "pred"(p)) ("RD"[q] - "kill"[p]) union "gen"[p] $

  This gives one equation per program point.
  Kleene iteration would update all points together.
  Chaotic iteration can update them in any order.
]

#theorem(title: "Chaotic Iteration Convergence")[
  Let $X = {x_1, dots, x_n}$ be variables with equations $x_i = f_i(accent(x, arrow))$ over a complete lattice with ascending chain condition.
  Let $sigma^0, sigma^1, sigma^2, dots$ be a sequence of assignments where:

  - $sigma^0(x_i) = bot$ for all $i$.
  - $sigma^(k+1)$ updates *some* variable: $sigma^(k+1)(x_i) = f_i(sigma^k(x_1), dots, sigma^k(x_n))$ for some $i$, and $sigma^(k+1)(x_j) = sigma^k(x_j)$ for $j != i$.
  - Every variable is updated *infinitely often*.

  Then the sequence converges to the least fixpoint.
]

The key insight: as long as we keep updating variables (fairness), the order doesn't matter!

#proof[
  Define the *product lattice* $L^n$ with ordering $(x_1, dots, x_n) <= (y_1, dots, y_n)$ iff $x_i <= y_i$ for all $i$.

  *Step 1:* The sequence is increasing.
  Each update $sigma^(k+1)(x_i) = f_i(sigma^k)$ satisfies:
  - $sigma^k(x_i) <= f_i(sigma^k)$ (by induction: initially $bot <= f_i(bot)$, and if all components increased, monotonicity gives $f_i(sigma^k) <= f_i(sigma^(k+1))$).
  - Thus $sigma^k <= sigma^(k+1)$ component-wise.

  *Step 2:* The sequence stabilizes.
  Since $L^n$ has ACC (product of ACC lattices), the increasing sequence stabilizes at some $sigma^*$.

  *Step 3:* $sigma^*$ is a fixpoint.
  For each $i$, since $x_i$ is updated infinitely often and the sequence stabilized:
  $ sigma^*(x_i) = f_i(sigma^*) $

  *Step 4:* $sigma^*$ is the least fixpoint.
  Any fixpoint $mu$ satisfies $sigma^0 <= mu$ (base case).
  If $sigma^k <= mu$, then $sigma^(k+1)(x_i) = f_i(sigma^k) <= f_i(mu) = mu(x_i)$ by monotonicity.
  Thus $sigma^* <= mu$.
]

== Worklist Algorithms

Chaotic iteration can be wasteful.
Updating a variable when its inputs haven't changed accomplishes nothing.
*Worklist algorithms* track dependencies and only recompute when necessary.

#algorithm(title: "Basic Worklist")[
  *Input:* Equation system $x_i = f_i(accent(x, arrow))$ with dependency graph $G$.

  *Output:* Least fixpoint solution.

  + $W <- {x_1, ..., x_n}$ $quad slash.double$ Initialize worklist with all variables.
  + $sigma <- lambda i . bot$ $quad slash.double$ Initialize solution to bottom.
  + *while* $W != emptyset$ *do*
    + $x <-$ *remove*$(W)$ $quad slash.double$ Pick a variable from worklist.
    + $"old" <- sigma(x)$
    + $"new" <- f_x (sigma)$ $quad slash.double$ Recompute using current solution.
    + *if* $"new" != "old"$ *then*
      + $sigma(x) <- "new"$ $quad slash.double$ Update solution.
      + *for each* $y$ *where* $x -> y in G$ *do*
        + *add*$(W, y)$ $quad slash.double$ Re-examine dependents.
      + *end for*
    + *end if*
  + *end while*
  + *return* $sigma$
]

Here is how a generic worklist solver looks in Rust:

```rust
use std::collections::{VecDeque, HashSet};
use std::hash::Hash;

pub fn solve_worklist<K, D, F>(
    initial_worklist: Vec<K>,
    mut get_deps: F,
    mut transfer: impl FnMut(&K, &D) -> D,
    bottom: D
) -> HashMap<K, D>
where
    K: Eq + Hash + Clone,
    D: AbstractDomain,
    F: FnMut(&K) -> Vec<K>, // Returns dependents of a node
{
    let mut state: HashMap<K, D> = HashMap::new();
    let mut worklist: VecDeque<K> = initial_worklist.into();
    let mut in_worklist: HashSet<K> = worklist.iter().cloned().collect();

    while let Some(node) = worklist.pop_front() {
        in_worklist.remove(&node);

        let old_val = state.get(&node).unwrap_or(&bottom).clone();
        let new_val = transfer(&node, &old_val);

        if new_val != old_val {
            // State changed! Update and notify dependents
            state.insert(node.clone(), new_val);

            for dep in get_deps(&node) {
                if !in_worklist.contains(&dep) {
                    worklist.push_back(dep.clone());
                    in_worklist.insert(dep);
                }
            }
        }
    }
    state
}
```

#figure(
  caption: [Worklist algorithm tracking dependencies],

  cetz.canvas({
    import cetz: draw

    // Dependency graph
    let draw-node(name, pos, label, status) = {
      let fill = if status == "in-worklist" {
        colors.warning.lighten(70%)
      } else if status == "computed" {
        colors.success.lighten(70%)
      } else {
        colors.bg-code
      }
      draw.circle(pos, radius: 0.4, name: name, fill: fill, stroke: colors.primary + 1pt)
      draw.content(name, label)
    }

    let draw-dep(from, to) = {
      draw.line(from, to, stroke: colors.text-light + 0.8pt, mark: (end: ">"))
    }

    // Example with 6 variables in CFG structure
    draw-node("x1", (2, 5), $x_1$, "computed")
    draw-node("x2", (4, 5), $x_2$, "in-worklist")
    draw-node("x3", (6, 5), $x_3$, "init")
    draw-node("x4", (2, 3), $x_4$, "computed")
    draw-node("x5", (4, 3), $x_5$, "in-worklist")
    draw-node("x6", (6, 3), $x_6$, "init")

    // Dependencies
    draw-dep("x1.south", "x4.north")
    draw-dep("x1.east", "x2.west")
    draw-dep("x2.south", "x5.north")
    draw-dep("x2.east", "x3.west")
    draw-dep("x4.east", "x5.west")
    draw-dep("x5.east", "x6.west")

    // Legend
    let legend-y = 1
    draw.circle((2, legend-y), radius: 0.25, fill: colors.success.lighten(70%), stroke: colors.primary + 0.8pt)
    draw.content((3, legend-y), [Computed])

    draw.circle((4.5, legend-y), radius: 0.25, fill: colors.warning.lighten(70%), stroke: colors.primary + 0.8pt)
    draw.content((5.8, legend-y), [In worklist])

    draw.circle((7, legend-y), radius: 0.25, fill: colors.bg-code, stroke: colors.primary + 0.8pt)
    draw.content((8, legend-y), [Not visited])

    // Worklist state
    draw.content((4, 0), text(weight: "bold")[Worklist: ${x_2, x_5}$])
  }),
)

#theorem(title: "Worklist Correctness")[
  The worklist algorithm computes the least fixpoint if:
  + Each variable is processed when added to the worklist.
  + Dependencies are correctly tracked.
  + The lattice satisfies ACC.
]

The proof is similar to chaotic iteration.
We observe that only variables whose inputs changed need recomputation.

== Iteration Strategies

The order of processing the worklist affects performance significantly.

#definition(title: "Iteration Order")[
  Common strategies for choosing the next variable:

  - *FIFO* (breadth-first): Process in insertion order.
  - *LIFO* (depth-first): Process most recently added first.
  - *RPO* (reverse postorder): Process following CFG structure.
  - *Priority queue*: Process by estimated impact.
]

#example-box[
  *Reverse postorder for forward dataflow:*

  For forward analyses (information flows with CFG edges), reverse postorder minimizes recomputation.

  Given CFG with postorder $p_n, dots, p_1$, process in order $p_1, dots, p_n$.
  This ensures each node is processed after most of its predecessors.

  For reducible CFGs (no irreducible loops), this converges in $O(d)$ passes where $d$ is loop nesting depth.
]

#figure(
  caption: [Iteration orders on control flow graph],

  cetz.canvas({
    import cetz: draw

    // Helper for CFG nodes
    let draw-cfg-node(name, pos, label, order) = {
      draw.circle(pos, radius: 0.35, name: name, stroke: colors.primary + 1pt)
      draw.content(name, label)
      draw.content((pos.at(0), pos.at(1) - 0.7), text(size: 8pt, fill: colors.accent)[$#order$])
    }

    // Simple CFG with loop
    draw-cfg-node("entry", (2, 5), [Entry], 1)
    draw-cfg-node("b1", (2, 3.5), $B_1$, 2)
    draw-cfg-node("b2", (4, 3.5), $B_2$, 3)
    draw-cfg-node("b3", (2, 2), $B_3$, 4)
    draw-cfg-node("exit", (2, 0.5), [Exit], 5)

    // Edges
    draw.line("entry", "b1", stroke: colors.text-light + 0.8pt, mark: (end: ">"))
    draw.line("b1", "b2", stroke: colors.text-light + 0.8pt, mark: (end: ">"))
    draw.line("b2", "b3", stroke: colors.text-light + 0.8pt, mark: (end: ">"))
    draw.line("b3", "exit", stroke: colors.text-light + 0.8pt, mark: (end: ">"))

    // Back edge (loop)
    draw.bezier("b3.west", "b1.west", (0.8, 2), (0.8, 3.5), stroke: colors.warning + 1pt, mark: (end: ">"))
    draw.content((0.3, 2.7), text(size: 8pt, fill: colors.warning)[Back edge])

    // Annotation
    draw.content((5.5, 2.5), text(size: 9pt, fill: colors.text-light)[RPO: 1, 2, 3, 4, 5])
    draw.content((5.5, 2), text(size: 9pt, fill: colors.text-light)[Minimizes iterations])
  }),
)

== Complexity Analysis

#theorem(title: "Worklist Complexity")[
  For a system with $n$ variables and maximum dependency degree $d$:

  - *Time per iteration*: $O(n d)$ (evaluate each function once).
  - *Number of iterations*: $O(h dot n)$ where $h$ is lattice height.
  - *Total time*: $O(h dot n^2 dot d)$.

  For *forward dataflow on reducible CFGs* with RPO:
  - Iterations: $O("depth of loops")$.
  - Total: $O("loop depth" dot n dot d)$.
]

The key insight: good iteration order reduces the constant factor dramatically!

#proof[
  Each variable can increase at most $h$ times (lattice height).
  With $n$ variables, total number of increases is $<= h dot n$.

  Each increase causes at most $d$ dependents to be re-examined.
  Thus total work is $O(h dot n dot d)$ updates.

  Each update costs $O(n)$ to evaluate the function (in general).
  Total: $O(h dot n^2 dot d)$.

  For RPO on reducible graphs, structural properties ensure $O("loop depth")$ passes suffice, improving the constant.
]

== Widening with Worklist

For infinite-height lattices, combine worklist with widening.

#algorithm(title: "Worklist with Widening")[
  + $W <- {x_1, ..., x_n}$
  + $sigma <- lambda i . bot$
  + $"count" <- lambda i . 0$ $quad slash.double$ Track update count per variable.
  + *while* $W != emptyset$ *do*
    + $x <-$ *remove*$(W)$
    + $"old" <- sigma(x)$
    + $"new" <- f_x (sigma)$
    + $"count"(x) <- "count"(x) + 1$
    + *if* $"count"(x) >$ threshold *then*
      + $"new" <- "old" widen "new"$ $quad slash.double$ Apply widening after threshold.
    + *end if*
    + *if* $"new" != "old"$ *then*
      + $sigma(x) <- "new"$
      + add dependents to $W$
    + *end if*
  + *end while*
  + *return* $sigma$
]

To support this in Rust, we extend our `AbstractDomain` trait with a `widen` method:

```rust
pub trait AbstractDomain: Clone + PartialEq + Debug {
    // ... existing methods ...

    // Default implementation: just join (for finite height lattices)
    fn widen(&self, other: &Self) -> Self {
        self.join(other)
    }
}

// Example: Interval widening
impl AbstractDomain for Interval {
    fn widen(&self, other: &Self) -> Self {
        // If bound is unstable, jump to infinity
        let new_min = if other.min < self.min { NegInf } else { self.min };
        let new_max = if other.max > self.max { PosInf } else { self.max };
        Interval::new(new_min, new_max)
    }
}
```

Typical threshold: 2-3 iterations before widening kicks in.

#example-box[
  *Interval analysis with widening:*

  Loop: `x = 0; while (x < 100) { x = x + 1; }`

  Without widening:
  - Iteration 1: $x in [0, 0]$
  - Iteration 2: $x in [0, 1]$
  - Iteration 3: $x in [0, 2]$
  - ... (100 iterations)

  With widening (threshold = 2):
  - Iteration 1: $x in [0, 0]$
  - Iteration 2: $x in [0, 1]$
  - Iteration 3: $x in [0, 1] widen [0, 2] = [0, +infinity]$ (stabilized!)
]

== Narrowing Iterations

After widening converges to a post-fixpoint, narrow to recover precision.

#algorithm(title: "Two-Phase Worklist")[
  + $slash.double$ Phase 1: Widening (ascending).
  + $sigma_"up" <-$ *widening_iteration*$(thin)$
  + $slash.double$ Phase 2: Narrowing (descending).
  + $W <- {x_1, ..., x_n}$
  + $sigma <- sigma_"up"$
  + *while* $W != emptyset$ *and* *not_too_many_iterations*$(thin)$ *do*
    + $x <-$ *remove*$(W)$
    + $"old" <- sigma(x)$
    + $"new" <- f_x (sigma)$
    + $"narrow" <- "old" triangle "new"$ $quad slash.double$ Apply narrowing.
    + *if* $"narrow" != "old"$ *then*
      + $sigma(x) <- "narrow"$
      + add dependents to $W$
    + *end if*
  + *end while*
  + *return* $sigma$
]

Narrowing is optional but often improves precision significantly.

#figure(
  caption: [Two-phase fixpoint computation with widening and narrowing],

  cetz.canvas({
    import cetz: draw

    // Timeline
    let phase1-end = 5
    let phase2-end = 10

    draw.line((0, 0), (phase2-end + 1, 0), stroke: colors.text-light + 0.8pt, mark: (end: ">"))

    // Phase dividers
    draw.line((phase1-end, -0.5), (phase1-end, 4.5), stroke: (
      paint: colors.text-light,
      thickness: 0.5pt,
      dash: "dashed",
    ))
    draw.content((phase1-end / 2, -1), text(size: 9pt, fill: colors.primary)[Phase 1: Widening])
    draw.content(((phase1-end + phase2-end) / 2, -1), text(size: 9pt, fill: colors.accent)[Phase 2: Narrowing])

    // Precision levels
    draw.line((0, 0), (0, 4), stroke: colors.text-light + 0.5pt)
    draw.content((-0.7, 4.2), text(size: 8pt, fill: colors.text-light)[Precision])

    // Iteration trajectory
    let y-lfp = 2.5
    let y-wide = 3.8

    // Widening phase (ascending)
    draw.line((0, 0.3), (1, 0.8), stroke: colors.primary + 1.2pt)
    draw.line((1, 0.8), (2, 1.5), stroke: colors.primary + 1.2pt)
    draw.line((2, 1.5), (3, y-wide), stroke: (paint: colors.primary, thickness: 1.2pt, dash: "dashed")) // jump!
    draw.line((3, y-wide), (phase1-end, y-wide), stroke: colors.primary + 1.2pt)

    // Narrowing phase (descending)
    draw.line((phase1-end, y-wide), (6, 3.4), stroke: colors.accent + 1.2pt)
    draw.line((6, 3.4), (7, 3.0), stroke: colors.accent + 1.2pt)
    draw.line((7, 3.0), (8, 2.7), stroke: colors.accent + 1.2pt)
    draw.line((8, 2.7), (phase2-end, y-lfp), stroke: colors.accent + 1.2pt)

    // Markers
    draw.circle((3, y-wide), radius: 0.15, fill: colors.warning)
    draw.content((3.8, y-wide), text(size: 8pt, fill: colors.warning)[Widened])

    draw.circle((phase2-end, y-lfp), radius: 0.15, fill: colors.success)
    draw.content((phase2-end + 0.8, y-lfp), text(size: 8pt, fill: colors.success)[Final])

    // True lfp reference
    draw.line((0, y-lfp), (phase2-end + 1, y-lfp), stroke: (paint: colors.text-light, thickness: 0.5pt, dash: "dotted"))
    draw.content((phase2-end + 1.8, y-lfp), text(size: 8pt, fill: colors.text-light)[True lfp])
  }),
)

== Delayed Widening

Applying widening too early loses precision unnecessarily.
*Delayed widening* waits for the analysis to explore "natural" convergence first.

#definition(title: "Widening Delay")[
  Strategies for delaying widening:

  - *Threshold-based*: Apply widening only after $k$ updates to a variable.
  - *Loop-based*: Apply widening only at loop heads.
  - *Heuristic*: Use domain-specific knowledge to identify widening points.
]

#example-box[
  *Loop with bounded iterations:*

  ```rust
  for i in 0..10 {
      x = x + 1;
  }
  ```

  Without delay: After 2 iterations, widen to $[0, +infinity]$, losing bound information.

  With delay (threshold = 5): Natural convergence to $[0, 10]$ before widening triggers.
]

== Chapter Summary

This chapter developed practical fixpoint algorithms:

- *Chaotic iteration* allows flexible update orders with convergence guarantees.
- *Worklist algorithms* track dependencies to minimize recomputation.
- *Iteration strategies* (RPO, FIFO, LIFO) affect performance dramatically.
- *Widening/narrowing* ensure termination for infinite-height lattices with two-phase iteration.
- *Delayed widening* improves precision by waiting for natural convergence.

These techniques are essential for implementing efficient program analyzers.
