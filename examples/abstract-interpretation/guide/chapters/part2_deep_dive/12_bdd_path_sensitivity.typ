#import "../../theme.typ": *

= BDD Path Sensitivity <ch-bdd-path>

#reading-path(path: "implementation")

@ch-domain-combinations established the theory of *Trace Partitioning* and *Reduced Products*.
We now implement the "Killer Feature": using Binary Decision Diagrams (BDDs) as the trace partitioning domain.

This architecture solves the "Diamond Problem" (loss of precision at join points) by maintaining separate abstract states for different execution paths, efficiently compressed by the BDD.

== The BDD Product Domain

We define a generic `BddProductDomain<D>` that combines a BDD (control) with an arbitrary abstract domain `D` (data).

#definition(title: "BDD Product State")[
  A state in the BDD product domain is a pair $(f, d)$ where:
  - $f$: A BDD representing the set of active control paths.
  - $d$: An element of domain $D$ representing data properties on those paths.
]

In Rust, we implement this using the `bdd-rs` library.

```rust
pub struct BddProductDomain<D: AbstractDomain> {
    bdd: Rc<Bdd>,           // Shared BDD manager
    control: Ref,           // The path condition 'f'
    data: D,                // The data state 'd'
}
```

#info-box(title: "Manager-Centric Design")[
  Note the `Rc<Bdd>`.
  In `bdd-rs`, the `Bdd` struct is the manager that owns all nodes.
  The `control` field is just a `Ref` (a lightweight integer handle).
  All operations must go through the manager: `self.bdd.and(self.control, other.control)`.
]

== Implementing Lattice Operations

The lattice operations for the product domain combine the control and data components.

=== Join (Union)

When merging two control-flow paths, we join the path conditions (logical OR) and the data states (domain join).

```rust
fn join(&self, other: &Self) -> Self {
    // Control: Union of paths
    let control = self.bdd.apply_or(self.control, other.control);

    // Data: Join of data facts
    let data = self.data.join(&other.data);

    BddProductDomain {
        bdd: self.bdd.clone(),
        control,
        data
    }
}
```

=== Meet (Intersection)

Used when paths converge or when applying constraints.

```rust
fn meet(&self, other: &Self) -> Self {
    let control = self.bdd.apply_and(self.control, other.control);
    let data = self.data.meet(&other.data);
    BddProductDomain { bdd: self.bdd.clone(), control, data }
}
```

== The Transfer Function: Assume & Filter

The `assume` function (filtering) updates *both* the BDD control state and the data state when the program encounters a condition `if x > 0`.

+ *Control Update*: We AND the current path condition with the BDD variable representing `x > 0`.
+ *Data Update*: We refine the data domain using `assume(x > 0)`.

```rust
fn assume(&self, condition: &Expr) -> Self {
    // 1. Map condition to BDD variable
    let cond_bdd = self.map_condition_to_bdd(condition);
    let new_control = self.bdd.apply_and(self.control, cond_bdd);

    // 2. Refine data domain
    let new_data = self.data.assume(condition);

    BddProductDomain {
        bdd: self.bdd.clone(),
        control: new_control,
        data: new_data,
    }
}
```

This ensures that on the "true" branch, we know `x > 0` in both the BDD (for path tracking) and the data domain (for value analysis).

== Reduction: The "Killer" Interaction

The *Reduced Product* (@ch-domain-combinations) allows the BDD to refine the data domain.
If the BDD knows that a certain path is impossible (control is `false`), the data state should be `bottom`.
More advanced reduction can extract facts from the BDD to refine the data.

#example-box(title: "Reduction Example")[
  If `control` implies `x > 0` (because we are on the true branch of an earlier check), we can tell the Interval domain to clip negative values of `x`.
]

#figure(
  caption: [BDD Product State: Control + Data],

  cetz.canvas({
    import cetz: draw

    // BDD Component
    draw.content((0, 4), text(weight: "bold")[Control (BDD)])
    draw.circle((0, 3), radius: 0.3, name: "root", fill: colors.bg-code, stroke: colors.primary + 1pt)
    draw.content("root", [$x_1$])

    draw.circle((-1, 1.5), radius: 0.3, name: "left", fill: colors.bg-code, stroke: colors.primary + 1pt)
    draw.content("left", [$x_2$])

    draw.rect((0.7, 1.2), (1.3, 1.8), name: "zero", fill: colors.error.lighten(70%), stroke: colors.error + 1pt)
    draw.content("zero", [0])

    draw.rect((-1.3, -0.3), (-0.7, 0.3), name: "one", fill: colors.success.lighten(70%), stroke: colors.success + 1pt)
    draw.content("one", [1])

    // Edges
    draw.line(
      "root.south-west",
      "left.north",
      stroke: (paint: colors.text-light, dash: "dashed"),
      mark: (end: ">", stroke: (dash: "solid")),
    ) // Low
    draw.line("root.south-east", "zero.north", stroke: colors.text-light + 0.8pt, mark: (end: ">")) // High

    draw.line("left.south", "one.north", stroke: colors.text-light + 0.8pt, mark: (end: ">")) // High
    draw.line(
      "left.south-east",
      "zero.west",
      stroke: (paint: colors.text-light, dash: "dashed"),
      mark: (end: ">", stroke: (dash: "solid")),
    ) // Low

    // Data Component
    draw.content((5, 4), text(weight: "bold")[Data (Intervals)])
    draw.rect((3.5, 1), (6.5, 3), name: "data", fill: colors.secondary.lighten(80%), stroke: colors.secondary + 1pt)
    draw.content("data", align(center)[
      $x in [0, 100]$ \
      $y in [10, 20]$
    ])

    // Product Link
    draw.line((1.5, 2), (3.5, 2), stroke: (paint: colors.accent, thickness: 2pt), mark: (end: ">", start: ">"))
    draw.content((2.5, 2.3), text(size: 9pt, fill: colors.accent)[Linked])
  }),
)

== Variable Ordering and Performance

BDD performance is sensitive to variable ordering.
In `bdd-rs`, variables are 1-indexed.
For path sensitivity, a good heuristic is to order variables by their appearance in the control flow graph (CFG).

#warning-box(title: "Dynamic Variable Allocation")[
  If you allocate BDD variables dynamically as you encounter branches, ensure you reuse the *same* variable for the *same* condition.
  Mapping `x > 0` to $v_1$ at line 10 and $v_2$ at line 20 destroys the correlation.
  Use a canonical mapping: `Map<Condition, BddVar>`.
]

== Case Study: Array Access Safety

Let's see this in action on a buffer processing routine.
This is a classic source of vulnerabilities: checking a size field but failing to respect it during access.

```rust
fn process_data(arr: &[u8], size: usize) {
    // 1. Check size
    if size < 4 { return; }

    // 2. Access metadata (safe because size >= 4)
    let meta = arr[0..4];

    // 3. Check content type
    if meta[0] == 0x1 {
        // 4. Access content (requires size >= 8)
        if size >= 8 {
            let content = arr[4..8];
        }
    }
}
```

=== Detailed Analysis Trace

Let's walk through this analysis step by step, tracking how the BDD path condition and data domain evolve together.

*At entry:*
The variable `size` has interval $[0, infinity]$ (unknown but non-negative).
The path condition is True (all paths feasible initially).

*After first branch (`size < 4`):*
We take the false branch (fallthrough), meaning the condition `size < 4` is false.
The BDD adds constraint $not v_1$ (where $v_1$ represents `size < 4`).
The data domain refines: `size` $in [4, infinity]$.

*At first array access (`arr[0..4]`):*
Safety requires `size >= 4` to access indices 0 through 3.
The data domain confirms $[4, infinity] subset.eq [4, infinity]$, so this access is safe.

*After third branch (`meta[0] == 0x1`):*
We enter the true branch, so the BDD adds $v_2$ (representing `meta[0] == 0x1`).
The path condition is now $not v_1 and v_2$.

*After fourth branch (`size >= 8`):*
We enter the true branch again, so the BDD adds $v_3$ (representing `size >= 8`).
The path condition becomes $not v_1 and v_2 and v_3$.
The data domain refines: `size` $in [8, infinity]$.

*At second array access (`arr[4..8]`):*
Safety requires `size >= 8` to access indices 4 through 7.
The data domain confirms $[8, infinity] subset.eq [8, infinity]$, so this access is safe.

Without path sensitivity (BDD), merging the paths after Branch 4 would lose the correlation between "we are inside the `size >= 8` block" and the variable `size`.
The BDD keeps these states distinct if we use partitioning, or allows us to recover the condition if we use the product domain.

== Performance Considerations

BDD-based path sensitivity trades precision for computational cost.
Managing this tradeoff determines whether an analyzer scales to real programs.

=== BDD Size Growth

Well-structured control flow produces compact BDDs.
A function with $n$ sequential conditionals generates $O(n)$ nodes when variable ordering follows control flow.
However, complex Boolean combinations can trigger exponential blowup to $O(2^n)$ nodes.

*Key factors affecting size:*
- *Variable ordering*: Allocate BDD variables following reverse postorder CFG traversal.
  This groups related conditions together, maximizing structural sharing.
- *Loop complexity*: Deeply nested loops with many exit conditions stress the representation.
- *Boolean structure*: Arbitrary functions over distant program points prevent sharing.

*Mitigation approaches:*
- Trigger garbage collection at loop headers or when node count exceeds thresholds (e.g., 10,000 nodes).
- Impose hard node limits per function (e.g., 100,000 nodes).
  When exceeded, widen aggressively or fall back to path-insensitive mode.

=== Loop Widening

Loops create infinite path families that require finite representation.
After $k$ iterations (typically $k = 2$), replace the path condition with `True`:

```rust
fn widen_bdd(&self, iteration: usize) -> Ref {
    if iteration >= 2 {
        self.bdd.constant(true)  // Abandon path tracking
    } else {
        self.control
    }
}
```

This abandons path sensitivity within loops, reverting to path-insensitive analysis.
More sophisticated strategies preserve conditions guarding safety checks while dropping routine control flow.

=== Performance Profiling

Identify whether BDD operations or data domain operations dominate:

- *Cheap data domains* (intervals, signs): BDD operations dominate.
  Focus on variable ordering and garbage collection.
- *Expensive data domains* (polyhedra, automata): Domain operations dominate.
  BDD overhead is negligible; consider domain simplifications instead.
- *Typical case* (BDDs + intervals): Expect some overhead versus path-insensitive analysis.

=== Practical Guidelines

+ Use widening threshold $k=2$.
  Most programs converge quickly; higher thresholds rarely improve precision.
+ Allocate BDD variables in reverse postorder.
  This single heuristic handles most ordering challenges.
+ Monitor node count during iteration.
  Spikes indicate problem regions requiring specialized handling.
+ For complex functions, fall back to path-insensitive analysis automatically.
  Hybrid approaches maintain soundness while bounding worst-case cost.

#chapter-summary[
  This chapter made path-sensitive abstract interpretation concrete through the BDD-based product domain implementation.

  The *`BddProductDomain`* architecture combines a BDD manager (tracking feasible paths) with an arbitrary data domain (tracking variable values).
  This separation enables *orthogonal composition* --- switching between different data abstractions without modifying the path-tracking mechanism.

  *Lattice operations* (`join`, `meet`) operate component-wise: combine path conditions through Boolean operations, merge data states through domain operations.
  The critical *`assume` operation* updates both layers: conjoining conditions to the path BDD and refining data facts based on the assumption.

  This architecture enables *automatic infeasible path detection*.
  When a path BDD becomes False through contradiction, that execution trace is proven unreachable.
  The executor can prune entire branches without explicit satisfiability checking.

  The implementation demonstrates path sensitivity's *practical value*: verifying properties dependent on control flow sequences, like array bounds under conditional guards or authorization checks under role conditions.
]
