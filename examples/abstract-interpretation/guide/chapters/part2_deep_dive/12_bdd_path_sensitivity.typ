#import "../../theme.typ": *

= BDD Path Sensitivity <ch-bdd-path>

#reading-path(path: "implementation")

In @ch-domain-combinations, we established the theory of *Trace Partitioning* and *Reduced Products*.
Now, we will implement the "Killer Feature" of our analyzer.
We will use Binary Decision Diagrams (BDDs) as the trace partitioning domain.

This architecture solves the "Diamond Problem" (loss of precision at join points).
It maintains separate abstract states for different execution paths, efficiently compressed by the BDD.

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

The magic happens in the `assume` function (filtering).
When the program encounters a condition `if x > 0`, we update *both* the BDD control state and the data state.

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
    draw.line("root.south-west", "left.north", stroke: (paint: colors.text-light, dash: "dashed"), mark: (end: ">")) // Low
    draw.line("root.south-east", "zero.north", stroke: colors.text-light + 0.8pt, mark: (end: ">")) // High

    draw.line("left.south", "one.north", stroke: colors.text-light + 0.8pt, mark: (end: ">")) // High
    draw.line("left.south-east", "zero.west", stroke: (paint: colors.text-light, dash: "dashed"), mark: (end: ">")) // Low

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

== Case Study: Packet Filter Safety

Let's see this in action on a packet filter rule.

```rust
fn filter(packet: &Packet) {
    if packet.proto == TCP {
        // Safe access to TCP header?
        let port = packet.tcp.dst_port;
    }
}
```

*Analysis Trace:*

+ *Entry*: `packet` is generic.
+ *Branch*: `packet.proto == TCP`.
  - BDD adds variable $v_1$ (`proto == TCP`).
  - Control state becomes $v_1$ (true branch).
+ *Access `packet.tcp`*:
  - The analyzer asks: "Is it safe to access the TCP union field?"
  - Data domain might not track union tags precisely.
  - *But* the BDD control state is $v_1$.
  - This implies `proto == TCP` is true.
  - The analyzer proves safety using the path condition.

== Performance Considerations

- *BDD Size*: For typical control flow (structured programming), BDDs remain small.
- *Widening*: We must widen the BDD to prevent infinite growth in loops.
  A simple strategy is to stop tracking path conditions after $N$ iterations (force `control = true`).

#chapter-summary[
  - The `BddProductDomain` combines a BDD manager with a data domain.

  - `join` and `meet` operate component-wise.

  - `assume` updates both the path condition (BDD) and the data facts.

  - This architecture enables precise, path-sensitive analysis that can verify properties dependent on control flow, like union access in guarded blocks.
]
