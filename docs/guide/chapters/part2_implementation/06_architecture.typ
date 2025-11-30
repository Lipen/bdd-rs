#import "../../theme.typ": *

= Manager-Centric Architecture <ch-architecture>

Picture a library where every book can reference any page in any other book, but the references only work because all books live on the same shelf.
Move a book to a different shelf, and the references shatter into meaningless numbers.

This is the essence of BDD architecture.
Every BDD node can reference any other node, and these references *must* remain consistent across the entire system.
This chapter explains why BDD libraries universally adopt a *manager-centric architecture* and how `bdd-rs` implements it.

== The Central Challenge: Sharing

What makes BDDs powerful is also what makes them tricky to implement: *maximal sharing*.

Consider building the BDD for $f = (a and b) or c$.
Now build $g = (a and b) or d$.
Both formulas contain the subexpression $(a and b)$.
In a well-designed BDD library, this subexpression is represented *exactly once* --- both $f$ and $g$ point to the same physical nodes in memory.

#figure(
  cetz.canvas(length: 1cm, {
    import cetz.draw: *

    // Shared subgraph demonstration
    let shared-pos = (4, 2)
    let a-pos = (4, 4)
    let b-pos = (4, 2.5)
    let zero = (3.5, 0.8)
    let one = (4.5, 0.8)

    // f = (a AND b) OR c
    let f-c-pos = (2, 3)
    let f-label = (0.5, 4.5)

    // g = (a AND b) OR d
    let g-d-pos = (6, 3)
    let g-label = (7.5, 4.5)

    // Draw the shared a AND b subgraph
    bdd-terminal-node(zero, 0, name: "zero")
    bdd-terminal-node(one, 1, name: "one")
    bdd-decision-node(a-pos, "a", name: "a")
    bdd-decision-node(b-pos, "b", name: "b")

    // a -> 0 (low), a -> b (high)
    bdd-low-edge((a-pos.at(0) - 0.3, a-pos.at(1) - 0.4), (zero.at(0) + 0.35, zero.at(1) + 0.7))
    bdd-high-edge((a-pos.at(0), a-pos.at(1) - 0.4), (b-pos.at(0), b-pos.at(1) + 0.4))

    // b -> 0 (low), b -> 1 (high)
    bdd-low-edge((b-pos.at(0) - 0.3, b-pos.at(1) - 0.4), (zero.at(0) + 0.2, zero.at(1) + 0.3))
    bdd-high-edge((b-pos.at(0) + 0.3, b-pos.at(1) - 0.4), (one.at(0) - 0.2, one.at(1) + 0.3))

    // f's c node
    bdd-decision-node(f-c-pos, "c", name: "c")
    // c -> a (low for OR structure), c -> 1 (high)
    bdd-low-edge((f-c-pos.at(0) + 0.35, f-c-pos.at(1) - 0.2), (a-pos.at(0) - 0.35, a-pos.at(1) + 0.2))
    bdd-high-edge((f-c-pos.at(0) - 0.2, f-c-pos.at(1) - 0.4), (one.at(0) - 0.5, one.at(1) + 0.5))

    // g's d node
    bdd-decision-node(g-d-pos, "d", name: "d")
    // d -> a (low), d -> 1 (high)
    bdd-low-edge((g-d-pos.at(0) - 0.35, g-d-pos.at(1) - 0.2), (a-pos.at(0) + 0.35, a-pos.at(1) + 0.2))
    bdd-high-edge((g-d-pos.at(0) + 0.2, g-d-pos.at(1) - 0.4), (one.at(0) + 0.5, one.at(1) + 0.5))

    // Labels
    content(f-label, text(fill: colors.primary, weight: "bold", $f$))
    content(g-label, text(fill: colors.primary, weight: "bold", $g$))

    // Highlight shared region
    rect(
      (2.8, 1.4),
      (5.2, 4.6),
      stroke: (paint: colors.accent, thickness: 2pt, dash: "dashed"),
      radius: 8pt,
    )
    content((4, 5), text(size: 0.8em, fill: colors.accent)[shared $(a and b)$ subgraph])
  }),
  caption: [Two BDDs sharing a common subgraph. Both $f$ and $g$ reference the same nodes for $(a and b)$.],
)

This sharing requires centralized control.
If $f$ and $g$ lived in separate data structures, they couldn't share nodes.
Every BDD library solves this the same way: a *manager* that owns all nodes.

== Why a Manager?

The manager pattern is not a stylistic choice --- it's a necessity.
BDDs need four guarantees that only centralized control can provide:

#table(
  columns: (auto, 1fr),
  align: (left, left),
  table.header([*Requirement*], [*Why It Needs a Manager*]),
  [*Shared storage*], [Nodes must live in one pool so references work across all BDDs],
  [*Hash consing*], [Before creating a node, check if it exists --- needs global view],
  [*Consistent ordering*], [All BDDs must agree on variable order],
  [*Shared caches*], [Operation results must be reusable everywhere],
)

Without a manager, two BDDs built independently would represent the same function with different structures.
The fundamental $O(1)$ equivalence check --- "are these two pointers equal?" --- would break.

#insight-box[
  Every major BDD library uses a manager:
  - *CUDD*: `DdManager` (the gold standard)
  - *BuDDy*: Global manager via `bdd_init()`
  - *Sylvan*: Lock-free parallel manager
  - *bdd-rs*: `Bdd` struct with interior mutability
]

== The Bdd Manager in bdd-rs

Here is the actual `Bdd` struct from the source code:

```rust
pub struct Bdd {
    /// Node storage: index 0 is the terminal node
    nodes: RefCell<Vec<Node>>,
    /// Free node indices available for reuse
    free_set: RefCell<HashSet<NodeId>>,

    /// Operation cache (memoizes ITE results)
    cache: RefCell<Cache<OpKey, Ref>>,
    /// Size computation cache
    size_cache: RefCell<Cache<Ref, u64>>,

    /// Variable ordering: level → variable
    var_order: RefCell<Vec<Var>>,
    /// Reverse mapping: variable → level
    level_map: RefCell<HashMap<Var, Level>>,

    /// Per-level hash tables for uniqueness
    subtables: RefCell<Vec<Subtable>>,

    /// Next variable ID to allocate
    next_var_id: Cell<u32>,
    /// Configuration settings
    config: BddConfig,
}
```

Let us visualize how these components fit together:

#figure(
  cetz.canvas(length: 1cm, {
    import cetz.draw: *

    // Main manager box
    rect(
      (0, 0),
      (12, 8),
      fill: colors.bg-subtle,
      stroke: 2pt + colors.primary,
      radius: 8pt,
      name: "manager",
    )
    content((6, 8.4), text(weight: "bold", size: 1em, fill: colors.primary, font: fonts.heading)[Bdd Manager])

    // Node storage
    arch-box(
      (0.3, 7.5),
      3.5,
      3,
      "nodes: Vec<Node>",
      (
        "[0] terminal",
        "[1] x → (0, 1)",
        "[2] y → (0, @1)",
        "...",
      ),
      fill-color: colors.box-definition,
    )

    // Free set
    arch-box(
      (0.3, 4.2),
      3.5,
      1.3,
      "free_set",
      (
        "recycled indices",
      ),
      fill-color: colors.box-insight.lighten(30%),
    )

    // Subtables
    arch-box(
      (4.2, 7.5),
      3.5,
      3,
      "subtables",
      (
        "Level 0: hash table",
        "Level 1: hash table",
        "Level 2: hash table",
        "...",
      ),
      fill-color: colors.box-example,
    )

    // Cache
    arch-box(
      (8.1, 7.5),
      3.5,
      2.2,
      "cache: ITE results",
      (
        "(f, g, h) → result",
        "memoized ops",
      ),
      fill-color: colors.box-warning.lighten(30%),
    )

    // Size cache
    arch-box(
      (8.1, 5),
      3.5,
      1.5,
      "size_cache",
      (
        "f → node count",
      ),
      fill-color: colors.box-warning.lighten(40%),
    )

    // Variable ordering
    arch-box(
      (4.2, 4.2),
      3.5,
      2.5,
      "Variable Ordering",
      (
        "var_order: [x, y, z]",
        "level_map: x→0, y→1",
        "next_var_id: 4",
      ),
      fill-color: colors.box-theorem.lighten(30%),
    )

    // Config
    arch-box(
      (8.1, 3.2),
      3.5,
      1.5,
      "config",
      (
        "initial capacity, etc.",
      ),
      fill-color: colors.bg-code,
    )

    // Ref output arrow
    line((6, 0), (6, -0.8), stroke: 2pt + colors.accent, mark: (end: ">", fill: colors.accent))
    content((6, -1.3), text(fill: colors.accent, weight: "bold")[`Ref`: 32-bit handle])

    // Ref bit layout
    rect((3.5, -2.8), (8.5, -1.8), stroke: 1pt + colors.line, radius: 4pt)
    rect((3.5, -2.8), (7.5, -1.8), fill: colors.box-definition)
    rect((7.5, -2.8), (8.5, -1.8), fill: colors.box-warning)
    content((5.5, -2.3), text(size: 0.8em)[31-bit node index])
    content((8, -2.3), text(size: 0.8em)[C])
    content((6, -3.2), text(size: 0.7em, fill: colors.text-muted)[C = complement bit (negation)])
  }),
  caption: [Architecture of the `Bdd` manager showing all major components.],
)

=== Interior Mutability

Notice all the `RefCell` wrappers?
They enable *interior mutability* --- the ability to modify data through a shared reference (`&self`).

This is a deliberate ergonomic choice.
Without it, every BDD operation would require `&mut self`, meaning you could not hold multiple `Ref` values while building a formula:

```rust
// With interior mutability (what we have):
let x = bdd.mk_var(1);  // &self
let y = bdd.mk_var(2);  // &self
let f = bdd.apply_and(x, y);  // &self - x and y still valid!

// Without (hypothetical):
let x = bdd.mk_var(1);  // &mut self
// x is now invalid because we'd need &mut self again!
```

The trade-off: runtime borrow checking instead of compile-time.
In practice, BDD operations don't nest in ways that cause panics.

== References: The User-Facing Handle

Users never touch `Node` structs directly.
Instead, they work with `Ref` --- a compact 32-bit handle:

#figure(
  cetz.canvas(length: 1cm, {
    import cetz.draw: *

    // Bit layout
    let total-width = 12
    let index-width = 10.5
    let comp-width = 1.5

    // Index bits
    rect((0, 0), (index-width, 1), radius: (west: 3pt), fill: colors.box-definition, stroke: 1pt + colors.primary)
    content((index-width / 2, 0.5), text(weight: "semibold")[Node Index (31 bits)])

    // Complement bit
    rect(
      (index-width, 0),
      (total-width, 1),
      radius: (east: 3pt),
      fill: colors.box-warning,
      stroke: 1pt + colors.warning,
    )
    content((index-width + comp-width / 2, 0.5), text(weight: "semibold")[C])

    // Labels below
    content((index-width / 2, -0.4), text(size: 0.8em, fill: colors.text-muted)[Points to node in storage])
    content((index-width + comp-width / 2, -0.4), text(size: 0.8em, fill: colors.text-muted)[Neg?])

    // Examples
    content(
      (0, -1.2),
      align(left)[
        #set text(size: 0.8em)
        *Examples:*
        - `Ref::ONE` = `0b...0` (terminal, positive)
        - `Ref::ZERO` = `0b...1` (terminal, negated)
        - Node 5, positive = `0b...1010`
        - Node 5, negated = `0b...1011`
      ],
      anchor: "north-west",
    )
  }),
  caption: [Bit layout of `Ref`: 31 bits for node index, 1 bit for complement flag.],
)

The complement bit is the key to $O(1)$ negation:

```rust
impl Neg for Ref {
    fn neg(self) -> Self {
        Self(self.0 ^ 1)  // Just flip the lowest bit!
    }
}
```

Instead of traversing a BDD and creating new nodes for $not f$, we simply flip one bit.
This single optimization cascades through the entire library, making XOR, equivalence, and implication faster.

#comparison-table(
  [*Aspect*],
  [*Ref*],
  [*Node*],
  [Size],
  [4 bytes],
  [24 bytes],
  [Copy],
  [Trivial],
  [Trivial but larger],
  [Negation],
  [$O(1)$ bit flip],
  [Would need new node],
  [Comparison],
  [Single integer compare],
  [Field-by-field],
)

== The API Surface

The manager exposes operations through method calls.
Here's a quick tour:

=== Construction

```rust
// Create variables (1-indexed by convention)
let x = bdd.mk_var(1);
let y = bdd.mk_var(2);

// Build cubes and clauses efficiently
let cube = bdd.mk_cube([1, -2, 3]);    // x₁ ∧ ¬x₂ ∧ x₃
let clause = bdd.mk_clause([1, -2, 3]); // x₁ ∨ ¬x₂ ∨ x₃
```

=== Boolean Operations

```rust
// Binary operations
let f_and_g = bdd.apply_and(f, g);
let f_or_g = bdd.apply_or(f, g);
let f_xor_g = bdd.apply_xor(f, g);

// The universal if-then-else
let result = bdd.apply_ite(f, g, h);  // f ? g : h

// Negation is just syntax
let not_f = -f;
```

=== Queries

```rust
// O(1) checks (after construction)
bdd.is_zero(f)   // Unsatisfiable?
bdd.is_one(f)    // Tautology?
f == g           // Equivalent? (pointer compare!)

// O(|f|) operations
bdd.size(f)              // Node count
bdd.sat_count(f, n_vars) // Solution count
```

=== Quantification

```rust
// Existential: ∃x. f  (is there some x making f true?)
let ex = bdd.exists(f, [Var::new(1)]);

// Universal: ∀x. f  (is f true for all x?)
let fa = bdd.forall(f, [Var::new(1)]);

// Relational product: ∃vars. (f ∧ g)
let rp = bdd.rel_product(f, g, &quant_vars);
```

== Creating and Configuring

For most uses, the default configuration works well:

```rust
let bdd = Bdd::default();
```

For large problems, customize the initial capacities:

```rust
use bdd_rs::bdd::{Bdd, BddConfig};

let config = BddConfig::default()
    .with_initial_nodes(1 << 20)  // ~1M nodes
    .with_cache_bits(18);         // 256K cache entries

let bdd = Bdd::with_config(config);
```

#warning-box(title: "Cross-Manager Pitfall")[
  A `Ref` is only valid for its originating manager.
  Mixing them causes silent corruption:

  ```rust
  let bdd1 = Bdd::default();
  let bdd2 = Bdd::default();
  let x = bdd1.mk_var(1);
  // WRONG: x is from bdd1!
  // bdd2.apply_and(x, bdd2.mk_var(2));  // Undefined behavior
  ```

  Rust's type system cannot catch this --- the indices look the same.
  Be careful when working with multiple managers.
]

== What's Next

The following chapters dive deep into each component:

- *@ch-node-representation*: How nodes store variable, children, and hash data
- *@ch-unique-table*: Per-level subtables for $O(1)$ node lookup
- *@ch-apply-algorithm*: The ITE algorithm that powers all operations
- *@ch-caching*: How memoization prevents exponential blowup
- *@ch-complement-edges*: The elegant trick behind $O(1)$ negation

