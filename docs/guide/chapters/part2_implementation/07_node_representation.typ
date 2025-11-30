#import "../../theme.typ": *

= Node Representation <ch-node-representation>

At the lowest level, a BDD is just memory: bytes laid out in a particular way.
How those bytes are organized directly impacts every operation's performance --- from cache locality during traversals to memory consumption with millions of nodes.

This chapter explores `bdd-rs`'s node structure, the type-safe wrappers that prevent common bugs, and the memory layout decisions that keep things fast.

== The Node Structure

Each BDD node represents a Shannon decomposition:

$ f = (not v and f_"low") or (v and f_"high") $

The `Node` struct captures this with five fields:

```rust
#[derive(Debug, Copy, Clone)]
pub struct Node {
    pub variable: Var,    // Decision variable at this node
    pub low: Ref,         // Child when variable = 0
    pub high: Ref,        // Child when variable = 1
    pub next: NodeId,     // Hash collision chain pointer
    hash: u64,            // Precomputed hash for fast lookup
}
```

#figure(
  cetz.canvas(length: 1cm, {
    import cetz.draw: *

    // Memory layout visualization
    content((6, 6.5), text(weight: "bold", size: 1em)[Node Memory Layout (24 bytes)])

    let y = 4
    let field-height = 0.8

    // Field boxes
    rect(
      (0, y),
      (2, y + field-height),
      fill: colors.box-definition.lighten(30%),
      stroke: 1pt + colors.primary,
      radius: 2pt,
    )
    content((1, y + field-height / 2), text(size: 0.8em)[`variable`])

    rect(
      (2.2, y),
      (4.2, y + field-height),
      fill: colors.box-example.lighten(30%),
      stroke: 1pt + colors.success.lighten(20%),
      radius: 2pt,
    )
    content((3.2, y + field-height / 2), text(size: 0.8em)[`low`])

    rect(
      (4.4, y),
      (6.4, y + field-height),
      fill: colors.box-example.lighten(30%),
      stroke: 1pt + colors.success.lighten(20%),
      radius: 2pt,
    )
    content((5.4, y + field-height / 2), text(size: 0.8em)[`high`])

    rect(
      (6.6, y),
      (8.6, y + field-height),
      fill: colors.box-warning.lighten(30%),
      stroke: 1pt + colors.warning.lighten(20%),
      radius: 2pt,
    )
    content((7.6, y + field-height / 2), text(size: 0.8em)[`next`])

    rect(
      (8.8, y),
      (12.8, y + field-height),
      fill: colors.box-insight.lighten(30%),
      stroke: 1pt + colors.info.lighten(20%),
      radius: 2pt,
    )
    content((10.8, y + field-height / 2), text(size: 0.8em)[`hash`])

    // Size labels
    content((1, y - 0.4), text(size: 0.8em, fill: colors.text-muted)[4B])
    content((3.2, y - 0.4), text(size: 0.8em, fill: colors.text-muted)[4B])
    content((5.4, y - 0.4), text(size: 0.8em, fill: colors.text-muted)[4B])
    content((7.6, y - 0.4), text(size: 0.8em, fill: colors.text-muted)[4B])
    content((10.8, y - 0.4), text(size: 0.8em, fill: colors.text-muted)[8B])

    // Role annotations
    content((1, y + 1.4), align(center, text(size: 0.8em, fill: colors.primary)[Decision\ variable]))
    content((4.3, y + 1.4), align(center, text(size: 0.8em, fill: colors.success)[Children\ (Ref handles)]))
    content((7.6, y + 1.4), align(center, text(size: 0.8em, fill: colors.warning)[Hash\ chain]))
    content((10.8, y + 1.4), align(center, text(size: 0.8em, fill: colors.info)[Precomputed\ hash]))

    // Explanation
    content((6, 3), align(center)[
      #set text(size: 0.8em)
      `next` enables *intrusive hashing* --- collision chains live in the nodes themselves.
    ])
  }),
  caption: [Node memory layout: 24 bytes with precomputed hash and intrusive collision chain.],
)

#info-box(title: "Why Store the Hash?")[
  Computing `hash(variable, low, high)` requires three multiplications and XORs.
  By precomputing and storing it in the node, we avoid recalculating during hash table operations.
  This trades 8 bytes of memory per node for faster lookups.
]

The `next` field implements *intrusive hashing* --- nodes themselves form the collision chains for the hash table, rather than using a separate wrapper struct.
This CUDD-inspired design eliminates allocation overhead and improves cache locality.

== Terminal Nodes

The terminal node (representing both $top$ and $bot$) receives special handling:

```rust
// During manager construction:
let mut nodes = Vec::with_capacity(capacity);
nodes.push(Node::new(Var::ZERO, Ref::INVALID, Ref::INVALID));

// Terminal references:
let one = Ref::positive(0);   // @0 (non-negated terminal)
let zero = -one;               // ~@0 (negated terminal)
```

Key properties of the terminal:

+ *Index 0*: The terminal always lives at index 0 in the node array
+ *Variable = 0*: `Var::ZERO` marks this as a terminal, not a decision node
+ *Invalid children*: `Ref::INVALID` signals that children don't exist
+ *Both constants share it*: `one = @0` and `zero = ~@0` (complement)

This design means checking for terminals is a simple index comparison:

```rust
impl Bdd {
    pub fn is_terminal(&self, r: Ref) -> bool {
        r.id().raw() == 0
    }

    pub fn is_one(&self, r: Ref) -> bool {
        r.raw() == self.one.raw()
    }

    pub fn is_zero(&self, r: Ref) -> bool {
        r.raw() == self.zero.raw()
    }
}
```

== Type-Safe Wrappers

`bdd-rs` uses the *newtype pattern* extensively to prevent mixing up different indices:

#figure(
  cetz.canvas(length: 1cm, {
    import cetz.draw: *

    content((6, 6), text(weight: "bold", size: 1em)[Type-Safe Index Wrappers])

    // Four type boxes arranged in a grid
    let y1 = 4.5
    let y2 = 3.5

    // NodeId
    rect((0.5, y1), (3, y1 + 1), fill: colors.box-definition.lighten(30%), stroke: 1pt + colors.primary, radius: 4pt)
    content((1.75, y1 + 0.7), text(size: 0.8em, weight: "semibold")[`NodeId(u32)`])
    content((1.75, y1 + 0.3), text(size: 0.7em, fill: colors.text-muted)[→ nodes array])

    // Var
    rect(
      (3.5, y1),
      (6, y1 + 1),
      fill: colors.box-example.lighten(30%),
      stroke: 1pt + colors.success.lighten(20%),
      radius: 4pt,
    )
    content((4.75, y1 + 0.7), text(size: 0.8em, weight: "semibold")[`Var(u32)`])
    content((4.75, y1 + 0.3), text(size: 0.7em, fill: colors.text-muted)[variable ID (1+)])

    // Level
    rect(
      (6.5, y1),
      (9, y1 + 1),
      fill: colors.box-warning.lighten(30%),
      stroke: 1pt + colors.warning.lighten(20%),
      radius: 4pt,
    )
    content((7.75, y1 + 0.7), text(size: 0.8em, weight: "semibold")[`Level(u32)`])
    content((7.75, y1 + 0.3), text(size: 0.7em, fill: colors.text-muted)[ordering position])

    // Ref
    rect(
      (9.5, y1),
      (12, y1 + 1),
      fill: colors.box-insight.lighten(30%),
      stroke: 1pt + colors.info.lighten(20%),
      radius: 4pt,
    )
    content((10.75, y1 + 0.7), text(size: 0.8em, weight: "semibold")[`Ref(u32)`])
    content((10.75, y1 + 0.3), text(size: 0.7em, fill: colors.text-muted)[id + complement])

    // Ref bit layout detail
    content((6, y2 + 0.3), text(size: 0.9em, weight: "semibold")[Ref Bit Layout:])

    let bit-y = y2 - 0.5
    // 31-bit node index
    rect((2, bit-y), (9, bit-y + 0.6), fill: colors.box-definition.lighten(40%), stroke: 0.5pt + colors.primary)
    content((5.5, bit-y + 0.3), text(size: 0.7em)[31-bit NodeId])

    // 1-bit complement
    rect((9, bit-y), (10, bit-y + 0.6), fill: colors.box-warning.lighten(30%), stroke: 0.5pt + colors.warning)
    content((9.5, bit-y + 0.3), text(size: 0.7em)[C])

    // Bit numbers
    content((2, bit-y - 0.3), text(size: 0.7em, fill: colors.text-muted)[31])
    content((9, bit-y - 0.3), text(size: 0.7em, fill: colors.text-muted)[1])
    content((10, bit-y - 0.3), text(size: 0.7em, fill: colors.text-muted)[0])

    // Explanation
    content((6, 2), text(size: 0.8em)[`C = 0`: positive edge #h(1em) `C = 1`: negated (complement) edge])
  }),
  caption: [Type-safe wrappers prevent accidentally mixing indices. The `Ref` type packs node ID and complement flag into 32 bits.],
)

```rust
pub struct NodeId(u32);   // Index into nodes array
pub struct Var(u32);      // Variable identifier (1-indexed)
pub struct Level(u32);    // Position in variable ordering
pub struct Ref(u32);      // Handle: (id << 1) | negated
```

These types are all `u32` internally, but the type system prevents accidental confusion:

```rust
fn process(v: Var, l: Level) { ... }

let var = Var::new(1);
let level = Level::new(0);

process(var, level);     // ✓ Compiles
// process(level, var);  // ✗ Type error!
```

#definition(title: "NodeId")[
  An index into the `nodes: Vec<Node>` array.
  Valid range is $[0, "nodes.len")$.
  Index 0 is the terminal node.
]

#definition(title: "Var")[
  A semantic variable identifier.
  Variables are *1-indexed* by convention --- `Var(0)` is reserved for terminals.
  This aligns with DIMACS format used in SAT solvers.
]

#definition(title: "Level")[
  Position in the current variable ordering.
  Level 0 is the root (top) of the BDD.
  Lower levels are closer to terminals.
]

#definition(title: "Ref")[
  A user-facing handle combining `NodeId` and a complement bit.
  The 31 high bits store the node index; the low bit stores negation.
]

#implementation-note[
  In `bdd-rs`, variables are 1-indexed by convention.
  Variable 0 is reserved for internal use (marking terminals).
  This aligns with DIMACS format used in SAT solvers.
]

== Variables vs. Levels

A common source of confusion is the distinction between *variables* and *levels*:

#comparison-table(
  [*Concept*],
  [*Meaning*],
  [*Example*],
  [Variable],
  [Semantic identity ($x_1, x_2, ...$)],
  [`Var(1)` = "input A"],
  [Level],
  [Position in current ordering],
  [`Level(0)` = root position],
)

Why does this distinction matter?
Because *variable reordering* can change which variable is at which level.

#example-box(title: "Variable vs. Level")[
  With ordering $x_2 < x_1 < x_3$:
  - $x_2$ is at level 0
  - $x_1$ is at level 1
  - $x_3$ is at level 2

  The variable $x_1$ always represents the same Boolean input, but its position in the BDD changes with the ordering.
]

The manager maintains bidirectional mappings:

```rust
// In Bdd struct:
var_order: RefCell<Vec<Var>>,            // level → variable
level_map: RefCell<HashMap<Var, Level>>, // variable → level

// Usage:
fn var_at_level(&self, level: Level) -> Var {
    self.var_order()[level.index()]
}

fn level_of_var(&self, var: Var) -> Level {
    self.level_map()[&var]
}
```

This separation is crucial for dynamic reordering --- we can swap positions without changing variable semantics.

== The Ref Type in Detail

`Ref` is the most important type for users.
It's a 32-bit value that encodes both *which node* and *whether it's negated*:

```rust
#[repr(transparent)]
pub struct Ref(u32);

impl Ref {
    // Bit layout: [31-bit node index][1-bit complement]

    pub fn new(id: NodeId, negated: bool) -> Self {
        Self((id.raw() << 1) | (negated as u32))
    }

    pub fn id(self) -> NodeId {
        NodeId::from_raw(self.0 >> 1)
    }

    pub fn is_negated(self) -> bool {
        (self.0 & 1) != 0
    }
}
```

#insight-box[
  The complement bit enables $O(1)$ negation.
  Instead of building a new BDD for $not f$, we just flip the low bit of the `Ref`.
  This is why BDD libraries with complement edges outperform those without for negation-heavy operations.
]

=== Ref Operations

```rust
// Negation: flip the complement bit
impl Neg for Ref {
    fn neg(self) -> Self {
        Self(self.0 ^ 1)
    }
}

// Comparison: direct integer compare
impl PartialEq for Ref {
    fn eq(&self, other: &Self) -> bool {
        self.0 == other.0
    }
}

// Hashing: use raw value
impl Hash for Ref {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.0.hash(state);
    }
}
```

The raw `u32` comparison for equality is *exactly* why BDD equivalence is $O(1)$.
Two `Ref` values are equal if and only if they represent the same Boolean function.

== Memory and Cache Considerations

=== Contiguous Storage

Nodes are stored in a simple `Vec<Node>`:

```rust
nodes: RefCell<Vec<Node>>
```

This provides:
- *O(1) access*: Index directly into array
- *Cache locality*: Sequential nodes are adjacent in memory
- *Simple growth*: `Vec` handles reallocation automatically

=== Cache-Friendly Traversal

BDD algorithms typically traverse nodes in a pattern that respects variable ordering:
+ Start at root (highest level)
+ Recursively process children (lower levels)
+ Combine results bottom-up

Because nodes at the same level are often created together, they tend to be adjacent in the array.
This improves CPU cache hit rates during traversal.

=== Size Analysis

With the current 24-byte node structure:

- 1M nodes $approx$ 24 MB
- 16M nodes $approx$ 384 MB
- 256M nodes $approx$ 6 GB

The cache size (for memoization) is typically smaller --- `bdd-rs` defaults to $2^16$ cache entries regardless of node capacity.

#performance-note[
  For large problems, the bottleneck is usually cache misses during graph traversal, not raw memory bandwidth.
  Keep your working set small by avoiding unnecessary intermediate results.
]

== Putting It Together

Here's how the types interact during a simple operation:

```rust
let bdd = Bdd::default();
let x = bdd.mk_var(1);  // Returns Ref

// mk_var internally:
// 1. Creates Var(1)
// 2. Registers var at next available Level
// 3. Creates Node { variable: Var(1), low: zero, high: one, ... }
// 4. Stores node at some NodeId
// 5. Returns Ref::positive(node_id)

let not_x = -x;  // Just flips the complement bit

// is_one check:
// 1. Compare x.raw() with one.raw()
// 2. Direct u32 comparison --- O(1)
```

The layered type system --- `Node`, `NodeId`, `Var`, `Level`, `Ref` --- may seem complex, but each type serves a specific purpose and prevents a class of bugs.
