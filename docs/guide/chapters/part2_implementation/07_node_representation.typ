#import "../../theme.typ": *

= Node Representation <ch-node-representation>

How BDD nodes are represented in memory directly impacts performance.
This chapter explores the node structure in `bdd-rs`, the type-safe wrappers that prevent bugs, and the memory layout considerations that affect cache efficiency.

== The Node Structure

Each BDD node represents a Shannon decomposition:

$ f = (not v and f_"low") or (v and f_"high") $

The `Node` struct captures this with four fields:

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

#info-box(title: "Why Store the Hash?")[
  Computing `hash(variable, low, high)` requires three multiplications and XORs.
  By precomputing and storing it in the node, we avoid recalculating during hash table operations.
  This trades 8 bytes of memory per node for faster lookups.
]

The `next` field implements *intrusive hashing* --- nodes themselves form the collision chains for the hash table, rather than using a separate wrapper struct.
This CUDD-inspired design eliminates allocation overhead and improves cache locality.

=== Memory Layout

```
+──────────+─────+──────+──────+──────+
│ variable │ low │ high │ next │ hash │
+──────────+─────+──────+──────+──────+
    4B       4B    4B     4B     8B    = 24 bytes total
```

In comparison, a minimal node without the hash or collision chain would be 12 bytes.
The extra space is a worthwhile trade for better hash table performance.

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

process(var, level);  // ✓ Compiles
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
  [*Concept*], [*Meaning*], [*Example*],
  [Variable], [Semantic identity ($x_1, x_2, ...$)], [`Var(1)` = "input A"],
  [Level], [Position in current ordering], [`Level(0)` = root position],
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
