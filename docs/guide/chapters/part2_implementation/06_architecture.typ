#import "../../theme.typ": *

= Manager-Centric Architecture <ch-architecture>

The design of a BDD library revolves around a fundamental architectural choice: how to organize the relationship between BDD nodes and the infrastructure that manages them.
This chapter explains why `bdd-rs` and most serious BDD libraries adopt a *manager-centric architecture*, where a central `Bdd` struct owns all state and controls all operations.

== Why a Manager?

Consider the alternative: standalone BDD objects that each own their own data.
At first glance, this seems natural --- after all, a BDD represents a Boolean function, so why not have independent `Bdd` objects?

The problem is *canonicity*.
BDDs achieve $O(1)$ equivalence testing because identical functions share identical representations.
This requires:

+ *Shared node storage*: All nodes must live in the same pool for comparison to work
+ *Consistent variable ordering*: All BDDs must use the same ordering
+ *Hash consing*: Creating a node must check if an identical one exists
+ *Shared caches*: Operation results must be reusable across all BDDs

With standalone objects, none of these guarantees hold.
Two independently created BDDs representing the same function would be different objects, breaking the fundamental $O(1)$ equivalence property.

#insight-box[
  The manager-centric design is not just an implementation choice --- it's essential for maintaining the canonical form invariant.
  Without centralized control, hash consing becomes impossible and canonicity breaks.
]

The manager pattern appears throughout the BDD ecosystem:
- *CUDD*: `DdManager` owns all nodes and operation caches
- *BuDDy*: `bdd_init()` creates global state for all operations
- *Sylvan*: Parallel manager with work-stealing queues
- *bdd-rs*: `Bdd` struct with interior mutability

== The Bdd Manager in bdd-rs

The `Bdd` struct is the heart of `bdd-rs`.
It encapsulates all state needed for BDD operations:

```rust
pub struct Bdd {
    // Node storage: index 0 = terminal
    nodes: RefCell<Vec<Node>>,
    free_set: RefCell<HashSet<NodeId>>,

    // Per-level subtables for hash consing
    subtables: RefCell<Vec<Subtable>>,

    // Operation cache (memoization)
    cache: RefCell<Cache<OpKey, Ref>>,
    size_cache: RefCell<Cache<Ref, u64>>,

    // Terminal references
    pub one: Ref,
    pub zero: Ref,

    // Variable ordering
    var_order: RefCell<Vec<Var>>,      // level → variable
    level_map: RefCell<HashMap<Var, Level>>,  // variable → level
    next_var_id: Cell<u32>,
}
```

#info-box(title: "Interior Mutability")[
  The `RefCell` wrappers enable *interior mutability* --- modification through shared references.
  This allows the ergonomic API pattern where methods take `&self` rather than `&mut self`, so users don't need exclusive access for every operation.
]

=== Component Responsibilities

Each component has a specific role:

#definition(title: "Node Storage")[
  `nodes: Vec<Node>` stores all BDD nodes contiguously in memory.
  Index 0 is reserved for the terminal node.
  The `free_set` tracks recycled indices available for reuse.
]

#definition(title: "Per-Level Subtables")[
  `subtables: Vec<Subtable>` provides hash-based lookup for each variable level.
  This enables $O(1)$ average-case node lookup during construction.
]

#definition(title: "Operation Cache")[
  `cache: Cache<OpKey, Ref>` memoizes ITE operation results.
  Without caching, BDD operations would have exponential complexity.
]

#definition(title: "Variable Ordering")[
  `var_order` and `level_map` maintain the bidirectional mapping between variables and their positions in the ordering.
]

=== Creating a Manager

```rust
use bdd_rs::bdd::Bdd;

// Default: 2^20 (~1M) nodes capacity
let bdd = Bdd::default();

// Custom capacity for large problems
let big_bdd = Bdd::new(24);  // 2^24 (~16M) nodes
```

The capacity parameter specifies bits, so `Bdd::new(20)` allocates space for $2^20 approx 1$ million nodes.
The cache is automatically sized based on storage capacity.

== References vs. Nodes

Users never interact directly with `Node` structs.
Instead, they work with `Ref` --- a lightweight 32-bit handle:

```rust
#[repr(transparent)]
pub struct Ref(u32);
```

The `Ref` type packs two pieces of information:
- *31 bits*: Index into the node storage
- *1 bit*: Complement flag (is this reference negated?)

This design has several advantages:

#comparison-table(
  [*Aspect*], [*Ref*], [*Node*],
  [Size], [4 bytes], [16 bytes],
  [Copy], [Trivial], [Trivial but larger],
  [Negation], [$O(1)$ bit flip], [Would need new node],
  [Comparison], [Direct integer compare], [Field-by-field],
  [Ownership], [Handle --- doesn't own data], [Data --- would need manager],
)

#info-box(title: "Why Complement Edges Matter")[
  The complement bit in `Ref` enables $O(1)$ negation.
  Instead of creating a new BDD for $not f$, we simply flip the bit: `-f` in Rust.
  This is why `Ref` implements `Neg`, making negation as simple as writing `-x`.
]

=== The Ref API

```rust
impl Ref {
    pub fn new(id: NodeId, negated: bool) -> Self;
    pub fn positive(id: NodeId) -> Self;
    pub fn negative(id: NodeId) -> Self;

    pub fn id(self) -> NodeId;        // Extract node index
    pub fn is_negated(self) -> bool;  // Check complement bit
}

// Negation is just XOR with 1
impl Neg for Ref {
    fn neg(self) -> Self {
        Self(self.0 ^ 1)
    }
}
```

== Lifetime and Ownership

A `Ref` is only meaningful in the context of its manager.
Using a `Ref` from manager A with manager B leads to undefined behavior --- the index might point to a completely different node (or no node at all).

Rust's type system doesn't prevent this at compile time (both are just `u32` values), so users must maintain this invariant manually.
This is a deliberate trade-off: strict type-level safety would require lifetime annotations throughout, significantly complicating the API.

#warning-box(title: "Cross-Manager Pitfall")[
  Never mix `Ref` values from different managers.
  The compiler won't catch this, but the results will be nonsensical.

  ```rust
  let bdd1 = Bdd::default();
  let bdd2 = Bdd::default();
  let x = bdd1.mk_var(1);
  // WRONG: x is from bdd1, not bdd2
  // let result = bdd2.apply_and(x, bdd2.mk_var(2));
  ```
]

=== Garbage Collection Implications

Unlike CUDD, `bdd-rs` does not perform automatic garbage collection.
Once a node is created, it persists until:
- The manager is dropped
- Manual cleanup is performed (if implemented)

This simplifies the implementation but means large computations may accumulate dead nodes.
For long-running applications, consider periodically recreating the manager or implementing node reclamation.

== The Public API Surface

The manager exposes operations through method calls:

=== Node Construction

```rust
// Create variables
let x = bdd.mk_var(1);
let y = bdd.mk_var(2);

// Low-level node creation (rarely needed)
let node = bdd.mk_node(var, low_child, high_child);
```

=== Boolean Operations

```rust
// Binary operations via apply
let f_and_g = bdd.apply_and(f, g);
let f_or_g = bdd.apply_or(f, g);
let f_xor_g = bdd.apply_xor(f, g);
let f_implies_g = bdd.apply_implies(f, g);

// The universal ITE operation
let result = bdd.apply_ite(f, g, h);  // f ? g : h

// Negation is just operator overloading
let not_f = -f;
```

=== Queries

```rust
// Terminal checks
bdd.is_zero(f)  // Is f ≡ ⊥?
bdd.is_one(f)   // Is f ≡ ⊤?

// Size queries
bdd.size(f)     // Number of nodes in BDD
bdd.sat_count(f, num_vars)  // Number of satisfying assignments
```

=== Quantification

```rust
use bdd_rs::types::Var;

// Existential: ∃x. f
let ex = bdd.exists(f, [Var::new(1)]);

// Universal: ∀x. f
let fa = bdd.forall(f, [Var::new(1)]);
```

== Architecture Diagram

The following diagram illustrates how the components interact:

#align(center)[
```
                         Bdd Manager
 ┌──────────────────────────────────────────────────────────┐
 │                                                          │
 │   nodes: Vec<Node>           subtables: Vec<Subtable>    │
 │   ┌────────────────┐         ┌───────────────────────┐   │
 │   │ [0] terminal   │         │ Level 0: buckets[...] │   │
 │   │ [1] node       │ ◄─────► │ Level 1: buckets[...] │   │
 │   │ [2] node       │         │ Level 2: buckets[...] │   │
 │   │ ...            │         │ ...                   │   │
 │   └────────────────┘         └───────────────────────┘   │
 │                                                          │
 │   cache: Cache               var_order: Vec<Var>         │
 │   ┌────────────────┐         ┌───────────────────────┐   │
 │   │ ITE results    │         │ level → variable      │   │
 │   │ memoized       │         │ variable → level      │   │
 │   └────────────────┘         └───────────────────────┘   │
 │                                                          │
 └──────────────────────────────────────────────────────────┘
                              │
                              ▼
              Ref: 32-bit handle (index + complement)
```
]

#info-box(title: "Why This Architecture Works")[
  The manager-centric design enables all the BDD guarantees:
  - *Canonicity*: Hash consing through subtables ensures uniqueness
  - *Efficiency*: Shared caches avoid redundant computation
  - *Consistency*: Single ordering for all BDDs
  - *Simplicity*: Users just work with `Ref` values
]

The next chapters dive into each component: node representation, the unique table, and the apply algorithm implementation.
