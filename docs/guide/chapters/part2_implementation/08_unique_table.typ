#import "../../theme.typ": *

= The Unique Table <ch-unique-table>

The *unique table* is the mechanism that ensures no two BDD nodes represent the same function.
It implements *hash consing* --- the technique of sharing identical structures by looking them up in a hash table before creating new ones.
Without the unique table, BDDs would lose their canonical form property.

== Purpose of the Unique Table

Recall the BDD uniqueness invariant: for any $("var", "low", "high")$ triple, at most one node exists in the entire graph.
The unique table enforces this by maintaining a mapping:

$ ("var", "low", "high") -> "NodeId" $

Before creating any node, we query this table.
If an entry exists, we return the existing node.
If not, we create a new node and insert it.

This is *hash consing*, a general technique for structural sharing in functional data structures.
The term comes from Lisp's `cons` cells --- by hashing them, we avoid duplicates.

#insight-box[
  Hash consing is what transforms BDDs from exponential-sized trees into polynomial-sized DAGs.
  Every time you'd have duplicate subtrees, hash consing makes them share a single representation.
]

== The mk Operation

The `mk` (make) function is the constructor that enforces all BDD invariants:

#algorithm(title: "mk (Make Node)")[
  ```
  mk(var, low, high):
    // Invariant 1: High edge never complemented
    if high.is_negated():
      return -mk(var, -low, -high)

    // Invariant 2: No redundant tests
    if low == high:
      return low

    // Invariant 3: Hash consing (uniqueness)
    level = get_level(var)
    if (low, high) in subtables[level]:
      return subtables[level].find(low, high)

    // Create new node
    node = Node::new(var, low, high)
    id = allocate_node(node)
    subtables[level].insert(low, high, id)
    return Ref::positive(id)
  ```
]

The three invariants are checked in order:

#definition(title: "Canonicity Invariant")[
  High edges are never complemented.
  If `high.is_negated()`, we flip both children and return a negated reference.
  This ensures a unique representation for each function.
]

#definition(title: "Reduction Invariant")[
  If `low == high`, the variable test is redundant --- the function doesn't depend on this variable.
  We return the child directly, avoiding a useless node.
]

#definition(title: "Uniqueness Invariant")[
  Before allocating a new node, check if an identical one exists.
  The unique table provides $O(1)$ average-case lookup for this check.
]

=== The mk Implementation in bdd-rs

```rust
pub fn mk_node(&self, v: Var, low: Ref, high: Ref) -> Ref {
    assert!(!v.is_terminal(), "Variable must not be Var::ZERO");

    // Handle canonicity: high edge must be positive
    if high.is_negated() {
        return -self.mk_node(v, -low, -high);
    }

    // Handle reduction: skip redundant tests
    if low == high {
        return low;
    }

    // Auto-register the variable if needed
    self.register_variable(v.id());
    let level = self.get_level(v).expect("Variable should be registered");

    // Hash consing: check if node exists
    {
        let nodes = self.nodes();
        let subtables = self.subtables();
        if let Some(id) = subtables[level.index()].find(low, high, &nodes) {
            return Ref::positive(id);
        }
    }

    // Node doesn't exist - allocate and insert
    let node = Node::new(v, low, high);
    let id = self.allocate_node(node);

    {
        let mut nodes = self.nodes_mut();
        self.subtables_mut()[level.index()].insert(low, high, id, &mut nodes);
    }

    Ref::positive(id)
}
```

== Hash Table Design

`bdd-rs` uses *per-level subtables* rather than a single global hash table.
Each level (variable) has its own hash table containing only nodes with that variable.

=== Per-Level Subtables

```rust
subtables: RefCell<Vec<Subtable>>  // level → subtable

// Each subtable handles one variable
pub struct Subtable {
    pub variable: Var,
    buckets: Vec<NodeId>,  // Hash buckets (head pointers)
    bitmask: u64,          // For computing bucket index
    count: usize,          // Number of nodes
}
```

The key insight: since we know the variable when querying, we can skip it in the hash.
The subtable only hashes `(low, high)`:

```rust
fn bucket_index(&self, low: Ref, high: Ref) -> usize {
    let hash = hash_children(low, high);
    (hash & self.bitmask) as usize
}
```

#info-box(title: "Why Per-Level Subtables?")[
  + *Smaller hash tables*: Each level has fewer nodes than the total
  + *Better locality*: Nodes at the same level are often accessed together
  + *Simpler reordering*: Swapping levels means swapping subtables
  + *Parallelism potential*: Different levels can be processed independently
]

=== Intrusive Hashing

Following CUDD's design, `bdd-rs` uses *intrusive hashing* --- collision chains are stored in the nodes themselves via the `next` field:

```rust
pub struct Node {
    pub variable: Var,
    pub low: Ref,
    pub high: Ref,
    pub next: NodeId,  // Next in collision chain
    hash: u64,
}
```

The `buckets` array stores head pointers.
Following `next` fields traverses the collision chain:

```
Subtable for level k:
┌─────────────────────────────────────────────────┐
│ buckets: [NodeId; 2^bits]                       │
│   [0] ───► Node@5 ──► Node@12 ──► ∅             │
│   [1] ───► ∅                                    │
│   [2] ───► Node@3 ──► ∅                         │
│   ...                                           │
└─────────────────────────────────────────────────┘
```

#comparison-table(
  [*Approach*], [*Memory*], [*Locality*], [*Complexity*],
  [Intrusive (CUDD-style)], [No extra allocation], [Better --- nodes are data], [Harder to implement],
  [External chaining], [Entry wrapper per node], [Worse --- indirection], [Easier],
  [Open addressing], [No chains], [Excellent], [Resizing tricky],
)

=== Lookup Operation

Finding a node with given children:

```rust
impl Subtable {
    pub fn find(&self, low: Ref, high: Ref, nodes: &[Node]) -> Option<NodeId> {
        let idx = self.bucket_index(low, high);
        let mut current = self.buckets[idx];

        // Walk collision chain
        while current != Node::NO_NEXT {
            let node = &nodes[current.index()];
            if node.low == low && node.high == high {
                return Some(current);
            }
            current = node.next;
        }
        None
    }
}
```

Average case is $O(1)$ assuming a good hash function and reasonable load factor.
Worst case is $O(n)$ if all nodes hash to the same bucket.

=== Insert Operation

Adding a new node to the subtable:

```rust
impl Subtable {
    pub fn insert(&mut self, low: Ref, high: Ref, id: NodeId, nodes: &mut [Node]) {
        let idx = self.bucket_index(low, high);

        // Prepend to collision chain
        nodes[id.index()].next = self.buckets[idx];
        self.buckets[idx] = id;

        self.count += 1;
    }
}
```

Insertion is $O(1)$ --- we prepend to the chain head.
No need to check for duplicates; we assume `find` was called first.

== Hash Function Design

A good hash function for $("low", "high")$ pairs should:
+ *Distribute evenly*: Minimize collisions
+ *Be fast*: Called frequently during BDD construction
+ *Handle similar inputs*: Nearby Ref values shouldn't cluster

```rust
fn hash_children(low: Ref, high: Ref) -> u64 {
    let x = low.raw() as u64;
    let y = high.raw() as u64;
    // Mix using multiplication and XOR
    x.wrapping_mul(PRIME1) ^ y.wrapping_mul(PRIME2)
}
```

The node's hash is precomputed during creation:

```rust
impl Node {
    pub fn new(variable: Var, low: Ref, high: Ref) -> Self {
        let hash = {
            let x = variable.id() as u64;
            let y = hash(&low);
            let z = hash(&high);
            hash(&(y, z, x))
        };
        Self { variable, low, high, next: Self::NO_NEXT, hash }
    }
}
```

== Load Factor and Resizing

The *load factor* is the ratio of nodes to buckets:

$ "load factor" = "count" / "num_buckets" $

High load factors mean longer collision chains and slower lookups.
`bdd-rs` initializes subtables with $2^16$ buckets by default:

```rust
const DEFAULT_BUCKET_BITS: usize = 16;  // 65536 buckets

impl Subtable {
    pub fn new(variable: Var) -> Self {
        Self::with_bucket_bits(variable, DEFAULT_BUCKET_BITS)
    }
}
```

For most applications, this is sufficient.
Dynamic resizing (rehashing) adds complexity and is not currently implemented in `bdd-rs`.

#warning-box(title: "Load Factor Implications")[
  If a single level grows to millions of nodes with only 65536 buckets, the average chain length becomes $approx 15$ nodes.
  For pathological cases, consider initializing with larger subtables.
]

== Maintaining Invariants

The unique table and node storage must stay synchronized:

#theorem(title: "Unique Table Invariants")[
  At all times:
  + Every node in storage (except free slots) is in exactly one subtable
  + Every entry in a subtable points to a valid node with matching children
  + No two nodes have the same $("var", "low", "high")$ triple
]

Violations indicate bugs in the implementation.
Debugging techniques include:

```rust
// Verify all nodes are reachable from subtables
fn validate_unique_table(&self) {
    let mut seen = HashSet::new();
    for subtable in self.subtables().iter() {
        for id in subtable.all_nodes(&self.nodes()) {
            assert!(!seen.contains(&id), "Duplicate entry");
            seen.insert(id);
        }
    }
    // Check free_set nodes are not in subtables
    for &id in self.free_set().iter() {
        assert!(!seen.contains(&id), "Free node in table");
    }
}
```

== Alternative Designs

Other BDD libraries make different choices:

#comparison-table(
  [*Library*], [*Table Structure*], [*Hash Strategy*],
  [CUDD], [Per-level subtables], [Intrusive chaining],
  [BuDDy], [Global table], [External chaining],
  [Sylvan], [Lock-free global table], [Open addressing],
  [bdd-rs], [Per-level subtables], [Intrusive chaining],
)

The per-level approach scales better for dynamic reordering, while global tables are simpler to implement.
Lock-free designs like Sylvan's enable parallelism but add significant complexity.

#insight-box[
  The unique table is where BDD libraries spend most of their implementation effort.
  A well-tuned hash table directly impacts the speed of every BDD operation.
]
