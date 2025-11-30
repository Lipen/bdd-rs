#import "../../theme.typ": *

= The Unique Table <ch-unique-table>

What stops a BDD from creating the same node twice?
The answer is the *unique table* --- a hash-based lookup structure ensuring that every $(v, "low", "high")$ triple maps to exactly one node.

This is the mechanism behind canonicity.
Without it, two separately constructed BDDs might represent the same function but have different structures.
The $O(1)$ equivalence check --- the killer feature of BDDs --- would break entirely.

This chapter explains how the unique table works and why `bdd-rs` uses per-level subtables for efficiency.

== The Problem: Duplicate Nodes

Imagine building the BDD for $f = (x and y) or (x and z)$.
The variable $x$ appears twice in the formula.
Without care, we might create two separate $x$-nodes:

#figure(
  cetz.canvas(length: 1cm, {
    import cetz.draw: *

    // Problem visualization: two separate x nodes
    content((2, 4.5), text(weight: "bold", fill: colors.error)[Problem: Duplicate nodes])

    // First x node
    bdd-decision-node((1.5, 3), $x$, name: "x1")
    content((1.5, 2), text(size: 0.7em, fill: colors.text-muted)[to $y$ branch])

    // Second x node
    bdd-decision-node((4, 3), $x$, name: "x2")
    content((4, 2), text(size: 0.7em, fill: colors.text-muted)[to $z$ branch])

    // Not equal sign
    content((2.75, 3), text(size: 1em, fill: colors.error)[$eq.not$])

    // Arrow to solution
    line((5.5, 3), (7, 3), stroke: 2pt + colors.success, mark: (end: ">", fill: colors.success))

    // Solution: single node
    content((9, 4.5), text(weight: "bold", fill: colors.success)[Solution: Hash consing])
    bdd-decision-node((9, 3), $x$, name: "x-shared")
    content((9, 2), text(size: 0.7em, fill: colors.text-muted)[shared by both])

    // Both point to it
    line((7.5, 4), (8.6, 3.4), stroke: 1pt + colors.text-muted, mark: (end: ">"))
    line((10.5, 4), (9.4, 3.4), stroke: 1pt + colors.text-muted, mark: (end: ">"))
  }),
  caption: [Without hash consing (left), duplicate nodes destroy canonicity. With it (right), identical structures are shared.],
)

Hash consing prevents this.
Before creating any node, we check: "Does this node already exist?"
If yes, return the existing one.
If no, create and register it.

== The Unique Table

The unique table maintains the invariant:

$ forall ("var", "low", "high"): "at most one node exists" $

It's a hash map from triples to node IDs:

$ U : ("Var" times "Ref" times "Ref") -> "NodeId" $

#definition(title: "Hash Consing")[
  *Hash consing* is a technique where:
  + Before creating a structure, check if an identical one exists
  + If it exists, return a reference to the existing one
  + If not, create it and add it to the table

  This ensures structural sharing: identical structures are represented exactly once.
]

== The `mk` Operation

The `mk` (make) function is the gatekeeper.
Every node creation goes through it, and it enforces all BDD invariants:

#figure(
  cetz.canvas(length: 1cm, {
    import cetz.draw: *

    // Flow diagram for mk
    let start = (5, 7)

    // Input
    rect((2.5, 6.6), (7.5, 7.4), fill: colors.box-definition, stroke: 1pt + colors.primary, radius: 4pt)
    content(start, text(size: 0.8em)[`mk(var, low, high)`])

    // Step 1: Canonicity
    rect((1.5, 5.3), (8.5, 6.1), fill: colors.box-warning.lighten(40%), stroke: 1pt + colors.warning, radius: 4pt)
    content((5, 5.7), text(size: 0.8em)[High negated? Flip: `return -mk(var, -low, -high)`])

    // Step 2: Reduction
    rect((1.5, 4), (8.5, 4.8), fill: colors.box-example.lighten(40%), stroke: 1pt + colors.success, radius: 4pt)
    content((5, 4.4), text(size: 0.8em)[`low == high`? Redundant: `return low`])

    // Step 3: Lookup
    rect((1.5, 2.7), (8.5, 3.5), fill: colors.box-insight.lighten(30%), stroke: 1pt + colors.info, radius: 4pt)
    content((5, 3.1), text(size: 0.8em)[Exists in unique table? `return existing`])

    // Step 4: Create
    rect((1.5, 1.4), (8.5, 2.2), fill: colors.box-theorem.lighten(30%), stroke: 1pt + colors.primary, radius: 4pt)
    content((5, 1.8), text(size: 0.8em)[Create new node, insert into table, return])

    // Arrows
    line((5, 6.6), (5, 6.1), stroke: 1pt + colors.text-muted, mark: (end: ">"))
    line((5, 5.3), (5, 4.8), stroke: 1pt + colors.text-muted, mark: (end: ">"))
    line((5, 4), (5, 3.5), stroke: 1pt + colors.text-muted, mark: (end: ">"))
    line((5, 2.7), (5, 2.2), stroke: 1pt + colors.text-muted, mark: (end: ">"))

    // Side labels
    content((9.5, 5.7), text(size: 0.7em, fill: colors.warning)[Invariant 1], anchor: "west")
    content((9.5, 4.4), text(size: 0.7em, fill: colors.success)[Invariant 2], anchor: "west")
    content((9.5, 3.1), text(size: 0.7em, fill: colors.info)[Invariant 3], anchor: "west")
  }),
  caption: [The `mk` function enforces three invariants in sequence.],
)

#algorithm(title: "mk (Make Node)")[
  ```
  mk(var, low, high):
    // Invariant 1: Canonicity (high edge positive)
    if high.is_negated():
      return -mk(var, -low, -high)

    // Invariant 2: Reduction (no redundant tests)
    if low == high:
      return low

    // Invariant 3: Uniqueness (hash consing)
    level = get_level(var)
    if (low, high) in subtables[level]:
      return subtables[level].find(low, high)

    // Create and register new node
    node = Node::new(var, low, high)
    id = allocate_node(node)
    subtables[level].insert(low, high, id)
    return Ref::positive(id)
  ```
]

== Per-Level Subtables

`bdd-rs` doesn't use a single global hash table.
Instead, it uses *per-level subtables* --- one hash table per variable:

#figure(
  cetz.canvas(length: 1cm, {
    import cetz.draw: *

    // Subtables visualization
    content((5, 6), text(weight: "bold", size: 1em)[Per-Level Subtables])

    // Level 0
    rect((0.5, 4.2), (3.5, 5.2), fill: colors.box-definition.lighten(30%), stroke: 1pt + colors.primary, radius: 4pt)
    content((2, 4.9), text(size: 0.8em, weight: "semibold")[Level 0: $x$])
    content((2, 4.5), text(size: 0.7em, fill: colors.text-muted)[nodes with var = x])

    // Level 1
    rect(
      (4, 4.2),
      (7, 5.2),
      fill: colors.box-example.lighten(30%),
      stroke: 1pt + colors.success.lighten(20%),
      radius: 4pt,
    )
    content((5.5, 4.9), text(size: 0.8em, weight: "semibold")[Level 1: $y$])
    content((5.5, 4.5), text(size: 0.7em, fill: colors.text-muted)[nodes with var = y])

    // Level 2
    rect(
      (7.5, 4.2),
      (10.5, 5.2),
      fill: colors.box-warning.lighten(30%),
      stroke: 1pt + colors.warning.lighten(20%),
      radius: 4pt,
    )
    content((9, 4.9), text(size: 0.8em, weight: "semibold")[Level 2: $z$])
    content((9, 4.5), text(size: 0.7em, fill: colors.text-muted)[nodes with var = z])

    // Hash buckets inside each
    for i in range(3) {
      let x = 1 + i * 0.6
      rect((x, 3.2), (x + 0.4, 3.8), fill: colors.bg-code, stroke: 0.5pt + colors.line)
    }
    for i in range(3) {
      let x = 4.5 + i * 0.6
      rect((x, 3.2), (x + 0.4, 3.8), fill: colors.bg-code, stroke: 0.5pt + colors.line)
    }
    for i in range(3) {
      let x = 8 + i * 0.6
      rect((x, 3.2), (x + 0.4, 3.8), fill: colors.bg-code, stroke: 0.5pt + colors.line)
    }

    content((2, 2.8), text(size: 0.7em, fill: colors.text-muted)[buckets])
    content((5.5, 2.8), text(size: 0.7em, fill: colors.text-muted)[buckets])
    content((9, 2.8), text(size: 0.7em, fill: colors.text-muted)[buckets])

    // Explanation
    content((5.5, 2), align(center)[
      #set text(size: 0.8em)
      Query: "Does node $(y, ell, h)$ exist?" $->$ Look only in Level 1's table
    ])
  }),
  caption: [Each level maintains its own hash table. Queries only search the relevant level.],
)

```rust
subtables: RefCell<Vec<Subtable>>  // level → subtable

pub struct Subtable {
    pub variable: Var,
    buckets: Vec<NodeId>,  // Hash bucket heads
    bitmask: u64,          // For fast modulo
    count: usize,          // Node count at this level
}
```

=== Why Per-Level?

#info-box(title: "Advantages of Per-Level Subtables")[
  + *Smaller tables*: Each level has fewer nodes than the total, reducing collision rates
  + *Better locality*: Operations often work within one or two levels
  + *Simpler reordering*: Swapping variable positions means swapping subtables
  + *Parallelism-friendly*: Different levels can be processed independently
]

The key insight: when creating a node for variable $v$, we *know* which subtable to search.
We don't need to include $v$ in the hash --- it's implicit from which table we're querying.

```rust
fn bucket_index(&self, low: Ref, high: Ref) -> usize {
    let hash = hash_children(low, high);
    (hash & self.bitmask) as usize
}
```

== The Unique Table vs. Computed Table

Two hash-based structures exist in a BDD library.
Don't confuse them:

#comparison-table(
  [*Aspect*],
  [*Unique Table*],
  [*Computed Table (Cache)*],
  [Purpose],
  [Node deduplication],
  [Operation memoization],
  [Key],
  [$("low", "high")$ at level],
  [$("op", f, g, h)$],
  [Value],
  [NodeId],
  [Ref (result)],
  [On collision],
  [Chain (must be complete)],
  [Evict (optimization only)],
  [Correctness],
  [*Required*],
  [Performance only],
)

The unique table must be *complete* --- every node must be findable.
The computed table can *evict* entries on collision; it only affects speed, not correctness.

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
  [*Approach*],
  [*Memory*],
  [*Locality*],
  [*Complexity*],
  [Intrusive (CUDD-style)],
  [No extra allocation],
  [Better --- nodes are data],
  [Harder to implement],
  [External chaining],
  [Entry wrapper per node],
  [Worse --- indirection],
  [Easier],
  [Open addressing],
  [No chains],
  [Excellent],
  [Resizing tricky],
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
  [*Library*],
  [*Table Structure*],
  [*Hash Strategy*],
  [CUDD],
  [Per-level subtables],
  [Intrusive chaining],
  [BuDDy],
  [Global table],
  [External chaining],
  [Sylvan],
  [Lock-free global table],
  [Open addressing],
  [bdd-rs],
  [Per-level subtables],
  [Intrusive chaining],
)

The per-level approach scales better for dynamic reordering, while global tables are simpler to implement.
Lock-free designs like Sylvan's enable parallelism but add significant complexity.

#insight-box[
  The unique table is where BDD libraries spend most of their implementation effort.
  A well-tuned hash table directly impacts the speed of every BDD operation.
]
