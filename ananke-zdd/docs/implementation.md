# Implementation Details

## Architecture Overview

```
┌─────────────────────────────────────────┐
│       ZddManager (public API)           │
│ union, intersection, join, subset1, ... │
└──────────┬──────────────────────────────┘
           │
     ┌─────┴─────────┬──────────────┐
     │               │              │
┌────▼───┐    ┌──────▼─────┐   ┌────▼─────┐
│ Nodes  │    │  Subtables │   │  Caches  │
│ (Vec)  │    │ (Per-Level)│   │(Memoized)│
└────────┘    └────────────┘   └──────────┘
```

The architecture centers around the **manager**, which owns:

1. **Node storage** (`Vec<ZddNode>`)
2. **Unique tables** (one Subtable per variable level)
3. **Operation caches** (memoization for all operations)

---

## Core Data Structures

### ZddId (Node Reference)

```rust
pub struct ZddId(u32);
```

A lightweight 32-bit reference to a node. Two special values:

- `ZddId::ZERO` = 0 (terminal ⊥)
- `ZddId::ONE` = 1 (terminal ⊤)

**Why u32?**: Limits ZDDs to ~2 billion nodes. In practice, problems rarely exceed millions, so u32 is sufficient and halves memory vs u64.

---

### ZddNode (Actual Node Data)

```rust
pub struct ZddNode {
    pub var: Var,
    pub lo: ZddId,   // Sets without this variable
    pub hi: ZddId,   // Sets with this variable
    pub next: ZddId, // Intrusive hash chain
}
```

**Precomputed hash**: Node includes a cached hash for subtable lookup.

**Invariant**: If `hi == ZddId::ZERO`, this node violates the zero-suppression rule and should never exist. The `get_node` constructor enforces this.

---

### Subtable (Per-Level Unique Table)

```rust
pub struct Subtable {
    var: Var,
    buckets: Vec<ZddId>,  // Hash bucket heads
    load_factor: f64,     // For resizing
}
```

**Design**: Intrusive hash chaining at each variable level.

**Why per-level?**

- All Var1 nodes have the same variable, so they're grouped together
- Lookup within a level is $O(1)$ average case
- Cache locality: related nodes stored together

**Collision resolution**: Intrusive chaining (next pointer stored in the node itself).

**Resizing**: When load factor exceeds threshold, rebuild all chains.

---

### Operation Cache

```rust
pub struct Cache {
    table: HashMap<CacheKey, ZddId>,
}

pub struct CacheKey {
    op: OpType,
    f: ZddId,
    g: ZddId,
    commutative: bool,
}
```

**Why memoization?**

- Operations like `union(f, g)` recurse deeply
- Many subtrees are identical across calls
- Memoization cuts exponential search to polynomial

**Commutative operations**: For symmetric operations (union, intersection, join), we store both orders under the same key:

- `union(f, g)` and `union(g, f)` share the same cache entry
- Reduces cache size by ~50% for these operations

---

### Counting Cache

```rust
pub struct CountCache {
    table: HashMap<ZddId, u64>,
}
```

Separate cache for `count()` operation. Set cardinality is independent of operation details, so it deserves its own cache.

---

## Key Algorithms

### Hash Consing (Node Creation)

```rust
fn get_node(&self, var: Var, lo: ZddId, hi: ZddId) -> ZddId {
    // Zero-suppression rule
    if hi == ZddId::ZERO {
        return lo;
    }

    // Check unique table
    if let Some(existing) = subtables[level].find(lo, hi) {
        return existing;  // Reuse existing node
    }

    // Create new node
    let id = NodeId::new(nodes.len());
    nodes.push(ZddNode::new(var, lo, hi));
    subtables[level].insert(lo, hi, id);

    return id;
}
```

**Critical invariant**: No two nodes with the same (var, lo, hi) tuple exist. This ensures canonicity.

---

### Join Operation (The Complex One)

```rust
fn join(&self, f: ZddId, g: ZddId) -> ZddId {
    if f.is_zero() || g.is_zero() { return ZddId::ZERO; }
    if f.is_one() { return g; }
    if g.is_one() { return f; }

    let key = CacheKey::commutative(OpType::Join, f, g);
    if let Some(result) = self.cache.get(&key) {
        return result;
    }

    let f_node = self.node(f);
    let g_node = self.node(g);
    let f_level = self.level(f_node.var);
    let g_level = self.level(g_node.var);

    let result = match f_level.cmp(&g_level) {
        Less => {  // f's variable is earlier
            let lo = self.join(f_node.lo, g);
            let hi = self.join(f_node.hi, g);
            self.get_node(f_node.var, lo, hi)
        }
        Greater => {  // g's variable is earlier
            let lo = self.join(f, g_node.lo);
            let hi = self.join(f, g_node.hi);
            self.get_node(g_node.var, lo, hi)
        }
        Equal => {  // Same variable
            let lo_lo = self.join(f_node.lo, g_node.lo);
            let hi_lo = self.join(f_node.hi, g_node.lo);
            let lo_hi = self.join(f_node.lo, g_node.hi);
            let hi_hi = self.join(f_node.hi, g_node.hi);

            let lo = lo_lo;  // Neither has var
            let hi = self.union(hi_lo, self.union(lo_hi, hi_hi));  // At least one has var
            self.get_node(f_node.var, lo, hi)
        }
    };

    self.cache.insert(key, result);
    result
}
```

**Key insight**: The hi branch combines three sub-cases:

- `hi_lo`: $f$ has the variable, $g$ doesn't
- `lo_hi`: $f$ doesn't have the variable, $g$ does
- `hi_hi`: both have the variable

All three produce sets with the variable, so they union into the hi branch.

---

## Memory Layout

### Node Storage

```
[ ZERO | ONE | Node_1 | Node_2 | ... ]
  idx0  idx1   idx2     idx3
```

All nodes live in a single Vec. Indices are permanently stable (no reallocation without copying).

**RefCell pattern**: Interior mutability for borrowing.

```rust
nodes: RefCell<Vec<ZddNode>>
```

Allows the manager to mutate node storage through immutable self reference.

---

### Subtable Bucket Layout

For each variable's subtable:

```
Bucket 0: Node_5 -> Node_12 -> Node_3 -> ...
Bucket 1: Node_7 -> Node_14 -> ...
Bucket 2: Node_2 -> ...
...
```

Intrusive chaining: each node's `next` field points to the next node in the same bucket.

**Why intrusive?**

- No extra allocation for chain nodes
- Better cache locality
- Simpler cleanup (no separate linked list structures)

---

## Performance Characteristics

### Time Complexity

| Operation | Time | Notes |
|-----------|------|-------|
| `base(v)` | O(1) | Create single node |
| `union/intersection` | $O(\|F\| × \|G\|)$ | Shannon expansion; memoized |
| `join` | $O(\|F\| × \|G\|)$ | More complex: 4-way recursion |
| `subset1` | $O(\|F\|)$ | Single recursive descent |
| `count` | $O(\|F\|)$ | Linear pass; memoized |
| `contains` | $O(n)$ | Path lookup; n = # variables |

---

### Space Complexity

**Node storage**: $O(M)$ where $M$ = total nodes in all ZDDs you create.

**Subtables**: $O(M)$ (one entry per node, per level).

**Caches**: $O(C)$ where $C$ = number of distinct operations performed. Typically $C \ll M^2$ because memoization prevents redundant computation.
**Total**: $O(M + C) \approx O(M)$ for typical usage.

---

## Memory Management

The current implementation uses **manual management**: nodes are created and never explicitly freed. This is sufficient for:

- One-shot analyses (build ZDD, query it, done)
- Research/prototyping
- Most practical problems don't create millions of nodes

For long-running systems with many ZDD operations, a **garbage collector** could reclaim unreachable nodes. This is left as future work (see `collect_garbage` placeholder).

---

## Performance Tips

### 1. Reuse ZDDs

```rust
// Good: Reuse the combination
let union_once = mgr.union(a, b);
let result1 = mgr.intersection(union_once, c);
let result2 = mgr.difference(union_once, d);

// Bad: Recompute union twice
let result1 = mgr.intersection(mgr.union(a, b), c);
let result2 = mgr.difference(mgr.union(a, b), d);
```

The cache makes reuse free; you avoid redundant computation.

---

### 2. Variable Ordering

```rust
// Good: Spatial locality (by row, then column)
for row in 0..8 {
    for col in 0..8 {
        mgr.ensure_var(Var::new(pos_to_var(row, col)));
    }
}

// Bad: Random ordering
let mut vars: Vec<_> = (1..=64).collect();
vars.shuffle(&mut rng);  // Creates large ZDDs
for var in vars {
    mgr.ensure_var(Var::new(var));
}
```

Good ordering clusters related variables, reducing intermediate ZDD sizes.

---

### 3. Filter Early

```rust
// Good: Apply constraints incrementally
let mut result = all_boards;
for (v1, v2) in conflicts {
    result = mgr.remove_sets_with_both(result, v1, v2);
}

// Bad: Build complete ZDD, then filter
let result = mgr.intersection(all_boards, valid_config);
```

Filtering early reduces memory and computation.

---

## Thread Safety

This implementation is **not thread-safe**. The `RefCell` pattern allows interior mutability but doesn't coordinate between threads.

For multi-threaded use:

- Create separate `ZddManager` instances per thread
- Synchronize results with mutexes/channels

---

Next: [Practical examples →](examples.md)
