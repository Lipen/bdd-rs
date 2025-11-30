#import "../../theme.typ": *

= Caching and Computed Tables <ch-caching>

The Apply algorithm's polynomial complexity hinges on *memoization* --- remembering results to avoid redundant computation.
Without caching, BDD operations degrade to exponential time, no better than brute-force enumeration.
This chapter explores the cache (also called the *computed table*) that transforms BDDs from a theoretical curiosity into a practical powerhouse.

== Why Caching Matters

Consider computing $f and g$ where both BDDs have $n$ nodes.
The recursive structure of Apply spawns a call tree that branches at every non-terminal node:

#figure(
  cetz.canvas(length: 1cm, {
    import cetz.draw: *

    // Without cache - exponential
    content((3, 6.5), text(weight: "bold", fill: colors.error)[Without Cache])

    // Tree structure
    rect((2.2, 5.5), (3.8, 6.1), fill: colors.box-definition.lighten(20%), stroke: 1pt + colors.primary, radius: 3pt)
    content((3, 5.8), text(size: 0.7em)[`Apply(∧,f,g)`])

    // Level 2
    rect((0.8, 4.2), (2.2, 4.8), fill: colors.bg-code, stroke: 0.5pt + colors.line, radius: 2pt)
    content((1.5, 4.5), text(size: 0.7em)[`Apply(∧,u,v)`])
    rect((3.8, 4.2), (5.2, 4.8), fill: colors.bg-code, stroke: 0.5pt + colors.line, radius: 2pt)
    content((4.5, 4.5), text(size: 0.7em)[`Apply(∧,u',v')`])

    // Level 3 - showing duplicates
    rect((0, 3), (1.2, 3.5), fill: colors.box-warning.lighten(30%), stroke: 0.5pt + colors.warning, radius: 2pt)
    content((0.6, 3.25), text(size: 0.7em)[`Apply(a,b)`])
    rect((1.5, 3), (2.7, 3.5), fill: colors.box-warning.lighten(30%), stroke: 0.5pt + colors.warning, radius: 2pt)
    content((2.1, 3.25), text(size: 0.7em)[`Apply(a,b)`])
    rect((3.3, 3), (4.5, 3.5), fill: colors.box-warning.lighten(30%), stroke: 0.5pt + colors.warning, radius: 2pt)
    content((3.9, 3.25), text(size: 0.7em)[`Apply(a,b)`])
    rect((4.8, 3), (6, 3.5), fill: colors.box-warning.lighten(30%), stroke: 0.5pt + colors.warning, radius: 2pt)
    content((5.4, 3.25), text(size: 0.7em)[`Apply(a,b)`])

    // Lines
    line((3, 5.5), (1.5, 4.8), stroke: 0.5pt + colors.line)
    line((3, 5.5), (4.5, 4.8), stroke: 0.5pt + colors.line)
    line((1.5, 4.2), (0.6, 3.5), stroke: 0.5pt + colors.line)
    line((1.5, 4.2), (2.1, 3.5), stroke: 0.5pt + colors.line)
    line((4.5, 4.2), (3.9, 3.5), stroke: 0.5pt + colors.line)
    line((4.5, 4.2), (5.4, 3.5), stroke: 0.5pt + colors.line)

    content((3, 2.3), text(size: 0.8em, fill: colors.error)[Same subproblem computed 4× !])
    content((3, 1.8), text(size: 0.8em, fill: colors.error)[Exponential blowup: $O(2^n)$])

    // Arrow
    line((6.5, 4.2), (8, 4.2), stroke: 2pt + colors.success, mark: (end: ">", fill: colors.success))

    // With cache - polynomial
    content((11, 6.5), text(weight: "bold", fill: colors.success)[With Cache])

    // Cache table
    rect(
      (8.8, 2.5),
      (13.2, 6),
      fill: colors.box-example.lighten(50%),
      stroke: 1pt + colors.success.lighten(20%),
      radius: 4pt,
    )
    content((11, 5.5), text(size: 0.8em, weight: "semibold")[Computed Table])

    // Cache entries
    rect((9.2, 4.5), (12.8, 5.1), fill: white, stroke: 0.5pt + colors.line, radius: 2pt)
    content((11, 4.8), text(size: 0.7em)[`(∧, f, g) → result₁`])

    rect((9.2, 3.8), (12.8, 4.4), fill: white, stroke: 0.5pt + colors.line, radius: 2pt)
    content((11, 4.1), text(size: 0.7em)[`(∧, u, v) → result₂`])

    rect((9.2, 3.1), (12.8, 3.7), fill: colors.box-definition.lighten(30%), stroke: 1pt + colors.primary, radius: 2pt)
    content((11, 3.4), text(size: 0.7em)[`(∧, a, b) → result₃ ✓`])

    // Arrow showing reuse
    content((11, 2.0), text(size: 0.8em, fill: colors.success)[Computed once, reused!])
    content((11, 1.5), text(size: 0.8em, fill: colors.success)[Polynomial: $O(|f| times |g|)$])
  }),
  caption: [Without caching (left), identical subproblems are recomputed exponentially. With caching (right), each unique subproblem is solved once.],
)

Without memoization, this tree can have exponentially many leaves.
The same subproblem `Apply(AND, u, v)` appears repeatedly from different branches --- and each time, we would naively recompute it from scratch.

With caching, each unique $("op", u, v)$ triple is computed *exactly once* and stored.
Since there are at most $O(|f| times |g|)$ such triples, the algorithm achieves polynomial time.

#theorem(title: "Caching Complexity")[
  Without memoization: $O(2^n)$ worst-case (exponential).
  With memoization: $O(|f| times |g|)$ (polynomial).
]

== Cache Structure

The cache in `bdd-rs` is a fixed-size hash table mapping operation keys to results:

```rust
pub struct Cache<K, V> {
    data: Vec<Option<Entry<K, V>>>,
    bitmask: u64,       // For fast index computation
    hits: Cell<usize>,  // Successful lookups
    faults: Cell<usize>, // Collisions (wrong key at index)
    misses: Cell<usize>, // Total unsuccessful lookups
}

struct Entry<K, V> {
    key: K,
    value: V,
}
```

#figure(
  cetz.canvas(length: 1cm, {
    import cetz.draw: *

    // Cache visualization
    content((5, 6.5), text(weight: "bold", size: 1em)[Direct-Mapped Cache])

    // Hash table slots
    for i in range(8) {
      let y = 5.5 - i * 0.55
      rect(
        (2, y - 0.22),
        (8, y + 0.22),
        fill: if i == 3 { colors.box-definition.lighten(30%) } else { colors.bg-code },
        stroke: 0.5pt + colors.line,
      )
      content((2.5, y), text(size: 0.7em, fill: colors.text-muted)[#i])
    }

    // Labels
    content((1.3, 5.5), text(size: 0.7em)[Index], anchor: "east")

    // Sample entry in slot 3
    content((5, 5.5 - 3 * 0.55), text(size: 0.7em)[`(∧, ref_5, ref_9) → ref_12`])

    // Hash arrow
    let query_y = 6
    rect(
      (8.5, query_y - 0.3),
      (12.5, query_y + 0.3),
      fill: colors.box-example.lighten(30%),
      stroke: 1pt + colors.success.lighten(20%),
      radius: 3pt,
    )
    content((10.5, query_y), text(size: 0.7em)[Query: `(∧, 5, 9)`])

    // Hash function
    content((10.5, 5.2), text(size: 0.7em)[`hash(5,9) & mask`])
    line((10.5, 5), (10.5, 4.5), stroke: 1pt + colors.text-muted, mark: (end: ">"))
    content((10.5, 4.2), text(size: 0.7em)[`= 3`])

    // Arrow to slot 3
    line((9, 4.2), (8, 5.5 - 3 * 0.55), stroke: 1.5pt + colors.primary, mark: (end: ">", fill: colors.primary))

    // Three outcomes
    content((5, 0.8), text(size: 0.8em, fill: colors.success)[*Hit*: Key matches → return cached result])
    content((5, 0.3), text(size: 0.8em, fill: colors.warning)[*Fault*: Different key → collision])
    content((5, -0.2), text(size: 0.8em, fill: colors.error)[*Miss*: Empty slot → compute fresh])
  }),
  caption: [The cache uses direct-mapped hashing. A query hashes to one slot; if the key matches, we have a hit.],
)

=== Key Structure

For ITE operations, the key is a triple of references:

```rust
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum OpKey {
    Ite(Ref, Ref, Ref),  // ite(f, g, h)
}
```

The key is hashed to find an index:

```rust
fn index(&self, key: &K) -> usize {
    (key.hash() & self.bitmask) as usize
}
```

The `bitmask` is `size - 1` where size is a power of two, making the modulo operation a simple bitwise AND.

=== Cache vs. Unique Table

It's important to distinguish these two hash-based structures:

#comparison-table(
  [*Property*],
  [*Unique Table*],
  [*Computed Table (Cache)*],
  [Purpose],
  [Hash consing (node dedup)],
  [Memoization (result reuse)],
  [Key],
  [$("var", "low", "high")$],
  [$("op", f, g, h)$],
  [Value],
  [NodeId],
  [Ref (result)],
  [Lifetime],
  [Permanent],
  [May evict on collision],
  [Correctness],
  [Required for canonicity],
  [Only affects performance],
)

The unique table is *essential* --- without it, BDDs lose canonicity.
The cache is an *optimization* --- without it, BDDs are correct but slow.

== Cache Operations

=== Lookup

```rust
pub fn get(&self, key: &K) -> Option<&V>
where
    K: Eq,
{
    let index = self.index(key);
    match &self.data[index] {
        Some(entry) => {
            if &entry.key == key {
                // Cache hit: exact key match
                self.hits.set(self.hits.get() + 1);
                Some(&entry.value)
            } else {
                // Cache fault: collision (different key)
                self.faults.set(self.faults.get() + 1);
                self.misses.set(self.misses.get() + 1);
                None
            }
        }
        None => {
            // Cache miss: empty slot
            self.misses.set(self.misses.get() + 1);
            None
        }
    }
}
```

=== Insert

```rust
pub fn insert(&mut self, key: K, value: V) {
    let index = self.index(&key);
    self.data[index] = Some(Entry { key, value });
}
```

Insert unconditionally overwrites the slot.
If another entry was there, it's lost (but this only affects performance, not correctness).

== Cache Sizing

The cache size is specified in bits:

```rust
impl<K, V> Cache<K, V> {
    pub fn new(bits: usize) -> Self {
        assert!(bits <= 31);
        let size = 1 << bits;  // 2^bits entries
        let bitmask = (size - 1) as u64;
        // ...
    }
}
```

In `bdd-rs`, the default is 16 bits = 65,536 entries:

```rust
impl Bdd {
    pub fn new(storage_bits: usize) -> Self {
        let cache_bits = 16;
        // ...
    }
}
```

=== Sizing Trade-offs

#comparison-table(
  [*Cache Size*],
  [*Memory*],
  [*Hit Rate*],
  [*Use Case*],
  [$2^(14)$ (16K)],
  [~0.5 MB],
  [Lower],
  [Small problems],
  [$2^(16)$ (64K)],
  [~2 MB],
  [Good],
  [Default],
  [$2^(18)$ (256K)],
  [~8 MB],
  [Better],
  [Large problems],
  [$2^(20)$ (1M)],
  [~32 MB],
  [Excellent],
  [Very large problems],
)

Memory estimates assume 32-byte entries (key + value + padding).

#info-box(title: "When to Increase Cache Size")[
  If you observe:
  - Hit rate below 70%
  - Large BDDs (millions of nodes)
  - Many repeated operations

  Consider increasing cache bits.
  Double the bits roughly quadruples memory but can significantly improve hit rates.
]

== Collision Handling

`bdd-rs` uses *direct-mapped* caching: each key maps to exactly one slot.
If two keys hash to the same index, the newer one overwrites the older.

=== Why Direct-Mapped?

#comparison-table(
  [*Strategy*],
  [*Complexity*],
  [*Hit Rate*],
  [*Memory*],
  [Direct-mapped],
  [Simple --- $O(1)$],
  [Lower],
  [Minimal],
  [Set-associative],
  [Medium --- $O(k)$ for $k$-way],
  [Better],
  [Slight overhead],
  [Fully associative],
  [Complex --- $O(n)$ or LRU],
  [Best],
  [Significant overhead],
)

Direct-mapped is the simplest and fastest, at the cost of more collisions.
For BDD operations, this trade-off usually favors simplicity:
- Operations are fast, so cache overhead matters
- Collisions lose performance but not correctness
- Memory efficiency allows larger caches

=== Collision Statistics

```rust
impl Cache<K, V> {
    pub fn hits(&self) -> usize;   // Successful lookups
    pub fn faults(&self) -> usize; // Key mismatch (collision)
    pub fn misses(&self) -> usize; // Total failures (empty + fault)
}
```

The *fault rate* indicates collision frequency:

$ "fault rate" = "faults" / ("hits" + "misses") $

High fault rates suggest:
- Cache is too small
- Hash function has poor distribution
- Working set exceeds cache capacity

#implementation-note[
  `bdd-rs` provides cache statistics via `cache.hits()`, `cache.misses()`, and `cache.faults()`.
  A hit rate below 80% may indicate the cache is too small.
]

== Hash Function Design

The cache's effectiveness depends on a good hash function.
`bdd-rs` uses a combination of pairing functions and bit mixing:

```rust
// Szudzik pairing function
pub const fn pairing_szudzik(a: u64, b: u64) -> u64 {
    if a < b {
        b.wrapping_mul(b).wrapping_add(a)
    } else {
        a.wrapping_mul(a).wrapping_add(a).wrapping_add(b)
    }
}

// MurmurHash3 finalizer for bit mixing
pub const fn mix64(mut x: u64) -> u64 {
    x = x.wrapping_mul(0xff51afd7ed558ccd);
    x ^= x >> 33;
    x = x.wrapping_mul(0xc4ceb9fe1a85ec53);
    x ^= x >> 33;
    x
}
```

For ITE keys, the hash combines three `Ref` values:

```rust
impl MyHash for OpKey {
    fn hash(&self) -> u64 {
        match self {
            OpKey::Ite(f, g, h) => {
                combine3(f.raw() as u64, g.raw() as u64, h.raw() as u64)
            }
        }
    }
}
```

== Multiple Caches

`bdd-rs` maintains separate caches for different purposes:

=== Operation Cache

```rust
cache: RefCell<Cache<OpKey, Ref>>
```

This is the main cache for ITE results.
All binary operations (AND, OR, XOR, etc.) go through ITE, so this single cache covers them all.

=== Size Cache

```rust
size_cache: RefCell<Cache<Ref, u64>>
```

The `size` function (counting nodes in a BDD) is cached separately:

```rust
pub fn size(&self, node_ref: Ref) -> u64 {
    if let Some(&size) = self.size_cache().get(&node_ref) {
        return size;
    }
    // ... compute size ...
    self.size_cache_mut().insert(node_ref, size);
    size
}
```

Why separate caches?
- *Different key types*: OpKey vs. Ref
- *Different access patterns*: Size is queried less frequently
- *Cache pollution*: Mixing would reduce hit rates

=== When to Clear Caches

Caches should be cleared when:
- After variable reordering (node indices change)
- When memory pressure is high
- Starting a new, unrelated computation phase

```rust
// In bdd-rs reordering code:
self.cache_mut().clear();
self.size_cache_mut().clear();
```

== Cache in the Apply Flow

Here's how caching fits into the overall Apply/ITE algorithm:

#algorithm(title: "Apply with Caching")[
  ```
  apply_ite(f, g, h):
    // 1. Terminal cases (no cache needed)
    if f == 1: return g
    if f == 0: return h
    // ... more terminals ...

    // 2. Normalize for cache efficiency
    if f.is_negated(): f = -f; swap(g, h)
    if g.is_negated(): negate_result = true; g = -g; h = -h

    // 3. Cache lookup
    key = (f, g, h)
    if key in cache:
      return cache[key]  // HIT: avoid recursion

    // 4. Recursive computation (cache MISS)
    m = top_variable(f, g, h)
    (f0, f1) = cofactors(f, m)
    (g0, g1) = cofactors(g, m)
    (h0, h1) = cofactors(h, m)
    e = apply_ite(f0, g0, h0)
    t = apply_ite(f1, g1, h1)
    result = mk(m, e, t)

    // 5. Cache insert
    cache[key] = result
    return result
  ```
]

The normalization step (2) is crucial for cache efficiency.
Without it, `ite(f, g, h)` and `ite(-f, h, g)` would be cached separately, wasting space and missing reuse opportunities.

== Performance Analysis

=== Cache Hit Rate Impact

Consider a computation making $N$ recursive calls:
- With 0% hit rate: All $N$ calls execute fully
- With 50% hit rate: ~$N/2$ calls execute fully
- With 90% hit rate: ~$N/10$ calls execute fully

Since each call involves node construction, cache lookup, and potentially allocation, the savings compound.

=== Measuring Cache Effectiveness

```rust
let bdd = Bdd::default();
// ... perform operations ...

let cache = bdd.cache();
let hits = cache.hits();
let misses = cache.misses();
let faults = cache.faults();

let total = hits + misses;
let hit_rate = hits as f64 / total as f64;
let fault_rate = faults as f64 / total as f64;

println!("Hit rate: {:.1}%", hit_rate * 100.0);
println!("Fault rate: {:.1}%", fault_rate * 100.0);
```

#warning-box(title: "Cache Pitfall")[
  A high hit rate doesn't always mean good performance.
  If the working set is small, even a tiny cache has high hit rate.
  Compare *absolute* hit counts and execution time, not just percentages.
]

== Summary

The computed table is simple in concept but critical in practice:

+ *Structure*: Fixed-size hash table with direct mapping
+ *Key*: Normalized operation triple $(f, g, h)$
+ *Collision handling*: Overwrite (lossy but fast)
+ *Sizing*: Power of two, typically $2^16$ to $2^20$
+ *Statistics*: Track hits, misses, faults for diagnostics

The cache transforms BDD operations from exponential to polynomial complexity, making the entire data structure practical for real-world use.
