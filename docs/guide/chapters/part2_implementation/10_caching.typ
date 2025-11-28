#import "../../theme.typ": *

= Caching and Computed Tables <ch-caching>

The Apply algorithm's polynomial complexity depends critically on *memoization* --- remembering the results of subproblems to avoid redundant computation.
Without caching, BDD operations would have exponential time complexity.
This chapter explores the cache (also called the *computed table*) that makes BDDs practical.

== Why Caching Matters

Consider computing $f and g$ where both BDDs have $n$ nodes.
The recursive structure of Apply creates a call tree:

```
Apply(AND, f, g)
├── Apply(AND, f_low, g_low)
│   ├── Apply(AND, ...)
│   │   └── ...
│   └── Apply(AND, ...)
│       └── ...
└── Apply(AND, f_high, g_high)
    ├── Apply(AND, ...)
    │   └── ...
    └── Apply(AND, ...)
        └── ...
```

Without memoization, this tree can have exponentially many leaves.
The same subproblem `Apply(AND, u, v)` might be computed repeatedly from different branches.

With caching, each unique $(op, u, v)$ triple is computed *exactly once*.
Since there are at most $O(|f| times |g|)$ such triples, the algorithm becomes polynomial.

#insight-box[
  The computed table is what transforms BDD operations from exponential to polynomial.
  It ensures that each unique subproblem is solved exactly once.
]

#theorem(title: "Caching Necessity")[
  Without memoization, Apply has worst-case time complexity $O(2^n)$ where $n$ is the number of variables.
  With memoization, the complexity is $O(|f| times |g|)$ where $|f|$ and $|g|$ are BDD sizes.
]

This is the classic *dynamic programming* pattern: identify overlapping subproblems, solve each once, and store results for reuse.

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
  [*Property*], [*Unique Table*], [*Computed Table (Cache)*],
  [Purpose], [Hash consing (node dedup)], [Memoization (result reuse)],
  [Key], [$("var", "low", "high")$], [$("op", f, g, h)$],
  [Value], [NodeId], [Ref (result)],
  [Lifetime], [Permanent], [May evict on collision],
  [Correctness], [Required for canonicity], [Only affects performance],
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

The lookup has three outcomes:
+ *Hit*: The key matches --- return cached result
+ *Fault*: Different key at this index --- collision
+ *Miss*: Empty slot --- no entry to check

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
  [*Cache Size*], [*Memory*], [*Hit Rate*], [*Use Case*],
  [$2^14$ (16K)], [~0.5 MB], [Lower], [Small problems],
  [$2^16$ (64K)], [~2 MB], [Good], [Default],
  [$2^18$ (256K)], [~8 MB], [Better], [Large problems],
  [$2^20$ (1M)], [~32 MB], [Excellent], [Very large problems],
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
  [*Strategy*], [*Complexity*], [*Hit Rate*], [*Memory*],
  [Direct-mapped], [Simple --- $O(1)$], [Lower], [Minimal],
  [Set-associative], [Medium --- $O(k)$ for $k$-way], [Better], [Slight overhead],
  [Fully associative], [Complex --- $O(n)$ or LRU], [Best], [Significant overhead],
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
