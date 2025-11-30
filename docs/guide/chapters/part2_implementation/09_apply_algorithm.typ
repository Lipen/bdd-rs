#import "../../theme.typ": *

= The Apply Algorithm in Detail <ch-apply-algorithm>

Apply is the workhorse of BDD manipulation.
It takes two (or three) BDDs and a Boolean operation, and produces a new BDD representing the combined function.
Nearly *every* BDD operation --- from simple AND/OR to complex quantification --- flows through Apply.

Understanding Apply deeply means understanding BDD performance.
This chapter dissects the algorithm: terminal cases, normalization tricks, and the crucial role of caching that makes everything polynomial.

== The Big Picture

Apply computes $f op g$ for any binary Boolean operation $op$ (AND, OR, XOR, etc.).
The structure follows the recursive decomposition of Boolean functions:

#figure(
  cetz.canvas(length: 1cm, {
    import cetz.draw: *

    // Main flow diagram
    let start = (5, 7)
    let terminal-check = (5, 5.5)
    let cache-check = (5, 4)
    let decompose = (5, 2.5)
    let recurse = (5, 1)

    // Boxes
    rect((2.5, 6.6), (7.5, 7.4), fill: colors.box-definition, stroke: 1pt + colors.primary, radius: 4pt)
    content(start, text(size: 0.8em)[`apply_ite(f, g, h)`])

    rect((2, 5.1), (8, 5.9), fill: colors.box-warning.lighten(40%), stroke: 1pt + colors.warning, radius: 4pt)
    content(terminal-check, text(size: 0.8em)[Terminal cases? Return immediately])

    rect((2, 3.6), (8, 4.4), fill: colors.box-example.lighten(40%), stroke: 1pt + colors.success, radius: 4pt)
    content(cache-check, text(size: 0.8em)[Cache hit? Return cached result])

    rect((1.5, 2.1), (8.5, 2.9), fill: colors.box-insight.lighten(30%), stroke: 1pt + colors.info, radius: 4pt)
    content(decompose, text(size: 0.8em)[Find top variable $v$, compute cofactors])

    rect((1.5, 0.6), (8.5, 1.4), fill: colors.box-theorem.lighten(30%), stroke: 1pt + colors.primary, radius: 4pt)
    content(recurse, text(
      size: 0.8em,
    )[Recurse: $t = "ite"(f_v, g_v, h_v)$, $e = "ite"(f_(not v), g_(not v), h_(not v))$])

    // Arrows
    line((5, 6.6), (5, 5.9), stroke: 1pt + colors.text-muted, mark: (end: ">"))
    line((5, 5.1), (5, 4.4), stroke: 1pt + colors.text-muted, mark: (end: ">"))
    line((5, 3.6), (5, 2.9), stroke: 1pt + colors.text-muted, mark: (end: ">"))
    line((5, 2.1), (5, 1.4), stroke: 1pt + colors.text-muted, mark: (end: ">"))

    // Result arrow
    line((5, 0.6), (5, -0.2), stroke: 1pt + colors.text-muted, mark: (end: ">"))
    content((5, -0.6), text(size: 0.8em)[`mk(v, e, t)` $->$ cache $->$ return])

    // Side notes
    content(
      (9.5, 5.5),
      align(left)[
        #set text(size: 0.7em, fill: colors.text-muted)
        $O(1)$ checks:\
        constants,\
        equal args
      ],
      anchor: "west",
    )

    content(
      (9.5, 4),
      align(left)[
        #set text(size: 0.7em, fill: colors.text-muted)
        Key to\
        polynomial\
        complexity
      ],
      anchor: "west",
    )
  }),
  caption: [High-level flow of the Apply (ITE) algorithm.],
)

The algorithm has polynomial complexity because of *memoization*: each unique triple $(f, g, h)$ is computed at most once.

== Everything is ITE

In `bdd-rs`, all operations go through the *ITE* (if-then-else) primitive:

$ "ite"(f, g, h) = (f and g) or (not f and h) $

Every binary operation can be expressed as ITE:

#table(
  columns: (auto, auto, auto),
  align: (left, center, left),
  table.header([*Operation*], [*Formula*], [*ITE Encoding*]),
  [$f and g$], [$f dot g$], [$ite(f, g, 0)$],
  [$f or g$], [$f + g$], [$ite(f, 1, g)$],
  [$f xor g$], [$f xor g$], [$ite(f, not g, g)$],
  [$f -> g$], [$overline(f) + g$], [$ite(f, g, 1)$],
  [$f equiv g$], [$overline(f xor g)$], [$ite(f, g, not g)$],
)

This unification simplifies implementation --- one algorithm handles everything.

== Terminal Cases

Terminal cases are where recursion stops.
More terminal cases mean faster computation.

=== Constant Arguments

```rust
// ite(1, g, h) = g
if self.is_one(f) { return g; }

// ite(0, g, h) = h
if self.is_zero(f) { return h; }
```

=== Equal and Complementary Arguments

```rust
// ite(f, g, g) = g  (doesn't matter what f is)
if g == h { return g; }

// ite(f, 1, 0) = f
if self.is_one(g) && self.is_zero(h) { return f; }

// ite(f, 0, 1) = ¬f
if self.is_zero(g) && self.is_one(h) { return -f; }
```

=== Advanced Terminal Cases

These catch more patterns:

```rust
// ite(f, 1, ¬f) = 1
if self.is_one(g) && h == -f { return self.one(); }

// ite(f, f, 0) = f  (f AND f = f)
if g == f && self.is_zero(h) { return f; }

// ite(f, ¬f, 0) = 0  (f AND ¬f = 0)
if g == -f && self.is_zero(h) { return self.zero(); }
```

#example-box(title: "Terminal Cases for AND")[
  Since $f and g = "ite"(f, g, 0)$, terminal cases include:
  - `ite(0, g, 0) = 0` (absorbing element)
  - `ite(1, g, 0) = g` (identity)
  - `ite(f, f, 0) = f` (idempotent)
  - `ite(f, ¬f, 0) = 0` (complement)
]

== Standard Triples: Cache Optimization

*Standard triples* normalize equivalent ITE calls to improve cache hit rates.

The insight: `ite(f, 1, g)` and `ite(g, 1, f)` compute the same function ($f or g$).
If we always put the "smaller" BDD first, they'll hit the same cache entry.

```rust
// ite(f, f, h) → ite(f, 1, h)  (f in "then" position is redundant)
if g == f {
    return self.apply_ite(f, self.one, h);
}
// ite(f, g, f) → ite(f, g, 0)  (f in "else" position is redundant)
if h == f {
    return self.apply_ite(f, g, self.zero);
}
// ite(f, ¬f, h) → ite(f, 0, h)
if g == -f {
    return self.apply_ite(f, self.zero, h);
}
// ite(f, g, ¬f) → ite(f, g, 1)
if h == -f {
    return self.apply_ite(f, g, self.one);
}
```

=== Argument Ordering

When possible, reorder arguments so the smallest-variable BDD comes first:

```rust
let i = self.variable(f.id());
let j = self.variable(g.id());
let k = self.variable(h.id());

// ite(f, 1, h) == ite(h, 1, f) == f ∨ h
// Choose the one with smaller top variable
if self.is_one(g) && self.var_precedes(k, i) {
    return self.apply_ite(h, self.one, f);
}
// ite(f, g, 0) == ite(g, f, 0) == f ∧ g
if self.is_zero(h) && self.var_precedes(j, i) {
    return self.apply_ite(g, f, self.zero);
}
```

This normalization ensures that `ite(f, 1, g)` and `ite(g, 1, f)` hit the same cache entry.

== Complement Edge Handling

The canonical form requires that the "then" branch (g) is never negated:

```rust
let (mut f, mut g, mut h) = (f, g, h);

// ite(¬f, g, h) → ite(f, h, g)
if f.is_negated() {
    f = -f;
    std::mem::swap(&mut g, &mut h);
}
assert!(!f.is_negated());

// ite(f, ¬g, h) → ¬ite(f, g, ¬h)
let mut n = false;
if g.is_negated() {
    n = true;
    g = -g;
    h = -h;
}
assert!(!g.is_negated());
```

The `n` flag tracks whether we need to negate the final result.
This normalization is crucial for cache efficiency --- without it, `ite(f, g, h)` and `ite(f, -g, -h)` would be cached separately.

#insight-box[
  Complement edge normalization can *double* cache hit rates.
  The small overhead of checking and swapping is far outweighed by reduced redundant computation.
]

== Cofactor Computation

Given the top variable $v$, we need cofactors of all three arguments:

```rust
// Determine top variable (smallest in ordering)
let mut m = i;  // f's variable
if !j.is_terminal() {
    m = self.top_variable(m, j);
}
if !k.is_terminal() {
    m = self.top_variable(m, k);
}

// Get cofactors
let (ft, fe) = self.top_cofactors(f, m);  // f|_{m=1}, f|_{m=0}
let (gt, ge) = self.top_cofactors(g, m);
let (ht, he) = self.top_cofactors(h, m);
```

The `top_cofactors` function handles three cases:

```rust
pub fn top_cofactors(&self, node_ref: Ref, v: Var) -> (Ref, Ref) {
    // Terminal: cofactors are the terminal itself
    if self.is_terminal(node_ref) {
        return (node_ref, node_ref);
    }

    let node = self.node(node_ref.id());

    // Variable not at this node: function doesn't depend on v
    if self.var_precedes(v, node.variable) {
        return (node_ref, node_ref);
    }

    // Variable matches: return children (respecting complement)
    assert_eq!(v, node.variable);
    if node_ref.is_negated() {
        (-node.low, -node.high)
    } else {
        (node.low, node.high)
    }
}
```

#info-box(title: "Cofactor Computation")[
  For a node with variable $x$:
  - If we're computing the cofactor for $x$: return low or high child
  - If we're computing the cofactor for a variable $y < x$ (above in ordering): the function doesn't depend on $y$, return the node itself
]

== The Recursive Step

With cofactors computed, we recurse:

```rust
// Recursive calls on cofactors
let t = self.apply_ite(ft, gt, ht);  // "then" branch
let e = self.apply_ite(fe, ge, he);  // "else" branch

// Build result
let result = self.mk_node(m, e, t);  // Note: low = else, high = then

// Cache and return
self.cache_mut().insert(key, result);
if n { -result } else { result }
```

Note the argument order to `mk_node`: low (else) comes before high (then).
This matches the Shannon decomposition $f = (not v and f_"low") or (v and f_"high")$.

== The Complete ITE Implementation

Here's the full implementation structure:

#algorithm(title: "apply_ite (ITE Operation)")[
  ```
  apply_ite(f, g, h):
    // Terminal cases (constants)
    if f == 1: return g
    if f == 0: return h
    if g == h: return g
    if g == 1 and h == 0: return f
    if g == 0 and h == 1: return -f
    // ... more terminal cases ...

    // Standard triple normalizations
    if g == f: return apply_ite(f, 1, h)
    if h == f: return apply_ite(f, g, 0)
    // ... more normalizations ...

    // Argument ordering (smallest variable first)
    // ... reordering logic ...

    // Complement edge normalization
    if f.is_negated():
      f = -f; swap(g, h)
    n = false
    if g.is_negated():
      n = true; g = -g; h = -h

    // Cache lookup
    key = (f, g, h)
    if key in cache: return cache[key] (negated if n)

    // Determine top variable
    m = top_var(f, g, h)

    // Get cofactors
    (ft, fe) = top_cofactors(f, m)
    (gt, ge) = top_cofactors(g, m)
    (ht, he) = top_cofactors(h, m)

    // Recurse
    t = apply_ite(ft, gt, ht)
    e = apply_ite(fe, ge, he)

    // Build and cache result
    result = mk(m, e, t)
    cache[key] = result
    return result (negated if n)
  ```
]

== Complexity Analysis

#theorem(title: "ITE Complexity")[
  For BDDs $f$, $g$, and $h$, `apply_ite(f, g, h)` runs in $O(|f| times |g| times |h|)$ time.
]

#proof[
  The cache key is the triple $(f, g, h)$ after normalization.
  There are at most $|f| times |g| times |h|$ distinct triples.
  Each non-cached call does $O(1)$ work (excluding recursive calls).
  Therefore, total time is bounded by $O(|f| times |g| times |h|)$.
]

For binary operations where one argument is constant, this simplifies:
- $f and g = ite(f, g, 0)$: $O(|f| times |g|)$ since $|0| = 1$
- $f or g = ite(f, 1, g)$: $O(|f| times |g|)$

== Iterative vs. Recursive Implementation

The recursive implementation is clean but has a limitation: deep BDDs can overflow the call stack.

```rust
// Recursive (current bdd-rs approach)
fn apply_ite(&self, f: Ref, g: Ref, h: Ref) -> Ref {
    // ... base cases ...
    let t = self.apply_ite(ft, gt, ht);  // Stack frame
    let e = self.apply_ite(fe, ge, he);  // Another stack frame
    self.mk_node(m, e, t)
}
```

For very large BDDs (millions of nodes), an *iterative* implementation with an explicit stack avoids overflow:

```rust
// Iterative alternative
fn apply_ite_iterative(&self, f: Ref, g: Ref, h: Ref) -> Ref {
    let mut stack = Vec::new();
    stack.push(Task::Compute(f, g, h));

    while let Some(task) = stack.pop() {
        match task {
            Task::Compute(f, g, h) => {
                // Check cache, terminal cases...
                // Push continuation and recursive tasks
                stack.push(Task::Combine(m, key));
                stack.push(Task::Compute(fe, ge, he));
                stack.push(Task::Compute(ft, gt, ht));
            }
            Task::Combine(m, key) => {
                // Pop results, build node, cache
            }
        }
    }
    // Return final result
}
```

The trade-off:
- *Recursive*: Cleaner code, limited by stack size
- *Iterative*: More complex, handles arbitrarily deep BDDs

#performance-note[
  BDD operations are exponentially faster in release mode.
  Debug builds have significant overhead from bounds checking and unoptimized recursion.
  Always benchmark with `--release`.
]

== Operation-Specific Optimizations

While ITE is universal, specialized implementations can be faster:

=== AND Optimization

```rust
pub fn apply_and(&self, f: Ref, g: Ref) -> Ref {
    // Special terminal rules for AND
    if self.is_zero(f) || self.is_zero(g) {
        return self.zero;  // Short-circuit
    }
    if self.is_one(f) {
        return g;
    }
    if self.is_one(g) {
        return f;
    }
    if f == g {
        return f;  // Idempotent
    }
    if f == -g {
        return self.zero;  // Contradiction
    }
    // Fall back to ITE
    self.apply_ite(f, g, self.zero)
}
```

=== XOR and Complement Edges

XOR has a special relationship with complement edges:

$ f xor g = not(f xor not g) $

This means XOR can often be computed by just flipping a complement bit:

```rust
pub fn apply_xor(&self, f: Ref, g: Ref) -> Ref {
    // f ⊕ 0 = f
    if self.is_zero(g) {
        return f;
    }
    // f ⊕ 1 = ¬f
    if self.is_one(g) {
        return -f;
    }
    // f ⊕ f = 0
    if f == g {
        return self.zero;
    }
    // f ⊕ ¬f = 1
    if f == -g {
        return self.one;
    }
    // General case
    self.apply_ite(f, -g, g)
}
```

== Summary

The Apply/ITE algorithm is the workhorse of BDD manipulation.
Its efficiency comes from:

+ *Aggressive terminal case checking*: Stop recursion as early as possible
+ *Standard triple normalization*: Maximize cache reuse
+ *Complement edge handling*: Unify equivalent computations
+ *Memoization*: Never recompute the same subproblem

The implementation in `bdd-rs` follows the classic CUDD approach, optimized for single-threaded use with interior mutability.
