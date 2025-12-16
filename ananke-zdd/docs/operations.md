# ZDD Operations Reference

## Constructors

### `base(v)` - Singleton Variable

```rust
let x1 = mgr.base(1);  // {{1}}
```

Creates a family containing exactly one set: $\{ v \}$.

**Implementation**: Creates a node where $v$ is at the decision point, lo=⊥, hi=⊤.

**Complexity**: $O(1)$

---

### `singleton(vars)` - Multi-Element Singleton

```rust
let s = mgr.singleton([1, 2, 3]);  // {{1, 2, 3}}
```

Creates a family containing exactly one set with all given elements.

**Implementation**: Builds a chain of nodes from top to bottom, where each node adds one variable to the set.

**Complexity**: $O(n)$ where $n$ = number of variables

---

### `powerset(vars)` - All Subsets

```rust
let p = mgr.powerset([1, 2, 3]);  // 2^3 = all 8 subsets
```

Creates the power set $2^S$ where $S = \{ \mathit{vars} \}$.

**Implementation**: At each variable level, both lo and hi branches lead to the same subtree (representing "include or exclude this variable").

**Complexity**: $O(n)$ nodes, $O(1)$ construction

---

### `combinations(vars, k)` - K-Element Subsets

```rust
let c42 = mgr.combinations([1, 2, 3, 4], 2);  // 6 subsets: {1,2}, {1,3}, {1,4}, {2,3}, {2,4}, {3,4}
```

Creates all $k$-element subsets of the given variables.

**Implementation**: Recursive with memoization. At each variable, either skip it (recurse with same $k$) or include it (recurse with $k-1$).

**Complexity**: $O(n \times k)$ nodes

---

## Set-Theoretic Operations

### `union(F, G)` - Set Family Union

```rust
let u = mgr.union(f, g);
```

Returns family containing all sets from $F$ and all sets from $G$.

**Semantics**: $F \cup G$

**Implementation**: Shannon expansion; recurse on both branches, combine results.

**Complexity**: $O(|F| \times |G|)$ time, $O(|F| \times |G|)$ space

---

### `intersection(F, G)` - Set Family Intersection

```rust
let i = mgr.intersection(f, g);
```

Returns family containing only sets that appear in both $F$ and $G$.

**Semantics**: $F \cap G$

**Implementation**: Recurse only when variables match; prune branches where families diverge.

**Complexity**: $O(|F| \times |G|)$ time

---

### `difference(F, G)` - Set Difference

```rust
let d = mgr.difference(f, g);
```

Returns family containing sets in $F$ but not in $G$.

**Semantics**: $F \setminus G = F \cap G^c$ (where $G^c$ is the complement)

**Implementation**: Subtract $G$ from $F$ by recursing through both and removing matched paths.
**Complexity**: $O(|F| \times |G|)$ time

---

### `symmetric_difference(F, G)` - XOR of Families

```rust
let s = mgr.symmetric_difference(f, g);
```

Returns sets in exactly one of $F$ or $G$.

**Semantics**: $F \triangle G = (F \setminus G) \cup (G \setminus F)$

**Implementation**: Computed as `difference(union(F, G), intersection(F, G))`

**Complexity**: $O(|F| \times |G|)$ time

---

## ZDD-Specific Operations

### `join(F, G)` - Cross Product

```rust
let j = mgr.join(f, g);  // {S ∪ T | S ∈ F, T ∈ G}
```

The fundamental ZDD operation. Computes all unions of pairs from the two families.

**Semantics**: $F \otimes G$

**Example**:

```rust
let f = mgr.base(1);     // {{1}}
let g = mgr.base(2);     // {{2}}
let j = mgr.join(f, g);  // {{1, 2}}

let f2 = mgr.union(mgr.base(1), mgr.base(3));  // {{1}, {3}}
let j2 = mgr.join(f2, g);                       // {{1,2}, {3,2}}
```

**Why join is powerful**: Most combinatorial enumeration problems reduce to joins:

- All $k$-element subsets: join $k$ singleton families
- All valid configurations: join constraint families

**Implementation**: Careful merging of all four branch combinations (lo-lo, hi-lo, lo-hi, hi-hi).

**Complexity**: $O(|F| \times |G|)$ best case, $O(|F| \times |G|)$ space

---

### `subset0(F, v)` - Filter Out Variable

```rust
let s0 = mgr.subset0(f, Var::new(1));
```

Returns all sets in $F$ that DO NOT contain $v$.

**Semantics**: $\{S \in F \mid v \notin S\}$

**Example**:

```rust
// F = {{1}, {2}, {1, 2}}
let s0 = mgr.subset0(f, Var::new(1));  // {{2}}
```

**Implementation**: Traverse to $v$'s node, return lo branch.

**Complexity**: $O(|F|)$ time

---

### `subset1(F, v)` - Extract with Removal

```rust
let s1 = mgr.subset1(f, Var::new(1));
```

Returns all sets containing $v$, but with $v$ removed.

**Semantics**: $\{S \setminus \{v\} \mid v \in S \in F\}$

**Example**:

```rust
// F = {{1}, {2}, {1, 2}}
let s1 = mgr.subset1(f, Var::new(1));  // {{}, {2}} (from {1} and {1,2})
```

**Implementation**: Traverse to $v$'s node, return hi branch (which already has $v$ removed by ZDD structure).

**Complexity**: $O(|F|)$ time

---

### `change(F, v)` - Toggle Variable

```rust
let c = mgr.change(f, Var::new(1));
```

Toggles $v$ in all sets: adds $v$ if not present, removes if present.

**Semantics**: $\{S \triangle \{v\} \mid S \in F\}$

**Example**:

```rust
// F = {{1}}
let c = mgr.change(f, Var::new(1));  // {{}} (removed 1)
let c2 = mgr.change(mgr.one(), Var::new(1));  // {{1}} (added 1 to {})
```

**Implementation**: Swap lo and hi branches at the target variable.

**Complexity**: $O(|F|)$ time

---

### `onset(F, v)` - Keep With Variable

```rust
let on = mgr.onset(f, Var::new(1));
```

Returns all sets containing $v$, keeping $v$ in the result.

**Semantics**: $\{S \in F \mid v \in S\}$

**Differs from subset1**: subset1 removes $v$; onset keeps it.
**Implementation**: `onset(F, v) = join(subset1(F, v), base(v))`

**Complexity**: $O(|F|)$ time

---

### `offset(F, v)` - Alias for subset0

Identical to subset0; provided for API consistency.

---

### `meet(F, G)` - Non-Empty Intersections

```rust
let m = mgr.meet(f, g);
```

Returns $\{S \cap T \mid S \in F, T \in G, S \cap T \neq \emptyset\}$.

Only non-empty intersections (excludes the empty set).

**Implementation**: Like join but only hi-branches contribute to result's hi.

**Complexity**: $O(|F| \times |G|)$ time

---

## Helper Operations

### `add_element_to_all(F, v)` - Add to Every Set

```rust
let f2 = mgr.add_element_to_all(f, Var::new(2));
```

Adds $v$ to all sets in $F$: $\{S \cup \{v\} \mid S \in F\}$.

**Semantics**: Equivalent to `join(F, base(v))`

**Implementation**: join with singleton family

**Complexity**: $O(|F|)$ time

---

### `remove_sets_with_both(F, v1, v2)` - Filter Pairs

```rust
let f2 = mgr.remove_sets_with_both(f, Var::new(1), Var::new(2));
```

Removes all sets containing both $v_1$ and $v_2$.

**Semantics**: $\{S \in F \mid \neg(v_1 \in S \wedge v_2 \in S)\}$

**Implementation**:

1. Extract sets with both: `s = subset1(subset1(F, v1), v2)`
2. Reconstruct by adding back: `add_element_to_all(add_element_to_all(s, v2), v1)`
3. Subtract from original: `difference(F, reconstructed)`

**Complexity**: $O(|F|)$ time

---

## Query Operations

### `contains_empty(F)` - Check for ∅

```rust
if mgr.contains_empty(f) {
    // F includes the empty set
}
```

Checks if the empty set is in the family.

**Implementation**: Follow lo branches until reaching ⊤.

**Complexity**: $O(\text{depth}) \approx O(n)$

---

### `contains(F, set)` - Membership Test

```rust
if mgr.contains(f, &[Var::new(1), Var::new(3)]) {
    // F contains the set {1, 3}
}
```

Checks if a specific set is in the family.

**Implementation**: Navigate the ZDD following the variables in the set; reach ⊤ if found.

**Complexity**: $O(n)$ time, $O(1)$ space

---

### `count(F)` - Cardinality

```rust
let num_sets = mgr.count(f);
```

Returns the number of sets in family $F$.

**Implementation**: Sum counts from both branches; memoize.

**Complexity**: $O(|F|)$ time

---

### `node_count(F)` - ZDD Size

```rust
let size = mgr.node_count(f);
```

Returns the number of nodes in the ZDD (excluding terminals).

**Implementation**: DFS traversal with visited set.

**Complexity**: $O(|F|)$ time

---

## Iteration

### `iter_sets(F)` - Enumerate All Sets

```rust
for set_vec in mgr.iter_sets(f) {
    // set_vec is a Vec<Var>
    println!("Set: {:?}", set_vec);
}
```

Iterates over all sets in the family.

**Implementation**: DFS stack; build sets as we traverse.

**Complexity**: $O(|F| \times n)$ time (enumerate all sets, each size ≤ $n$)

---

## Performance Tips

1. **Cache operations**: ZDD operations are memoized automatically; reusing results is efficient.

2. **Variable ordering**: Choose ordering to exploit problem structure (e.g., spatial locality).

3. **Early filtering**: Apply constraints early to reduce intermediate ZDD sizes.

4. **Join over union**: Prefer `join` for combinatorial generation over building unions incrementally.

5. **Batch constraints**: Apply multiple `remove_sets_with_both` operations to filter conflicting configurations.

---

Next: [Implementation details →](implementation.md)
