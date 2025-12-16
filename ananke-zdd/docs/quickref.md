# Quick Reference

## Common Tasks

### Create Families

```rust
let x = mgr.base(1);                    // {{1}}
let s = mgr.singleton([1, 2]);          // {{1,2}}
let p = mgr.powerset([1, 2, 3]);        // All 8 subsets
let c = mgr.combinations([1..5], 3);    // All 3-element subsets
```

### Set Operations

```rust
let u = mgr.union(f, g);                // F ∪ G
let i = mgr.intersection(f, g);         // F ∩ G
let d = mgr.difference(f, g);           // F \ G
let s = mgr.symmetric_difference(f, g); // F △ G
let j = mgr.join(f, g);                 // {S ∪ T | S∈F, T∈G}
let m = mgr.meet(f, g);                 // Non-empty intersections
```

### Filter & Extract

```rust
let s0 = mgr.subset0(f, v);             // Sets without v
let s1 = mgr.subset1(f, v);             // Sets with v (v removed)
let on = mgr.onset(f, v);               // Sets with v (v kept)
let c = mgr.change(f, v);               // Toggle v in all sets
```

### Add/Remove Elements

```rust
let f2 = mgr.add_element_to_all(f, v);                // Add v to all
let f2 = mgr.remove_sets_with_both(f, v1, v2);       // Remove those with both
```

### Query

```rust
let count = mgr.count(f);               // # of sets
let has_empty = mgr.contains_empty(f);  // Contains ∅?
let has_set = mgr.contains(f, &[v1, v2]); // Contains {v1,v2}?
let size = mgr.node_count(f);           // # of ZDD nodes

for set in mgr.iter_sets(f) {           // Iterate all sets
    println!("{:?}", set);
}
```

---

## ZDD Semantics Cheat Sheet

### Terminals

```
⊥ = ZERO = empty family (no sets)
⊤ = ONE  = family with only ∅
```

### Node Semantics

```
Node(v, lo, hi) represents:
  - lo: all sets NOT containing v
  - hi: all sets containing v

Path to ⊤: represents one set (collect all "hi" variables)
Path to ⊥: invalid (not in family)
```

### Zero-Suppression Rule

```
If hi = ⊥: eliminate node, use lo instead
Intuition: no sets contain this variable, so decision is useless
```

---

## Variable Ordering Tips

**Good**:

- Group by spatial locality (rows, then columns)
- Related variables adjacent
- Minimize problem depth

**Bad**:

- Random ordering
- Widely scattered related variables
- Artificial problem inflation

---

## Performance Checklist

- [ ] Use `new_var()` once per variable (not repeatedly)
- [ ] Reuse ZDD results via caching (don't rebuild)
- [ ] Filter constraints early (before join/union)
- [ ] Choose good variable ordering
- [ ] Use `join` instead of repeated unions for combinatorics

---

## Common Formulas

```
All k-subsets: mgr.combinations(vars, k)
Power set:     mgr.powerset(vars)
All but set:   mgr.difference(mgr.powerset(all), single_set)
With v, no u:  mgr.intersection(mgr.onset(f, v), mgr.offset(f, u))
```

---

## Error Handling

ZDDs are infallible:

- Operations always succeed
- No panics (except for OOM)
- Worst case: exponential-size ZDD

**Debugging**:

```rust
println!("Family has {} sets", mgr.count(f));
println!("ZDD uses {} nodes", mgr.node_count(f));
for set in mgr.iter_sets(f).take(10) {
    println!("  {:?}", set);
}
```

---

## Complexity Summary

| Op | Time | Space | Notes |
|----|------|-------|-------|
| base | O(1) | O(1) | |
| union | O(\|F\|×\|G\|) | O(\|F\|×\|G\|) | Memoized |
| join | O(\|F\|×\|G\|) | O(\|F\|×\|G\|) | More complex |
| subset1 | O(\|F\|) | O(\|F\|) | Single descent |
| count | O(\|F\|) | O(1) | Linear pass |
| contains | O(n) | O(1) | Path lookup |
| iterate | O(n+m) | O(n) | n=vars, m=sets |

---

## API Stability

Stable public API:

- ZddManager constructor, operations, queries
- Var, ZddId types
- Manager lifetimes

Subject to change:

- Internal node representation
- Cache structure
- Subtable implementation

---

## Further Reading

- **[Introduction](introduction.md)** - Conceptual overview
- **[Theory](theory.md)** - Mathematical foundations
- **[Operations](operations.md)** - Detailed operation semantics
- **[Implementation](implementation.md)** - Architecture deep-dive
- **[Examples](examples.md)** - Real usage patterns

---

Last updated: 2025-12-16
