# ananke-zdd

Zero-Suppressed Decision Diagrams (ZDDs) for Rust.

## Overview

ZDDs are a variant of BDDs optimized for representing **families of sets** (combinatorial sets). Unlike BDDs which eliminate nodes where `lo = hi`, ZDDs eliminate nodes where `hi = ⊥` (zero-suppression rule), making them highly efficient for sparse set families.

## Key Features

- **Manager-centric design**: All operations go through `ZddManager`
- **Set-theoretic API**: `union`, `intersection`, `difference`, `join`
- **Efficient sparse representation**: Zero-suppression rule eliminates absent elements
- **Rich operations**: `subset0/1`, `change`, `combinations`, `powerset`
- **Counting & enumeration**: Count sets, iterate all sets in a family

## Quick Start

```rust
use ananke_zdd::zdd::ZddManager;

let mut mgr = ZddManager::new();

// Create singleton sets
let x1 = mgr.base(1);  // {{1}}
let x2 = mgr.base(2);  // {{2}}

// Union: {{1}} ∪ {{2}} = {{1}, {2}}
let union = mgr.union(x1, x2);
assert_eq!(mgr.count(union), 2);

// Join (cross product): {{1}} ⊗ {{2}} = {{1, 2}}
let joined = mgr.join(x1, x2);
assert_eq!(mgr.count(joined), 1);

// All 2-element subsets of {1,2,3,4}
let c42 = mgr.combinations([1, 2, 3, 4], 2);
assert_eq!(mgr.count(c42), 6);  // C(4,2) = 6
```

## Semantics

| Terminal | Symbol | Meaning |
|----------|--------|---------|
| ZERO | ⊥ | Empty family (no sets) |
| ONE | ⊤ | Family containing only empty set: {∅} |

A ZDD node labeled with variable `x` has two children:

- **LO (0-edge)**: Sets that **do not** contain `x`
- **HI (1-edge)**: Sets **containing** `x`

The family represented by a ZDD node $v$ is defined recursively:
$$
    \text{Eval}(v) = \begin{cases}
        \emptyset & \text{if } v = \bot \\
        \{\emptyset\} & \text{if } v = \top \\
        \text{Eval}(\text{LO}(v)) \cup \{S \cup \{x_v\} \mid S \in \text{Eval}(\text{HI}(v))\} & \text{otherwise}
    \end{cases}
$$

## Operations

### Set-Theoretic

| Operation | Method | Description |
|-----------|--------|-------------|
| Union | `union(f, g)` | Sets in either family |
| Intersection | `intersection(f, g)` | Sets in both families |
| Difference | `difference(f, g)` | Sets in F but not G |
| Symmetric Diff | `symmetric_difference(f, g)` | Sets in exactly one |

### ZDD-Specific

| Operation | Method | Description |
|-----------|--------|-------------|
| Subset0 | `subset0(f, var)` | Sets NOT containing var |
| Subset1 | `subset1(f, var)` | Sets containing var (with var removed) |
| Change | `change(f, var)` | Toggle var in all sets |
| Join | `join(f, g)` | {S ∪ T \| S ∈ F, T ∈ G} |
| Meet | `meet(f, g)` | Non-empty intersections |

### Constructors

| Method | Description |
|--------|-------------|
| `base(var)` | Singleton family: {{var}} |
| `singleton(vars)` | Single set: {{v₁, v₂, ...}} |
| `powerset(vars)` | All subsets: 2^vars |
| `combinations(vars, k)` | All k-subsets: C(n,k) |

### Queries

| Method | Description |
|--------|-------------|
| `count(f)` | Number of sets in family |
| `contains(f, set)` | Check if set is in family |
| `contains_empty(f)` | Check if ∅ ∈ F |
| `iter_sets(f)` | Iterate all sets |
| `pick_one(f)` | Get one arbitrary set |

## Comparison with BDDs

| Aspect | BDD | ZDD |
|--------|-----|-----|
| Reduction rule | `lo = hi → lo` | `hi = ⊥ → lo` |
| Optimized for | Boolean functions | Set families |
| Negation | O(1) with complement edges | O(n) |
| Sparse data | Can be inefficient | Very compact |

## Examples

Run examples with:

```bash
cargo run --example simple -p ananke-zdd
cargo run --example combinations -p ananke-zdd
cargo run --example queens -p ananke-zdd --release
```

## Applications

- **Combinatorics**: Generating combinations, permutations
- **Graph problems**: Paths, matchings, independent sets
- **Data mining**: Frequent itemset mining
- **Fault tree analysis**: Minimal cut sets
- **Constraint satisfaction**: Solution enumeration

## References

1. S. Minato, "Zero-Suppressed BDDs for Set Manipulation in Combinatorial Problems," DAC 1993
2. D. Knuth, "The Art of Computer Programming, Volume 4A: Combinatorial Algorithms"
3. CUDD: CU Decision Diagram Package
