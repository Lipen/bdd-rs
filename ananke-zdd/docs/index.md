# Zero-Suppressed Decision Diagrams (ZDDs) - Complete Guide

Welcome to the ananke-zdd documentation. This guide covers ZDDs from foundational theory to practical implementation and usage.

## Quick Navigation

- **[Introduction](introduction.md)** - What are ZDDs and why do we care?
- **[Quick Reference](quickref.md)** - Common tasks, code snippets, and cheat sheets
- **[Theory & Fundamentals](theory.md)** - Mathematical foundations and core concepts
- **[Operations](operations.md)** - Set operations and ZDD-specific algorithms
- **[Implementation](implementation.md)** - Architecture, data structures, and performance considerations
- **[Examples](examples.md)** - Practical patterns and use cases

## TL;DR

ZDDs are a compressed representation for families of sets. Unlike general data structures that require O(2^n) space for n-element sets, ZDDs exploit sparsity to represent only the families that actually appear in your problem. They're particularly powerful for:

- **Combinatorial enumeration** (all k-element subsets)
- **Set partitioning** (all valid partitions)
- **Constraint satisfaction** (after encoding into set families)
- **Graph problems** (paths, cuts, cliques)

The key insight: **the zero-suppression rule** eliminates redundant nodes that represent trivial set families, making ZDDs exponentially more compact than BDDs for sparse set families.

## Getting Started

```rust
use ananke_zdd::zdd::ZddManager;

let mgr = ZddManager::new();

// Create base sets
let x1 = mgr.base(1);     // {{1}}
let x2 = mgr.base(2);     // {{2}}

// Set operations
let union = mgr.union(x1, x2);      // {{1}, {2}}
let product = mgr.join(x1, x2);    // {{1, 2}}
let all_subsets = mgr.powerset([1, 2, 3]);  // 2^3 = 8 sets

// Queries
assert_eq!(mgr.count(union), 2);
assert_eq!(mgr.count(product), 1);
assert_eq!(mgr.count(all_subsets), 8);
```

---

Next: [Introduction to ZDDs →](introduction.md)
