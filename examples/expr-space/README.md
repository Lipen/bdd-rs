# Symbolic Expression Space Exploration

Explore the entire space of Boolean expression trees at once — not one by one.

Instead of traditional program synthesis that enumerates millions of expressions individually, this tool builds a **single BDD that represents all possible trees** and manipulates them symbolically. Think of it as "bulk operations" on an exponential search space.

## Why This Matters

Naive enumeration is exponentially slow:

```python
for each AST in enumerate_all_trees(depth ≤ d):
    if semantics(AST) == target:
        return AST
```

For depth 2 with just 2 Boolean variables, there are **9,468 possible expression trees**, but only **16 distinct Boolean functions** they can represent. Most trees are redundant or structurally equivalent. Checking them one-by-one is wasteful.

## Our Approach

We represent all 9,468 trees as a **single BDD** — a compressed Boolean formula — then manipulate them in bulk:

1. **Symbolic construction** — Build the entire expression space as one compact BDD structure
2. **Bulk filtering** — Eliminate redundant forms all at once (commutativity, idempotence, constant folding, etc.)
3. **Semantic partitioning** — Group all trees by truth table (discovering all 16 Boolean functions automatically)
4. **Canonical extraction** — Find the minimal, most elegant representative of each function
5. **Node expansion analysis** — Understand the surprising BDD behavior when filtering

## Modules

- `encoding` — Position and NodeTag types, variable allocation
- `builder` — Recursive expression space construction via BDD operations
- `filters` — Commutativity, idempotence, no-double-negation, no-constant-ops
- `eval` — Symbolic semantic evaluation (truth tables, semantic partitioning)
- `ast` — AST reconstruction from BDD paths (path → Lit sequence → Expr)
- `main` — Canonical extraction via streaming TopK, flag-based analysis

## Getting Started

```bash
# From the expr-space example directory
cd examples/expr-space

# Explore depth ≤ 2 (fast, shows canonical forms)
cargo run --release -- --depth 2

# See how expressions group by truth table (16 Boolean functions)
cargo run --release -- --depth 2 --semantics

# Apply filters to remove redundant forms (commutativity, idempotence, etc.)
cargo run --release -- --depth 2 --filter

# See semantic counts AND filtered results together
cargo run --release -- --depth 2 --filter --semantics

# Show first 10 canonical forms per function (default is 5)
cargo run --release -- --depth 2 --semantics --samples 10

# Run the test suite
cargo test
```

## Real Results (Depth ≤ 2, Two Variables)

Here's what the tool discovers when exploring all 9,468 possible expression trees:

| Stage | Trees | BDD Nodes | Reduction | Key Insight |
|-------|-------|-----------|-----------|-------------|
| **Raw space** | 9,468 | 188 | — | Baseline: all possible trees |
| No double-negation | 9,464 | 181 | 0.04% | Barely eliminates anything |
| No constant ops | 786 | 165 | 91.7% | Huge jump: removes `0 ∧ x`, `1 ∨ x`, etc. |
| No idempotent | 442 | 266 | 95.3% | Removes `x ∧ x`, `x ∨ x` |
| **Final (all filters)** | 154 | 298 | **98.4%** | Only truly unique canonical forms |
| **Semantically unique** | 16 | — | — | The 16 Boolean functions |

### The BDD Paradox

Notice something surprising: filtering *reduces* trees by 98.4% but *increases* BDD nodes from 188 → 298. Why?

When you constrain the search space, you remove uniformity. The 9,468 raw trees share massive structural redundancy — many look similar, compress well. The 154 filtered trees are more *diverse* — fewer commonalities to compress. It's like this:

- **Raw space**: Many trees, very repetitive patterns → **small BDD**
- **Filtered space**: Few trees, diverse patterns → **larger BDD**

This is a key insight: filtering and compression don't always go hand-in-hand!

### Key Capabilities

- **Semantic Discovery**: Automatically partitions all trees into the 16 Boolean functions
- **Canonical Forms**: Finds the minimal, most elegant expression for each function (sorted by depth, size, negation)
- **Smart Filtering**: Removes commutativity (`(x ∧ y)` vs. `(y ∧ x)`), idempotence, constant folding
- **Memory Efficient**: Uses streaming TopK algorithm — never stores all forms in memory
