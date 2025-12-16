# Symbolic Expression Space Exploration

This example demonstrates using **BDDs to symbolically represent and manipulate the entire space of Boolean expression trees**.

## The Problem

Traditional program synthesis enumerates expressions one-by-one:

```
for each AST in enumerate_all_trees(depth ≤ d):
    if semantics(AST) == specification:
        return AST
```

This is exponentially slow — most trees are redundant (semantically or structurally).

## The Solution

Instead of enumeration, we represent **all possible trees** as a single BDD and perform:

1. **Symbolic construction** — Build entire expression space as a single BDD
2. **Bulk filtering** — Remove redundant forms symbolically (commutativity, idempotence, etc.)
3. **Semantic partitioning** — Group all 9,468 trees by their 16 Boolean functions
4. **Canonical extraction** — Find minimal representatives via streaming TopK algorithm
5. **Constraint analysis** — Understand why filtering paradoxically expands node count

## Modules

- `encoding` — Position and NodeTag types, variable allocation
- `builder` — Recursive expression space construction via BDD operations
- `filters` — Commutativity, idempotence, no-double-negation, no-constant-ops
- `eval` — Symbolic semantic evaluation (truth tables, semantic partitioning)
- `ast` — AST reconstruction from BDD paths (path → Lit sequence → Expr)
- `main` — Canonical extraction via streaming TopK, flag-based analysis

## Usage

```bash
# Basic exploration (depth ≤ 3)
cargo run -p expr-space --release

# With specific depth and canonical form extraction
cargo run -p expr-space --release -- --depth 2

# With semantic partitioning (tracks actual expression counts per truth table)
cargo run -p expr-space --release -- --depth 2 --semantics

# With filtering (removes commutativity, idempotence, constant ops)
cargo run -p expr-space --release -- --depth 2 --filter

# Combined: filter + semantics + show first 10 canonical forms per function
cargo run -p expr-space --release -- --depth 2 --filter --semantics --samples 10

# Run tests
cargo test -p expr-space
```

## Results

For a 2-variable Boolean language with depth ≤ 2:

| Stage | Tree Count | BDD Nodes | Example |
|-------|-----------|-----------|---------|
| Raw expression space | 9,468 | 188 | `(x ∧ y)`, `(y ∧ x)`, `((x ∧ y) ∨ 0)`, ... |
| After no-double-negation | 3,261 | 165 | −91.7% reduction |
| After no-constant-ops | 786 | 173 | −93.7% reduction |
| After no-idempotent | 412 | 298 | −97.1% reduction |
| After commutativity | 154 | 298 | −98.4% reduction |
| Semantically unique | 16 | — | `0`, `1`, `x`, `y`, `¬x`, `¬y`, `(x ∧ y)`, `(x ∨ y)`, ... |

**Key Features:**

- **Semantic Partitioning**: Automatically groups all trees by truth table (using `--semantics`)
- **Canonical Extraction**: Finds minimal representatives (depth, size, negation status)
- **Bulk Filtering**: Eliminates redundant forms symbolically (using `--filter`)
- **Streaming TopK**: Memory-efficient extraction of best N canonical forms per function
