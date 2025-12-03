# Sentential Decision Diagrams (SDDs)

A Rust implementation of **Sentential Decision Diagrams** — a tractable, canonical representation of propositional knowledge bases.

## Overview

SDDs are a powerful generalization of Binary Decision Diagrams (BDDs) introduced by Adnan Darwiche in 2011. They provide:

- **Canonicity**: For a fixed vtree, each Boolean function has exactly one SDD
- **Tractability**: Polynomial-time conjunction, disjunction, negation, and model counting
- **Succinctness**: Can be exponentially more compact than BDDs for certain functions
- **Flexibility**: Vtree structure can be optimized for specific formulas

## Quick Start

```rust
use sdd::SddManager;

// Create manager with 4 variables
let mgr = SddManager::new(4);

// Create variables (1-indexed)
let x1 = mgr.var(1);
let x2 = mgr.var(2);

// Boolean operations
let f = mgr.and(x1, x2);           // x₁ ∧ x₂
let g = mgr.or(x1, mgr.neg(x2));   // x₁ ∨ ¬x₂

// Check properties
assert!(mgr.is_satisfiable(f));
assert!(!mgr.is_valid(f));         // Not a tautology

// Count satisfying assignments
let count = mgr.model_count(f);
println!("Models: {}", count);     // 4 models for x₁ ∧ x₂ over 4 vars
```

## Features

### Core Operations

| Operation | Description | Complexity |
|-----------|-------------|------------|
| `and(f, g)` | Conjunction | O(\|f\| × \|g\|) |
| `or(f, g)` | Disjunction | O(\|f\| × \|g\|) |
| `neg(f)` | Negation | O(1) |
| `xor(f, g)` | Exclusive OR | O(\|f\| × \|g\|) |
| `implies(f, g)` | Implication | O(\|f\| × \|g\|) |
| `equiv(f, g)` | Equivalence | O(\|f\| × \|g\|) |
| `ite(c, t, e)` | If-then-else | O(\|c\| × \|t\| × \|e\|) |

### Queries

| Query | Description | Complexity |
|-------|-------------|------------|
| `is_false(f)` | Check if f ≡ ⊥ | O(1) |
| `is_true(f)` | Check if f ≡ ⊤ | O(1) |
| `is_satisfiable(f)` | Check if f is SAT | O(1) |
| `model_count(f)` | Count SAT assignments | O(\|f\|) |
| `any_sat(f)` | Get one SAT assignment | O(\|f\|) |
| `size(f)` | Count nodes | O(\|f\|) |

### Transformations

| Transform | Description | Complexity |
|-----------|-------------|------------|
| `condition(f, lit)` | Restrict by literal | O(\|f\|) |
| `exists(f, var)` | Existential quantification | O(\|f\|²) |
| `forall(f, var)` | Universal quantification | O(\|f\|²) |

## Vtree Structures

The vtree determines SDD decomposition. Three built-in strategies:

### Balanced Vtree (default)

```rust
let mgr = SddManager::new(4);  // Balanced vtree
```

```
       (root)
       /    \
      /      \
    (L)      (R)
    / \      / \
   x₁  x₂  x₃  x₄
```

Best for: Symmetric formulas, general use.

### Right-Linear Vtree

```rust
let mgr = SddManager::with_right_linear_vtree(4);
```

```
        (root)
        /    \
       x₁    ( )
            /   \
           x₂   ( )
               /   \
              x₃   x₄
```

Best for: When variable ordering is known (similar to BDDs).

### Left-Linear Vtree

```rust
let mgr = SddManager::with_left_linear_vtree(4);
```

Best for: Opposite ordering preference.

## Project Structure

```
examples/sdd/
├── Cargo.toml
├── README.md                   # This file
├── examples/
│   ├── simple.rs               # Comprehensive SDD tour
│   ├── vtree.rs                # Vtree structures and impact
│   ├── knowledge_compilation.rs  # Knowledge base queries
│   ├── probabilistic.rs        # Weighted model counting
│   ├── sdd_vs_bdd.rs           # When SDDs beat BDDs
│   ├── queens.rs               # N-Queens constraint solving
│   ├── circuit_analysis.rs     # Digital circuit verification
│   └── file_io.rs              # Save/load in libsdd format
└── src/
    ├── lib.rs                  # Public API
    ├── literal.rs              # Boolean literals
    ├── vtree.rs                # Variable tree
    ├── sdd.rs                  # SDD nodes
    ├── manager.rs              # SDD manager
    ├── dot.rs                  # Graphviz export
    └── io.rs                   # File I/O (libsdd format)
```

## Examples

### Overview

| Example | Description |
|---------|-------------|
| `simple` | Comprehensive tour of all SDD operations |
| `vtree` | Vtree types, structure, and size impact |
| `knowledge_compilation` | Entailment, consistency, abstraction |
| `probabilistic` | Bayesian inference via weighted model counting |
| `sdd_vs_bdd` | When SDDs are exponentially smaller |
| `queens` | N-Queens puzzle constraint solving |
| `circuit_analysis` | Digital circuit verification and fault detection |
| `file_io` | Save/load in libsdd-compatible format |

### Run Examples

```bash
cd examples/sdd

# Comprehensive tour of all operations
cargo run --example simple

# Vtree structures and their impact
cargo run --example vtree

# Knowledge compilation for query answering
cargo run --example knowledge_compilation

# Probabilistic inference with WMC
cargo run --example probabilistic

# SDD vs BDD comparison
cargo run --example sdd_vs_bdd

# N-Queens puzzle (with options)
cargo run --example queens             # 4×4 board
cargo run --example queens -- -n 5     # 5×5 board
cargo run --example queens -- --show-all  # Show all solutions

# Digital circuit analysis
cargo run --example circuit_analysis

# File I/O demonstration
cargo run --example file_io
```

### Run Tests

```bash
cargo test
```

## Application Areas

1. **Knowledge Compilation**: Compile constraints once, query efficiently many times
2. **Probabilistic Inference**: Weighted model counting for Bayesian networks
3. **Configuration Management**: Valid product configurations
4. **Machine Learning**: Tractable probabilistic models
5. **Verification**: Symbolic model checking

## File I/O

SDDs and Vtrees can be saved/loaded in libsdd-compatible format:

```rust
use sdd::{SddManager, vtree::Vtree};

// Create and compile
let mgr = SddManager::new(4);
let f = mgr.and(mgr.var(1), mgr.var(2));

// Save to files
mgr.save_sdd(f, "formula.sdd").unwrap();
mgr.vtree().save("formula.vtree").unwrap();

// Load into new manager
let vtree = Vtree::load("formula.vtree").unwrap();
let mgr2 = SddManager::with_vtree(vtree);
let f2 = mgr2.load_sdd("formula.sdd").unwrap();
```

Files are compatible with UCLA's libsdd for interoperability.

## Comparison with BDDs

| Aspect | BDD | SDD |
|--------|-----|-----|
| Decomposition | Shannon (if-then-else) | (prime, sub) pairs |
| Variable structure | Linear ordering | Binary tree (vtree) |
| Canonicity | Per variable order | Per vtree |
| Succinctness | — | ≥ BDD (never larger) |
| Implementation | Simpler | More complex |

Key insight: **Every BDD is also an SDD** (with a right-linear vtree), but SDDs can be exponentially more compact for hierarchically structured formulas.

## Performance Tips

1. **Use `--release`**: Debug mode is significantly slower
2. **Choose vtree wisely**: Vtree structure greatly affects size
3. **Reuse managers**: Creating new managers is expensive
4. **Clear caches**: Call `clear_caches()` if memory is a concern

## References

### Original Papers

1. **Darwiche, A. (2011)**. SDD: A New Canonical Representation of Propositional Knowledge Bases. *IJCAI-11*, 819-826.

2. **Darwiche, A. & Marquis, P. (2002)**. A Knowledge Compilation Map. *JAIR*, 17, 229-264.

3. **Choi, A. & Darwiche, A. (2013)**. Dynamic Minimization of Sentential Decision Diagrams. *AAAI-13*, 187-194.

### Related Resources

- [SDD Package (UCLA)](http://reasoning.cs.ucla.edu/sdd/) — Reference C implementation
- [PySDD](https://github.com/wannesm/PySDD) — Python bindings
- [Knowledge Compilation Map](http://www.cril.univ-artois.fr/KC/) — Survey of representations

## License

MIT License — see [LICENSE](../../LICENSE)
