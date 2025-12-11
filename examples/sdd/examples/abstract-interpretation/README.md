# SDD Abstract Interpretation

A case study in using **Sentential Decision Diagrams (SDDs)** as abstract states for program analysis.

## Overview

This example demonstrates how SDDs provide a structured, modular representation of abstract program states that automatically suggests decompositions for static analysis.

### Key Insight

**Abstract state = Boolean function over bit-encoded variable values**

Each concrete state (variable assignment) becomes a satisfying assignment to an SDD. The SDD's prime-sub decomposition naturally reveals:

- Independent state components
- Variable clustering opportunities
- Hierarchical program structure

## Problem Statement

### Traditional Abstract Domains

Classical domains (intervals, constants, polyhedra) are:

- **Efficient**: Simple operations, small memory
- **But Limited**: Lose correlation structure between variables
- **Opaque**: No insight into why abstractions work

### SDD-Based Domains

SDDs offer:

- **Structure**: Prime-sub decomposition shows independent factors
- **Precision**: Can represent arbitrary predicates compactly
- **Learnability**: VTree structure suggests good domain decomposition
- **Compositionality**: Natural operations align with program structure

## Mini-Language

Variables with domain 0–7 (3-bit encoding):

```
Expr ::= Var(x | y | z | ...)
       | Const(0 | 1 | ... | 7)
       | Expr + Expr
       | Expr * Expr
       | -Expr

Predicate ::= Expr < Expr
            | Expr <= Expr
            | Expr == Expr
            | Expr != Expr
            | Pred && Pred
            | Pred || Pred
            | !Pred

Stmt ::= Var := Expr
       | if Pred { Stmt* } else { Stmt* }
       | assume Pred
       | assert Pred
```

## Architecture

```
lib.rs                      Main library interface
├── language.rs              Mini-language AST
├── cfg.rs                   CFG compilation
├── bit_encoding.rs          Variable → SDD variable mapping
├── sdd_domain.rs            Abstract state (SDD wrapper)
├── interpreter.rs           Main abstract interpreter
├── vtree_strategy.rs        VTree strategy selection
├── analysis.rs              Domain comparison framework
└── classical_domains/
    ├── interval_domain.rs   Interval abstraction
    └── bitset_domain.rs     Exact bitset abstraction
```

## Abstract Interpreter

### Design

1. **Control Flow Graph**: Program → CFG with labeled edges
2. **Worklist Algorithm**: Forward dataflow analysis
3. **State Lattice**: Abstract states ordered by SDD inclusion
4. **Join/Meet**: SDD disjunction (union) and conjunction (intersection)

### Key Operations

| Operation | Semantics |
|-----------|-----------|
| `assign(v := e)` | Restrict SDD to new variable value |
| `assume(pred)` | Intersect SDD with predicate formula |
| `join(s1, s2)` | Merge states via disjunction (widening candidate) |
| `meet(s1, s2)` | Combine constraints via conjunction |
| `assert(pred)` | Verify all states satisfy predicate |

### Example: `x := x + 1`

```
Before: SDD representing {(x,y) | ...possible...}
       ↓
After:  SDD representing {(x,y) | x' = x+1 (mod 8), y unchanged...}
```

## VTree Strategies

Compare 5 different decomposition approaches:

### 1. **Balanced** (Default)

Symmetric binary tree — general-purpose, good for symmetric formulas.

```
       (root)
       /    \
      /      \
    (L)      (R)
    / \      / \
   x1  x2  x3  x4
```

### 2. **Right-Linear**

Left-skewed tree — forces variable ordering dependency.

```
        (root)
        /    \
       x1    ( )
            /   \
           x2   ( )
               /   \
              x3   x4
```

### 3. **Left-Linear**

Right-skewed tree — opposite ordering.

```
       ( )
       /  \
      ( )  x4
      / \
     x1  x2
```

### 4. **Syntactic**

Based on variable appearance order in source program.

### 5. **Semantic**

Groups variables appearing together in predicates (heuristic clustering).

## Building & Running

### Build

```bash
cd examples/abstract-interpretation
cargo build --release
```

### Run Simple Example

```bash
cargo run --example simple --release
```

### Run All Examples

```bash
cargo run --example simple --release
cargo run --example conditional --release
cargo run --example comparison --release
```

## Example Programs

### Example 1: Simple Counter

```
x := 0
x := x + 1
assert x < 7
```

**Analysis:**

- Initial state: top (all values 0–7)
- After `x := 0`: singleton {0}
- After `x := 1`: singleton {1}
- Assertion: x ∈ {1} ⊆ {0..6} ✓ Safe

### Example 2: Conditional Merge

```
x := 0
y := 5
if x < y { x := 1 } else { x := 0 }
assert x <= 1
```

**Analysis:**

- After conditional: x ∈ {0, 1}
- y unchanged at {5}
- Assertion: {0,1} ⊆ {0..1} ✓ Safe

### Example 3: Potential Violation

```
x := 0
y := 0
assert x == 0
x := 7
assert x < 7  // May fail!
```

## Research Questions

### A. VTree Inference

**Can we automatically learn good VTrees from program structure?**

- Parse program into dependency DAG
- Use hierarchical clustering on variable dependencies
- Compare learned VTree to hand-tuned strategies

### B. Dynamic VTree Optimization

**Can we adapt VTree during analysis for efficiency?**

- Monitor SDD size at each node
- When size > threshold, restructure VTree locally
- Rememoization with new decomposition

### C. Explainable Abstract Interpretation

**Does SDD decomposition explain why abstraction works?**

- Extract minimal "certificates" from SDD primes
- Show which variable clusters are independent
- Generate human-readable abstraction justifications

### D. Precision vs. Cost Trade-offs

**When does SDD-domain beat classical domains?**

- Benchmark on 20+ programs
- Compare: max state size, join operations, assertion checks
- Identify program classes where SDDs excel

## Output Example

```
📊 Abstract Interpretation Results
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
VTree Strategy: Balanced
Initial state size: 1
Final state size: 1
Max state size: 2
Total states computed: 5

✓ Safe assertions:
  • Assert x < 7 at node 3
  • Assert x <= 1 at node 7

✓ All assertions are safe!
```

## Comparison with Classical Domains

### Interval Domain

- **Precision**: Low (x ∈ [0,1])
- **Cost**: O(1) per operation
- **Good for**: Simple bounds, overflow detection

### Bitset Domain

- **Precision**: High (x ∈ {0,1,3,5})
- **Cost**: O(|values|) per operation
- **Good for**: Exact value tracking, small domains

### SDD Domain

- **Precision**: High (respects correlations)
- **Cost**: O(SDD size) — varies
- **Good for**: Discovering decompositions, explaining abstractions

## References

### SDD Papers

- Darwiche (2011). "SDD: A New Canonical Representation of Propositional Knowledge Bases." IJCAI-11.
- Choi & Darwiche (2013). "Dynamic Minimization of Sentential Decision Diagrams." AAAI-13.

### Abstract Interpretation

- Cousot & Cousot (1977). "Abstract Interpretation: A Unified Lattice Model..." POPL-77.
- Rival & Yi (2016). "Introduction to Static Analysis." MIT Press.

### Related Work

- Symbolic model checking with BDDs (Clarke, Grumberg, Peled)
- Decision diagram applications (Wegener, Becker)

## Future Extensions

- [ ] Real SDD integration (wrap libsdd)
- [ ] Recursive procedure analysis (call graphs)
- [ ] Data structure abstractions (arrays, heap)
- [ ] VTree learning from programs
- [ ] Benchmark suite with 50+ programs
- [ ] Visualization (Graphviz export)
- [ ] Web UI for interactive analysis

## License

MIT — see parent LICENSE file
