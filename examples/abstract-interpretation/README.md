# BDD-Guided Abstract Interpretation

A Rust implementation of abstract interpretation with BDD-based control state representation.

## Overview

This package implements a modular abstract interpretation framework combining:

- **Numeric abstract domains** (intervals, octagons, polyhedra)
- **Product domains** for compositional analysis
- **Fixpoint engines** with widening/narrowing
- **BDD integration** (planned) for path-sensitive control analysis

## Quick Start

### Build and Test

```bash
cargo build
cargo test
```

### Run Examples

```bash
# Simple loop analysis with fixpoints
cargo run --bin simple_loops

# Transfer function demonstrations
cargo run --bin transfer_example
```

## Examples

### Simple Loops (`simple_loops.rs`)

Demonstrates fixpoint computation with interval domain:

1. **Counter loop**: `while x < 10 { x = x + 1 }`
   Shows convergence with widening

2. **Countdown**: `while x > 0 { x = x - 1 }`
   Reverse iteration pattern

3. **Unbounded loop**: `while true { x = x + 1 }`
   Widening extrapolates to [0, +∞]

### Transfer Functions (`transfer_example.rs`)

Statement-by-statement analysis:

1. **Sequential assignments**: Dataflow through variables
2. **Conditional branches**: Path-sensitive refinement
3. **Nested conditionals**: Complex control flow
4. **Assertions/Assumptions**: Contract refinement

## Architecture

### Core Traits

```rust
pub trait AbstractDomain {
    type Element: Clone;

    // Lattice operations
    fn join(&self, a: &Element, b: &Element) -> Element;     // ⊔
    fn meet(&self, a: &Element, b: &Element) -> Element;     // ⊓
    fn widen(&self, a: &Element, b: &Element) -> Element;    // ∇
    fn narrow(&self, a: &Element, b: &Element) -> Element;   // ∆

    // Tests
    fn is_bottom(&self, elem: &Element) -> bool;
    fn is_top(&self, elem: &Element) -> bool;
    fn is_less_or_equal(&self, a: &Element, b: &Element) -> bool;
}

pub trait NumericDomain: AbstractDomain {
    type Var: Clone;
    type Value: Clone;

    fn assign(&self, elem: &Element, var: &Var, expr: &NumExpr<Var, Value>) -> Element;
    fn assume(&self, elem: &Element, pred: &NumPred<Var, Value>) -> Element;
    fn project(&self, elem: &Element, var: &Var) -> Element;
}
```

### Module Structure

- **`domain.rs`**: `AbstractDomain` trait with lattice operations
- **`numeric.rs`**: `NumericDomain` trait for numeric analysis
- **`interval.rs`**: Complete interval domain [low, high] (500+ lines)
- **`product.rs`**: Product domain D₁ × D₂ for composition
- **`fixpoint.rs`**: Fixpoint engine with widening/narrowing
- **`transfer.rs`**: Transfer functions for abstract semantics
- **`expr.rs`**: AST types (NumExpr, NumPred, Stmt)

### Interval Domain Features

- **Bounds**: -∞, finite values, +∞
- **Operations**: join (hull), meet (intersection), widening, narrowing
- **Expression evaluation**: arithmetic with interval arithmetic
- **Predicate refinement**: assume() for path sensitivity

### Fixpoint Engine

```rust
pub struct FixpointEngine<D: AbstractDomain> {
    pub domain: D,
    pub widening_threshold: usize,      // Default: 3
    pub narrowing_iterations: usize,    // Default: 2
    pub max_iterations: usize,          // Default: 100
}
```

- **LFP**: Least fixpoint with widening (loops, reachability)
- **GFP**: Greatest fixpoint with narrowing (co-reachability)
- **Convergence**: Automatic detection with iteration limits

## Implementation Status

### ✅ Phase 1-2: Core Infrastructure (Complete)

- [x] AbstractDomain and NumericDomain traits
- [x] Interval domain with ±∞ bounds
- [x] Product domain for composition
- [x] Transfer functions (assign, assume, seq, if)
- [x] Fixpoint engine (lfp, gfp)
- [x] Example programs (simple_loops, transfer_example)
- [x] Unit tests (interval ops, transfer, fixpoint)

### 🚧 Phase 3: BDD Integration (Next)

- [ ] BddDomain wrapper around bdd-rs
- [ ] Full product: BDD(control) × Interval(data)
- [ ] Path-sensitive examples
- [ ] Integration tests

### 📋 Phase 4: Advanced Features (Planned)

- [ ] Octagon domain (relational: x±y ≤ c)
- [ ] Polyhedra domain (linear: ∑aᵢxᵢ ≤ c)
- [ ] Reduced product with refinement
- [ ] SMT solver integration

## Usage Example

```rust
use abstract_interpretation::*;

let domain = IntervalDomain;
let engine = FixpointEngine {
    domain: domain.clone(),
    widening_threshold: 3,
    narrowing_iterations: 2,
    max_iterations: 100,
};

// Initial: x = 0
let init = {
    let mut elem = IntervalElement::new();
    elem.set("x".to_string(), Interval::constant(0));
    elem
};

// Loop: x = x + 1; assume x < 10
let f = |elem: &IntervalElement| {
    // ... transfer function ...
};

let result = engine.lfp(init, f);
println!("x ∈ {}", result.get("x"));
```

## Testing

```bash
# Run all tests
cargo test

# Run specific test
cargo test test_interval_operations

# With output
cargo test -- --nocapture
```

Current tests:

- `interval::tests::test_interval_operations`
- `interval::tests::test_interval_domain`
- `transfer::tests::test_assignment`
- `transfer::tests::test_conditional`
- `fixpoint::tests::test_simple_fixpoint`

## Documentation

Comprehensive docs in `docs/`:

- **`theory.md`**: Abstract interpretation fundamentals, lattice theory, widening/narrowing
- **`architecture.md`**: System design, trait hierarchy, implementation patterns
- **`implementation.md`**: Phase-by-phase development guide with code examples
- **`benchmarks.md`**: 25+ benchmark programs, evaluation metrics
- **`examples.md`**: Tutorials, state machines, real-world applications
- **`PLAN.md`**: 4-month research roadmap, milestones, publication strategy

Start with `docs/PLAN.md` for project overview.

## Performance

Fixpoint iterations typically converge in < 10 iterations with widening:

- **Counter loop (0→10)**: 3 iterations
- **Countdown (100→0)**: 3 iterations
- **Unbounded loop**: 3 iterations (widening to ∞)

## Dependencies

```toml
[dependencies]
bdd-rs = { path = "../.." }
log = "0.4"
num-traits = "0.2"
simplelog = "0.12"
```

## References

- **Cousot & Cousot (1977)**: Abstract Interpretation: A Unified Lattice Model
- **Miné (2006)**: The Octagon Abstract Domain
- **Blanchet et al. (2003)**: A Static Analyzer for Large Safety-Critical Software (Astrée)
- **Beyer & Keremoglu (2011)**: CPAchecker: A Tool for Configurable Software Verification

## License

MIT License - see LICENSE file for details.
