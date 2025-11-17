# BDD-Guided Abstract Interpretation

A Rust implementation of abstract interpretation with BDD-based control state representation.

## Overview

This package implements a modular abstract interpretation framework combining:

- **Numeric abstract domains**: Sign, Constant, Interval
- **Pointer analysis domain**: BDD-based Points-to Analysis
- **Product domains** for compositional analysis
- **Fixpoint engines** with widening/narrowing

## Available Domains

### Numeric Domains

1. **Sign Domain** (`sign.rs`)
   - Tracks sign information: Neg, Zero, Pos, NonNeg, NonPos, Top, Bottom
   - Fast and lightweight
   - Useful for detecting sign errors and division by zero

2. **Constant Propagation** (`constant.rs`)
   - Tracks exact constant values
   - Identifies dead code and optimization opportunities
   - Constant folding at analysis time

3. **Interval Domain** (`interval.rs`)
   - Tracks value ranges [low, high] with ±∞ bounds
   - More precise than signs, captures numeric relationships
   - 500+ lines with complete arithmetic

### Pointer Analysis Domain

4. **Points-to Analysis** (`pointsto.rs`)
   - BDD-based representation of pointer targets
   - Tracks aliasing relationships (must-alias, may-alias)
   - Supports heap allocation, strong/weak updates
   - Flow-insensitive Andersen-style analysis

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

# Sign domain analysis
cargo run --bin sign_analysis

# Constant propagation
cargo run --bin constant_propagation

# Combined domain analysis
cargo run --bin combined_analysis

# Points-to analysis
cargo run --example pointsto_example

# Realistic program analysis (all domains)
cargo run --example realistic_programs
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
- **`sign.rs`**: Sign domain (Neg/Zero/Pos/NonNeg/NonPos/Top/Bottom)
- **`constant.rs`**: Constant propagation domain (Bottom/Const(n)/Top)
- **`interval.rs`**: Interval domain [low, high] with ±∞ (500+ lines)
- **`pointsto.rs`**: BDD-based pointer analysis (~1500 lines)
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

### ✅ Phase 1: Constant Propagation Domain (Complete)

- [x] ConstValue enum (Bottom, Const(i64), Top)
- [x] AbstractDomain implementation with lattice operations
- [x] NumericDomain implementation with expression evaluation
- [x] Arithmetic operations with constant folding
- [x] 62 unit tests covering all operations
- [x] Integration with other domains

### ✅ Phase 2: Points-to Analysis Domain (Complete)

- [x] Location types (Null, Stack, Heap, Global, Unknown)
- [x] BDD-based points-to set representation
- [x] AbstractDomain implementation
- [x] Pointer operations (assign_null, assign_address, assign_copy, assign_alloc)
- [x] Load/store operations (assign_load, assign_store)
- [x] Alias analysis (must_alias, may_alias)
- [x] 17 comprehensive tests
- [x] Full documentation with theory background

### ✅ Phase 3: Sign Domain (Complete)

- [x] Sign enum (Bottom, Neg, Zero, Pos, NonNeg, NonPos, Top)
- [x] AbstractDomain and NumericDomain implementations
- [x] Arithmetic operations with sign propagation
- [x] Comparison operations
- [x] Integration tests
- [x] Complete documentation

### ✅ Phase 4: Integration & Testing (Complete)

- [x] Product domain compositions (Sign × Constant, Sign × Interval, etc.)
- [x] 10 integration tests showing multi-domain cooperation
- [x] Realistic program examples (array bounds, constant propagation, pointer aliasing)
- [x] Combined analysis demonstrations
- [x] 88+ tests passing (79 unit + 10 integration)

## Usage Examples

### Sign Analysis

```rust
use abstract_interpretation::*;

let domain = SignDomain;

// x = -5
let state = domain.constant(&"x".to_string(), -5);
assert_eq!(state.get("x"), Sign::Neg);

// y = x + 10
let expr = NumExpr::Add(
    Box::new(NumExpr::Var("x".to_string())),
    Box::new(NumExpr::Const(10))
);
let state = domain.assign(&state, &"y".to_string(), &expr);
assert_eq!(state.get("y"), Sign::NonNeg);  // Could be positive or zero
```

### Constant Propagation

```rust
let domain = ConstantDomain;

// x = 7; y = x + 3; z = y * 2;
let state = domain.constant(&"x".to_string(), 7);
let state = domain.assign(&state, &"y".to_string(),
    &NumExpr::Add(Box::new(NumExpr::Var("x".to_string())), Box::new(NumExpr::Const(3))));
let state = domain.assign(&state, &"z".to_string(),
    &NumExpr::Mul(Box::new(NumExpr::Var("y".to_string())), Box::new(NumExpr::Const(2))));

assert_eq!(state.get("z"), ConstValue::Const(20));  // Exact value!
```

### Interval Analysis

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

### Points-to Analysis

```rust
use abstract_interpretation::*;
use std::rc::Rc;

let domain = PointsToDomain::new();
let mut state = PointsToElement::new(Rc::clone(domain.manager()));

// p = &x; q = &y;
state = domain.assign_address(&state, "p", &Location::Stack("x".to_string()));
state = domain.assign_address(&state, "q", &Location::Stack("y".to_string()));

// Check aliasing
assert!(!state.must_alias(&domain, "p", "q"));  // Different targets
assert!(!state.may_alias(&domain, "p", "q"));   // No overlap

// p = q;
state = domain.assign_copy(&state, "p", "q");
assert!(state.must_alias(&domain, "p", "q"));   // Now they alias!
```

### Combined Multi-Domain Analysis

```rust
// Use Sign, Constant, and Interval together for maximum precision
let sign_domain = SignDomain;
let const_domain = ConstantDomain;
let interval_domain = IntervalDomain;

// All domains track x = 5
let sign_state = sign_domain.constant(&"x".to_string(), 5);
let const_state = const_domain.constant(&"x".to_string(), 5);
let interval_state = interval_domain.constant(&"x".to_string(), 5);

// Sign: x is positive
// Constant: x is exactly 5
// Interval: x ∈ [5, 5]
// → Combined analysis gives most precise information
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

- **79 unit tests** across all domains:
  - Sign domain: 17 tests (lattice, arithmetic, comparisons)
  - Constant domain: 15 tests (lattice, propagation, arithmetic)
  - Interval domain: 20+ tests (bounds, operations, widening)
  - Points-to domain: 17 tests (pointer ops, aliasing, BDD integration)
  - Transfer functions, fixpoint engine
- **10 integration tests** (domain cooperation, reduced products)
- **2 doc tests**

Run specific domain tests:

```bash
cargo test sign::tests
cargo test constant::tests
cargo test interval::tests
cargo test pointsto::tests
cargo test --test domain_integration
```

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
