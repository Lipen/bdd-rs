# BDD-Guided Abstract Interpretation

A comprehensive Rust implementation of abstract interpretation combined with Binary Decision Diagrams (BDDs) for precise program analysis and verification.

## Overview

This project implements a modular framework for **static program analysis** that combines:

- **Abstract interpretation**: Sound over-approximation of program behaviors
- **BDD-based control representation**: Path-sensitive analysis with efficient symbolic state management
- **Multiple abstract domains**: Numeric, pointer, string, automata, and type domains
- **Domain composition**: Product domains and reduced products for multi-dimensional analysis
- **Fixpoint computation**: Automated analysis with widening/narrowing operators

The implementation demonstrates how BDDs enable **path-sensitive abstract interpretation** by maintaining separate abstract states for different control paths, dramatically improving precision while remaining scalable.

## What's Included

### Abstract Domains

**Numeric Domains:**

- **Sign Domain** (`sign.rs`): Tracks sign information (`Neg`, `Zero`, `Pos`, `NonNeg`, `NonPos`, `Top`, `Bottom`)
- **Constant Domain** (`constant.rs`): Propagates constant values for optimization and dead code detection
- **Interval Domain** (`interval.rs`): Tracks value ranges [low, high] with ±∞ bounds (500+ lines)
- **Congruence Domain** (`congruence.rs`): Tracks modular arithmetic properties (e.g., "divisible by 4")

**Pointer Analysis:**

- **Points-to Domain** (`pointsto.rs`): BDD-based representation of pointer targets with must/may aliasing (~1500 lines)

**String Analysis:**

- **String Domain** (`string_domain.rs`): Tracks string lengths, prefixes, suffixes, and character sets
- **Automata Domain** (`automata.rs`): Regular expression matching and string constraints

**Control & Type Domains:**

- **BDD Control Domain** (`bdd_control.rs`): Path-sensitive control state representation
- **Type Domain** (`type_domain.rs`): Tracks dynamic types for type safety analysis

**Domain Combinators:**

- **Product Domain** (`product.rs`): Combines domains independently (D₁ × D₂)
- **Reduced Product** (`generic_product.rs`): Domains that refine each other (e.g., Sign × Interval)

### Analysis Infrastructure

- **Fixpoint Engine** (`fixpoint.rs`): Automated least/greatest fixpoint computation with widening/narrowing
- **Transfer Functions** (`transfer.rs`): Abstract semantics for statements and expressions
- **Expression AST** (`expr.rs`): Typed representation of numeric/boolean expressions and predicates

### Comprehensive Examples

The `examples/` directory contains 20 detailed demonstrations:

**Basic Domain Analysis:**

- `sign_analysis.rs`: Sign domain operations and arithmetic
- `constant_propagation.rs`: Constant folding and dead code detection
- `combined_analysis.rs`: Multi-domain cooperation (Sign × Constant × Interval)

**Fixpoint & Loops:**

- `simple_loops.rs`: Fixpoint computation with widening (counter, countdown, unbounded loops)
- `transfer_example.rs`: Statement-by-statement dataflow analysis
- `loop_optimization.rs`: Loop invariant detection

**Control Flow:**

- `traffic_light.rs`: State machine analysis with path-sensitive control
- `mode_controller.rs`: Modal system verification
- `protocol_fsm.rs`: Protocol compliance checking

**Pointer Analysis:**

- `pointsto_example.rs`: Pointer assignments, aliasing, load/store operations

**String Analysis:**

- `string_concatenation.rs`: String length tracking through concatenation
- `string_constant_and_length.rs`: Constant strings and length bounds
- `string_prefix_and_charset.rs`: Prefix matching and character set constraints
- `string_suffix_and_inclusion.rs`: Suffix analysis and substring detection
- `regex_analysis.rs`: Regular expression domain demonstration
- `automata_analysis.rs`: Finite automata-based string analysis

**Type Analysis:**

- `dynamic_type_check.rs`: Dynamic type tracking and type error detection

**Security & Validation:**

- `security_and_normalization.rs`: Taint analysis and input sanitization
- `input_validation.rs`: Input constraint verification

**Realistic Programs:**

- `realistic_programs.rs`: Array bounds checking, pointer aliasing, combined multi-domain analysis

## Quick Start

### Build and Test

```bash
# Build the project
cargo build

# Run all tests (80+ unit and integration tests)
cargo test

# Build with optimizations (abstract interpretation benefits greatly from release mode)
cargo build --release
```

### Run Examples

Each example demonstrates specific analysis capabilities with detailed explanations:

```bash
# Numeric analysis
cargo run --example sign_analysis
cargo run --example constant_propagation
cargo run --example combined_analysis

# Fixpoint computation
cargo run --example simple_loops
cargo run --example transfer_example
cargo run --example loop_optimization

# Control-sensitive analysis
cargo run --example traffic_light
cargo run --example mode_controller
cargo run --example protocol_fsm

# Pointer analysis
cargo run --example pointsto_example

# String analysis
cargo run --example string_concatenation
cargo run --example string_constant_and_length
cargo run --example regex_analysis
cargo run --example automata_analysis

# Type analysis
cargo run --example dynamic_type_check

# Security analysis
cargo run --example security_and_normalization
cargo run --example input_validation

# Comprehensive examples
cargo run --example realistic_programs
```

### Run with Release Mode for Performance

Abstract interpretation with BDDs is **exponentially faster** in release mode:

```bash
cargo run --release --example traffic_light
cargo run --release --example realistic_programs
```

## Architecture

### Core Traits

The framework is built around two foundational traits:

```rust
/// Abstract domain with lattice operations
pub trait AbstractDomain {
    type Element: Clone;

    // Lattice operations
    fn join(&self, a: &Element, b: &Element) -> Element;     // ⊔ (least upper bound)
    fn meet(&self, a: &Element, b: &Element) -> Element;     // ⊓ (greatest lower bound)
    fn widen(&self, a: &Element, b: &Element) -> Element;    // ∇ (widening)
    fn narrow(&self, a: &Element, b: &Element) -> Element;   // ∆ (narrowing)

    // Order and limits
    fn is_bottom(&self, elem: &Element) -> bool;
    fn is_top(&self, elem: &Element) -> bool;
    fn is_less_or_equal(&self, a: &Element, b: &Element) -> bool;  // ⊑
}

/// Numeric domain with transfer functions
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
- **`sign.rs`**: Sign domain implementation (7 lattice elements)
- **`constant.rs`**: Constant propagation domain (Bottom/Const(n)/Top)
- **`interval.rs`**: Interval domain [low, high] with ±∞ (500+ lines)
- **`congruence.rs`**: Congruence domain for modular arithmetic
- **`pointsto.rs`**: BDD-based pointer analysis (~1500 lines)
- **`string_domain.rs`**: String length, prefix, suffix, charset analysis
- **`automata.rs`**: Regular expression and automata domains
- **`type_domain.rs`**: Dynamic type tracking
- **`bdd_control.rs`**: BDD-based control state representation
- **`product.rs`**: Independent product domain (D₁ × D₂)
- **`generic_product.rs`**: Reduced product with inter-domain refinement
- **`fixpoint.rs`**: Fixpoint engine with widening/narrowing strategies
- **`transfer.rs`**: Abstract transfer functions for statements
- **`expr.rs`**: Expression and predicate AST types

### Fixpoint Engine

The fixpoint engine automates iterative analysis with convergence guarantees:

```rust
pub struct FixpointEngine<D: AbstractDomain> {
    pub domain: D,
    pub widening_threshold: usize,      // Default: 3
    pub narrowing_iterations: usize,    // Default: 2
    pub max_iterations: usize,          // Default: 100
}
```

Features:

- **LFP (Least Fixpoint)**: For forward reachability with widening
- **GFP (Greatest Fixpoint)**: For backward co-reachability with narrowing
- **Automatic convergence**: Iteration limits and stabilization detection
- **Configurable widening**: Control precision vs. termination tradeoff

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
    &NumExpr::Add(
        Box::new(NumExpr::Var("x".to_string())),
        Box::new(NumExpr::Const(3))
    ));
let state = domain.assign(&state, &"z".to_string(),
    &NumExpr::Mul(
        Box::new(NumExpr::Var("y".to_string())),
        Box::new(NumExpr::Const(2))
    ));

assert_eq!(state.get("z"), ConstValue::Const(20));  // Exact value!
```

### Interval Analysis with Fixpoints

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
    let expr = NumExpr::Add(
        Box::new(NumExpr::Var("x".to_string())),
        Box::new(NumExpr::Const(1))
    );
    let elem = domain.assign(elem, &"x".to_string(), &expr);
    let pred = NumPred::Lt(
        Box::new(NumExpr::Var("x".to_string())),
        Box::new(NumExpr::Const(10))
    );
    domain.assume(&elem, &pred)
};

let result = engine.lfp(init, f);
println!("x ∈ {}", result.get("x"));  // x ∈ [0, 9]
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

// Sign: x is Pos
// Constant: x is exactly 5
// Interval: x ∈ [5, 5]
// → Combined analysis gives most precise information
```

## Testing

```bash
# Run all tests
cargo test

# Run specific domain tests
cargo test sign::tests
cargo test constant::tests
cargo test interval::tests
cargo test pointsto::tests
cargo test string_domain::tests

# Run integration tests
cargo test --test domain_integration

# With output
cargo test -- --nocapture
```

**Current test coverage:**

- 80+ unit tests across all domains
- 10+ integration tests for domain cooperation
- 2 doc tests
- All domains have comprehensive test suites

## Performance

Fixpoint iterations typically converge quickly with widening:

- **Counter loop (0→10)**: ~3 iterations
- **Countdown (100→0)**: ~3 iterations
- **Unbounded loop**: ~3 iterations (widening to ∞)
- **BDD operations**: Exponentially faster in `--release` mode

**Key insight**: Abstract interpretation trading precision for termination enables analyzing loops that would require infinite concrete execution.

## Companion Guide

This implementation is accompanied by **"Abstract Interpretation with BDDs: A Gentle Guide"**, a comprehensive tutorial located in the `guide/` directory.

### Guide Structure

**Part I: Gentle Introduction** (Chapters 0-6)

- Prologue: The case for static analysis
- Foundations of abstraction
- Control flow and program structure
- Symbolic reasoning with BDDs
- Implementing the analysis engine
- Abstract program state and domain combinations
- Complete symbolic execution engine example

**Part II: Deep Dive** (Chapters 7-15)

- Lattice theory foundations
- Fixpoint algorithms
- Advanced Galois connections
- Approximation theory
- Algebraic domain combinations
- BDD path sensitivity
- String and automata domains
- Points-to and dynamic type domains
- Precision techniques and design patterns

**Part III: Applications & Future Directions** (Chapters 16-21)

- Security analysis (taint tracking, input validation)
- Inter-procedural analysis
- Performance optimization and debugging
- AI-guided analysis
- Case study: Access control system
- Conclusion and further reading

### Build the Guide

```bash
cd guide/

# Compile to PDF
typst compile main.typ guide.pdf

# Watch mode (auto-rebuild on changes)
typst watch main.typ guide.pdf
```

The guide provides:

- **Progressive learning**: From first principles to advanced implementation
- **Theory and practice**: Mathematical foundations with working code examples
- **Multiple reading paths**: Marked sections for beginners, practitioners, and researchers
- **Rich pedagogy**: Examples, exercises, warnings, insights, and visual diagrams
- **Complete coverage**: ~150 pages covering theory, implementation, and applications

## Project Structure

```text
abstract-interpretation/
├── src/                    # Core library implementation
│   ├── domain.rs          # Abstract domain trait
│   ├── numeric.rs         # Numeric domain trait
│   ├── sign.rs            # Sign domain
│   ├── constant.rs        # Constant propagation
│   ├── interval.rs        # Interval domain
│   ├── congruence.rs      # Congruence domain
│   ├── pointsto.rs        # Pointer analysis
│   ├── string_domain.rs   # String analysis
│   ├── automata.rs        # Automata domain
│   ├── type_domain.rs     # Type tracking
│   ├── bdd_control.rs     # BDD control domain
│   ├── product.rs         # Product domains
│   ├── generic_product.rs # Reduced products
│   ├── fixpoint.rs        # Fixpoint engine
│   ├── transfer.rs        # Transfer functions
│   └── expr.rs            # Expression AST
├── examples/              # 20 detailed examples
├── tests/                 # Integration tests
├── guide/                 # Comprehensive tutorial
│   ├── main.typ          # Guide entry point
│   ├── theme.typ         # Custom styling
│   ├── chapters/         # Guide chapters
│   └── code-examples/    # Example code for guide
└── README.md             # This file
```

## Dependencies

```toml
[dependencies]
bdd-rs = { path = "../.." }     # BDD library
log = "0.4"                      # Logging
num-integer = "0.1"              # Integer operations
num-traits = "0.2"               # Numeric traits
simplelog = "0.12"               # Simple logging
```

## References

### Foundational Papers

- **Cousot & Cousot (1977)**: "Abstract Interpretation: A Unified Lattice Model for Static Analysis of Programs by Construction or Approximation of Fixpoints"
- **Cousot & Cousot (1979)**: "Systematic Design of Program Analysis Frameworks"
- **Bryant (1986)**: "Graph-Based Algorithms for Boolean Function Manipulation"

### Domain Theory

- **Miné (2006)**: "The Octagon Abstract Domain"
- **Granger (1989)**: "Static Analysis of Arithmetical Congruences"
- **Blanchet et al. (2003)**: "A Static Analyzer for Large Safety-Critical Software" (Astrée)

### Pointer Analysis

- **Andersen (1994)**: "Program Analysis and Specialization for the C Programming Language"
- **Steensgaard (1996)**: "Points-to Analysis in Almost Linear Time"

### Applications

- **Beyer & Keremoglu (2011)**: "CPAchecker: A Tool for Configurable Software Verification"
- **Calcagno et al. (2015)**: "Moving Fast with Software Verification" (Facebook Infer)

## Contributing

Contributions are welcome! This project is part of the larger `bdd-rs` ecosystem.

- **Bug reports**: Open an issue with a minimal reproduction
- **New domains**: Add domain implementation with tests
- **Examples**: Demonstrate new analysis capabilities
- **Guide improvements**: Enhance explanations or add exercises

## License

MIT License --- see LICENSE file for details.

## Acknowledgments

This implementation builds on decades of research in abstract interpretation and symbolic verification.
Special thanks to Patrick and Radhia Cousot for pioneering abstract interpretation, and to Randal Bryant for introducing BDDs.

The `bdd-rs` library and this framework are open-source projects welcoming community contributions.
