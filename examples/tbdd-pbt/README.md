# T-BDD: Theory-Aware BDD-Guided Property-Based Testing

**T-BDD** turns a program's branching structure into a BDD, then uses theory solvers to generate tests that systematically cover all feasible execution paths.

## The Idea in One Sentence

> BDDs compactly represent all boolean combinations of program predicates; theory solvers prune infeasible paths and produce concrete test inputs.

## Why T-BDD?

| Problem | Random Testing | Symbolic Execution | T-BDD |
|---------|----------------|--------------------|-------|
| Covers rare paths | ✗ Unlikely | ✓ Systematic | ✓ Systematic |
| Scales to many paths | ✓ O(1) per test | ✗ Exponential explosion | ✓ BDD compaction |
| Generates witnesses | ✓ Random values | ✓ SMT solver | ✓ Theory solvers |
| Tracks coverage | ✗ No structure | ✗ Explicit path lists | ✓ BDD operations |

**Key insight**: BDDs give us a *canonical*, *compact* representation of the boolean path space, while theory solvers give us *pruning* and *witness generation* — together they enable systematic testing without the exponential blowup of symbolic execution.

## How It Works

```
             ┌────────────────────┐
             │ Program Predicates │
             │  x < 0, y == 10    │
             └─────────┬──────────┘
                       │
                       ▼
              ┌──────────────────┐
              │  BDD Path Space  │  ← compact representation
              │  (all boolean    │     of 2^n combinations
              │   combinations)  │
              └────────┬─────────┘
                       │
         ┌─────────────┴─────────────┐
         ▼                           ▼
┌─────────────────┐        ┌─────────────────┐
│ Theory Solver   │        │  Path Explorer  │
│ • Prune UNSAT   │───────▶│  • Enumerate    │
│ • Generate      │        │  • Prioritize   │
│   witnesses     │        │  • Track cover  │
└─────────────────┘        └────────┬────────┘
                                    │
                                    ▼
                           ┌─────────────────┐
                           │  Test Inputs    │
                           │  {x=-5, y=10}   │
                           └─────────────────┘
```

## Quick Example

```rust
use tbdd_pbt::*;
use bdd_rs::bdd::Bdd;

// Create BDD manager and predicate universe
let bdd = Bdd::new();
let mut universe = PredicateUniverse::new();

// Register predicates (program branch conditions)
let x_neg = universe.register(Predicate::lt("x", 0), &bdd);     // x < 0
let x_zero = universe.register(Predicate::eq("x", 0), &bdd);    // x == 0
let x_small = universe.register(Predicate::lt("x", 100), &bdd); // x < 100

// Build path constraint: x >= 0 AND x != 0 AND x < 100 (small positive)
let small_positive = bdd.and(bdd.not(x_neg), bdd.and(bdd.not(x_zero), x_small));

// Generate tests using theory solver
let solver = IntervalSolver::with_bounds(-1000, 1000);
let generator = TestGenerator::new(&bdd, &universe, &solver, GeneratorConfig::default());

for test in generator.generate(small_positive) {
    let x = test.witness.get("x").unwrap();
    assert!(*x > 0 && *x < 100, "x={} should be small positive", x);
}
```

## Modules

| Module | Purpose |
|--------|---------|
| `predicate` | Map program conditions to BDD variables |
| `theory` | Constraint solvers: interval, relational, modular, bitwise, combined |
| `generator` | Enumerate BDD paths, generate test inputs |
| `coverage` | Track coverage using BDD operations |
| `property` | Property-based testing with shrinking |
| `cfg` | Control-flow graph construction and path extraction |
| `loops` | Loop detection and bounded unrolling |
| `domain` | Abstract domains for precise constraint solving |

## Theory Solvers

| Solver | Constraints | Algorithm |
|--------|-------------|-----------|
| `IntervalSolver` | `x < 10`, `y >= 0` | Interval propagation |
| `RelationalSolver` | `x < y`, `a - b <= 5` | Bellman-Ford shortest paths |
| `ModularSolver` | `x % n == r` | CRT-based enumeration |
| `BitwiseSolver` | Power-of-2, alignment | Bit manipulation |
| `CombinedSolver` | Chain solvers | Theory combination |

## Usage

```bash
# Run tests
cargo test -p tbdd-pbt

# Run examples
cargo run -p tbdd-pbt --example basic
cargo run -p tbdd-pbt --example cfg_exploration
cargo run -p tbdd-pbt --example loop_analysis
cargo run -p tbdd-pbt --example abstract_domains

# Run benchmarks
cargo bench -p tbdd-pbt
```

## Research Context

T-BDD bridges several research areas:

- **Symbolic Execution** (KLEE, SAGE): systematic path exploration
- **Property-Based Testing** (QuickCheck): automatic test generation
- **Abstract Interpretation**: sound constraint propagation
- **BDD Applications**: compact boolean function representation

The novelty is using BDDs as the *central data structure* for test space representation, enabling efficient coverage tracking and path enumeration while maintaining soundness through theory solver integration.

## Limitations & Future Work

**Current**:

- Predicates must be specified manually (no automatic extraction)
- Loop handling requires bounded unrolling
- No SMT solver integration (custom lightweight solvers only)

**Planned**:

- Automatic predicate extraction from CFG
- Adaptive path prioritization
- SMT solver backends for richer theories
- Fuzzing integration

## License

See the root repository license.
