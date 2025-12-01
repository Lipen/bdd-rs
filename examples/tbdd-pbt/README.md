# T-BDD: Theory-Aware BDD-Guided Property-Based Testing

A novel approach to property-based testing that combines Binary Decision Diagrams (BDDs) with theory solvers for intelligent test generation.

## What is T-BDD?

**T-BDD** (Theory-aware BDD-guided Property-Based Testing) combines three powerful techniques:

1. **Binary Decision Diagrams (BDDs)** — Canonical, compact representation of boolean functions
2. **Theory Solvers** — Reasoning about arithmetic, arrays, and other first-order theories
3. **Property-Based Testing** — Automatic generation of test inputs

## Core Idea

Traditional property-based testing generates random inputs, hoping to find bugs.
T-BDD instead:

1. **Encodes program branching** as predicates (e.g., `x < 0`, `y == 10`)
2. **Builds a BDD** representing all feasible execution paths
3. **Uses theory solvers** to prune infeasible paths and generate witnesses
4. **Produces targeted test inputs** that exercise specific program behaviors

## Key Benefits

| Aspect | Random Testing | Symbolic Execution | T-BDD |
|--------|---------------|-------------------|-------|
| Path coverage | ✗ Random | ✓ Systematic | ✓ Systematic |
| Scalability | ✓ Fast | ✗ Path explosion | ✓ BDD compaction |
| Constraint solving | ✗ None | ✓ SMT queries | ✓ Lightweight solvers |
| Representation | N/A | Explicit paths | ✓ Canonical BDD |

## Architecture

```
┌─────────────────────────────────────────────────────────────────┐
│                        T-BDD Framework                          │
├─────────────────────────────────────────────────────────────────┤
│                                                                 │
│  ┌─────────────┐    ┌─────────────┐    ┌─────────────────────┐  │
│  │   Program   │───▶│ Predicate   │───▶│   BDD Path Space    │  │
│  │ Predicates  │    │  Universe   │    │  (boolean combos)   │  │
│  └─────────────┘    └─────────────┘    └──────────┬──────────┘  │
│                                                   │             │
│                                                   ▼             │
│                     ┌─────────────────────────────────────────┐ │
│                     │         Path Explorer                   │ │
│                     │  • Enumerate BDD satisfying paths       │ │
│                     │  • Query theory checker for pruning     │ │
│                     │  • Track coverage via BDD operations    │ │
│                     └──────────┬──────────────────────────────┘ │
│                                │                                │
│              ┌─────────────────┴─────────────────┐              │
│              ▼                                   ▼              │
│  ┌─────────────────────┐           ┌─────────────────────────┐  │
│  │   Theory Solvers    │           │    Test Generator       │  │
│  │  (see table below)  │           │  (concrete witnesses)   │  │
│  └─────────────────────┘           └─────────────────────────┘  │
│                                                                 │
└─────────────────────────────────────────────────────────────────┘
```

## Core Components

### 1. Predicate Universe (`predicate.rs`)

Maps program conditions to BDD variables:

```rust
let p1 = Predicate::lt("x", 0);        // x < 0
let p2 = Predicate::ge("x", 100);      // x >= 100
let p3 = Predicate::lt_var("x", "y");  // x < y (relational)

let v1 = universe.register(p1, &bdd);
let v2 = universe.register(p2, &bdd);
let v3 = universe.register(p3, &bdd);
```

### 2. Theory Solvers (`theory.rs`)

Check path feasibility and generate concrete witnesses:

| Solver | Handles | Algorithm |
|--------|---------|-----------|
| `IntervalSolver` | `x < 10`, `y >= 0` | Interval abstract interpretation |
| `RelationalSolver` | `x < y`, `a == b` | Bellman-Ford on difference constraints |
| `ModularSolver` | `x % n == 0` | Modular arithmetic enumeration |
| `ArrayBoundsSolver` | `0 <= i < len` | Array index bounds verification |
| `BitwiseSolver` | Power-of-2, alignment | Bit manipulation post-processing |
| `CombinedSolver<S1, S2>` | Chain solvers | Theory combination |

```rust
let solver = IntervalSolver::new();
let result = solver.solve(&assignments, &universe);

match result {
    SolveResult::Sat(witness) => { /* use witness for testing */ }
    SolveResult::Unsat => { /* prune this path */ }
    SolveResult::Unknown => { /* solver couldn't determine */ }
}
```

### 3. Test Generator (`generator.rs`)

Multiple generation strategies for BDD paths:

| Generator | Description |
|-----------|-------------|
| `TestGenerator` | Basic path enumeration with theory solving |
| `RandomizedGenerator` | Randomized path exploration order |
| `PrioritizedGenerator` | Priority-based path selection |
| `SymbolicExecutor` | Full symbolic execution with path tracking |

```rust
let generator = TestGenerator::new(&bdd, &universe, &solver, config);
let tests = generator.generate(path_constraint);

for test in tests {
    let x = test.witness.get("x").unwrap();
    run_test_with_input(x);
}
```

### 4. Property Checker (`property.rs`)

Property-based testing with BDD-guided exploration:

```rust
let property = Property::new("abs is non-negative", |inputs| {
    let x = inputs.get("x").unwrap();
    x.abs() >= 0
});

let checker = PropertyChecker::new(&bdd, &universe, &solver);
match checker.check(&property, constraint) {
    CheckResult::Pass { test_count, .. } => println!("Passed {} tests", test_count),
    CheckResult::Fail { counterexample, .. } => println!("Found: {:?}", counterexample),
    CheckResult::Vacuous => println!("All paths pruned as infeasible"),
}
```

### 5. Coverage Tracker (`coverage.rs`)

Uses BDD operations for efficient coverage tracking:

```rust
let mut coverage = CoverageTracker::new(&bdd, target_paths);

// Record test execution
coverage.record_assignments(&test.path_assignments);

// Get coverage summary
let summary = coverage.summary();
println!("Coverage: {:.1}%", summary.predicate_coverage_ratio * 100.0);
println!("Complete: {}", summary.is_complete);

// Get uncovered paths as BDD
let uncovered = coverage.uncovered();
```

## Key Insights

### Why BDDs?

1. **Canonical Representation**: Each boolean function has exactly one BDD
2. **Efficient Set Operations**: Coverage tracking via BDD AND/OR is O(|BDD|)
3. **Compact Path Enumeration**: Exponential paths stored in polynomial space
4. **Easy Unsatisfiability**: Zero BDD = infeasible path

### Why Theory Integration?

BDDs only reason about boolean structure. Theory solvers handle:

- **Arithmetic Constraints**: `x < 5 AND x > 10` is UNSAT
- **Witness Generation**: Find concrete values satisfying constraints
- **Early Pruning**: Skip infeasible paths before test generation

## Usage

```bash
# Run tests
cargo test -p tbdd-pbt
```

### Running Examples

```bash
# Basic usage
cargo run -p tbdd-pbt --example basic

# Multi-variable constraints
cargo run -p tbdd-pbt --example multi_variable

# Property testing with shrinking
cargo run -p tbdd-pbt --example property_testing

# Coverage analysis
cargo run -p tbdd-pbt --example coverage

# Advanced theory solvers
cargo run -p tbdd-pbt --example advanced_theory

# Bug hunting patterns
cargo run -p tbdd-pbt --example bug_hunting
```

## Example: Function Categorization

```rust
fn categorize(x: i64) -> &'static str {
    if x < 0 { "negative" }
    else if x == 0 { "zero" }
    else if x < 100 { "small" }
    else { "large" }
}
```

T-BDD automatically:

1. Identifies 4 distinct paths
2. Prunes infeasible combinations (e.g., `(x < 0) ∧ (x == 0)`)
3. Generates witnesses: `x = -1`, `x = 0`, `x = 50`, `x = 100`
4. Achieves 100% path coverage

## Example Output

```
=== T-BDD: Theory-Aware BDD-Guided Property-Based Testing ===

Registered predicates:
  P1 (var Var(1)): x < 0
  P2 (var Var(2)): x == 0
  P3 (var Var(3)): x < 100

Testing path 'negative':
  ✓ x =  -500 -> 'negative' (expected 'negative')

Testing path 'zero':
  ✓ x =     0 -> 'zero' (expected 'zero')

=== Coverage Summary ===
  Predicate coverage: 100.0%
  Tests executed:     4
  Complete:           yes

=== Demonstrating Theory-Based Pruning ===

Infeasible path (x < 0 AND x == 0):
  No tests generated (theory pruned infeasible path) ✓
```

## Scientific Novelty & Future Directions

### Current Contributions

1. **BDD-Based Path Representation**: Novel use of BDDs for test space representation
2. **Theory-Aware Pruning**: Combines boolean reasoning with arithmetic constraints
3. **Coverage-Guided Generation**: Uses BDD operations for efficient coverage tracking

### Potential Research Extensions

1. **Richer Theories**
   - Linear integer arithmetic (LIA) via SMT solvers
   - Bitvectors for low-level code
   - Arrays and strings

2. **Adaptive Exploration**
   - Learn which predicates correlate with bugs
   - Prioritize under-tested code regions
   - Use reinforcement learning for path selection

3. **Incremental Solving**
   - Cache theory solver results across similar paths
   - Exploit BDD structure for incremental constraint solving

4. **Integration with Fuzzing**
   - Use BDD structure to guide mutation strategies
   - Combine symbolic reasoning with coverage-guided fuzzing

5. **Program Analysis Integration**
   - Extract predicates automatically from source code
   - Build CFG-based path constraints
   - Handle loops via bounded unrolling or abstraction

### Related Work Connections

- **DART/SAGE**: Directed automated random testing
- **KLEE**: Symbolic execution with constraint solving
- **QuickCheck/Hypothesis**: Property-based testing
- **Concolic Testing**: Concrete + symbolic execution

T-BDD sits at the intersection of these approaches, offering:

- Symbolic reasoning (like KLEE) but with BDD efficiency
- Random testing (like QuickCheck) but with path awareness
- Constraint solving (like SAGE) but with compact representation

## Implementation Notes

### Dependencies

- `bdd-rs`: BDD library with complement edges
- `rand`: Randomized test generation
- `color-eyre`: Error handling

### Limitations

Current implementation:

1. **Manual Predicate Extraction**: Predicates must be specified manually
2. **Lightweight Theories**: Custom solvers, no SMT integration
3. **No Loop Handling**: Assumes acyclic control flow

These can be addressed in future work.
