# T-BDD: Theory-Aware BDD-Guided Property-Based Testing

A novel approach to property-based testing that combines Binary Decision Diagrams (BDDs) with theory solvers for intelligent test generation.

## Overview

T-BDD bridges the gap between symbolic execution and property-based testing:

- **Symbolic Execution**: Explores program paths symbolically but faces path explosion
- **Property-Based Testing**: Generates random inputs but may miss edge cases
- **T-BDD**: Uses BDDs to compactly represent the path space, theory solvers to prune infeasible paths, and guided generation to maximize coverage

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
│  │   Theory Checker    │           │    Test Generator       │  │
│  │  (Interval Domain)  │           │  (concrete witnesses)   │  │
│  └─────────────────────┘           └─────────────────────────┘  │
│                                                                 │
└─────────────────────────────────────────────────────────────────┘
```

## Core Components

### 1. Predicate Universe (`predicate.rs`)

Maps program conditions to BDD variables:

```rust
// Extract predicates from program branches
let p1 = Predicate::lt("x", 0);      // x < 0
let p2 = Predicate::eq("x", 0);      // x == 0
let p3 = Predicate::lt("x", 100);    // x < 100

// Register with BDD
let v1 = universe.register(p1, &bdd);
let v2 = universe.register(p2, &bdd);
let v3 = universe.register(p3, &bdd);
```

### 2. Theory Solver (`theory.rs`)

Checks feasibility of path constraints using interval arithmetic:

```rust
// Path: x < 0 AND x >= 10 → UNSAT (impossible!)
let solver = IntervalSolver::new();
let result = solver.solve(&assignments, &universe);

match result {
    SolveResult::Sat(witness) => { /* use witness for testing */ }
    SolveResult::Unsat => { /* prune this path */ }
    SolveResult::Unknown => { /* conservative: try anyway */ }
}
```

### 3. Test Generator (`generator.rs`)

Generates concrete test inputs from BDD paths:

```rust
let generator = TestGenerator::new(&bdd, &universe, &solver, config);

// Generate tests for a specific path constraint
let tests = generator.generate(path_constraint);

for test in tests {
    // test.witness contains concrete values
    let x = test.witness.get("x").unwrap();
    run_test_with_input(x);
}
```

### 4. Coverage Tracker (`coverage.rs`)

Uses BDD operations for efficient coverage tracking:

```rust
let mut coverage = CoverageTracker::new(&bdd, target_paths);

// Record test execution
coverage.record_assignments(&test.path_assignments);

// Check what's left to cover
let uncovered = coverage.uncovered();  // Returns BDD of uncovered paths
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
# Run the example
cargo run -p tbdd-pbt

# Run tests
cargo test -p tbdd-pbt
```

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
- `thiserror`: Error handling

### Limitations

Current implementation has some simplifications:

1. **Manual Predicate Extraction**: Predicates must be specified manually
2. **Simple Theory**: Only interval arithmetic (no SMT)
3. **No Loop Handling**: Assumes acyclic control flow
4. **Single Variable Comparisons**: No `x < y` constraints

These can be addressed in future work.
