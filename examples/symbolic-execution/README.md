# Symbolic Execution with BDDs

A symbolic execution engine for a simple imperative language that demonstrates how Binary Decision Diagrams (BDDs) enable efficient formal verification.

## Overview

This tool performs symbolic execution on programs written in a boolean imperative language. It leverages BDDs to:

- Efficiently track symbolic states across execution paths
- Compactly represent path conditions and constraints
- Precisely detect assertion violations without false positives
- Explore all reachable program paths

## Language Features

The language supports:

- **Boolean variables** and literals (`true`, `false`)
- **Boolean operators**: `&&` (AND), `||` (OR), `!` (NOT), `^` (XOR), `=>` (IMPLIES), `==` (EQUALS)
- **Assignments**: `x = expr;`
- **Conditionals**: `if expr { ... } else { ... }`
- **Loops**: `while expr { ... }` with bounded unrolling
- **Assertions**: `assert expr;` — specify properties to verify
- **Assumptions**: `assume expr;` — add constraints to execution paths
- **Exceptions**: `try { ... } catch (e) { ... } finally { ... }` — exception handling with cleanup

## Usage

```bash
# Run built-in examples
# cargo run --bin symexec -- example <name>

# Available examples
cargo run --bin symexec -- example simple      # sequential program
cargo run --bin symexec -- example branch      # branching logic
cargo run --bin symexec -- example xor         # property verification
cargo run --bin symexec -- example mutex       # concurrency verification
cargo run --bin symexec -- example loop        # loop unrolling
cargo run --bin symexec -- example buggy       # counterexample generation
```

## Examples

### 1. Simple Sequential Program

```rust
x = true;
y = x;
assert y;
```

**Result**: ✓ All assertions passed (verified that y is always true)

### 2. Branching with Equivalence

```rust
if x {
  y = true;
} else {
  y = false;
}
assert x == y;
```

**Result**: ✓ Proved that y always equals x after this code

### 3. XOR Property Verification

```rust
z = x ^ y;
assert z == ((x || y) && !(x && y));
```

**Result**: ✓ Verified XOR definition is equivalent to its logical expansion

### 4. Mutex Protocol Verification

This example models a simple mutual exclusion protocol where two threads compete for a lock. The symbolic variable `locked` represents whether the lock is initially held, and `thread1_first` determines the execution order.

```rust
in_cs1 = false;
in_cs2 = false;
if thread1_first {
  if !locked {
    locked = true;
    in_cs1 = true;
  }
  if !locked {
    locked = true;
    in_cs2 = true;
  }
} else {
  if !locked {
    locked = true;
    in_cs2 = true;
  }
  if !locked {
    locked = true;
    in_cs1 = true;
  }
}
assert !(in_cs1 && in_cs2);
```

**Result**: ✓ Verified that both threads never simultaneously enter the critical section (mutex property holds)

## How It Works

### Symbolic State

Each execution state tracks:

- **Variable map**: Maps program variables to unique BDD indices
- **Symbolic store**: Maps program variables to BDD expressions representing their current symbolic values
- **Path condition**: A BDD encoding all constraints accumulated along the current execution path

### Execution Algorithm

The engine uses a worklist-based exploration strategy:

1. **Path enumeration**: Systematically explores all feasible execution paths through the program
2. **Branch forking**: At each conditional, creates two states with complementary path constraints
3. **Constraint propagation**: Prunes infeasible paths where path conditions become unsatisfiable
4. **Loop handling**: Applies bounded unrolling (default: 10 iterations) to handle loops
5. **Assertion checking**: Verifies that `path_condition ∧ ¬assertion` is unsatisfiable (no counterexample exists)

### Why BDDs?

BDDs provide several key advantages for symbolic execution:

- **Canonical representation**: Equivalent boolean expressions are automatically unified, enabling efficient state comparison
- **Compact encoding**: Path conditions with many constraints can often be represented compactly
- **Efficient operations**: Boolean operations (AND, OR, NOT) are polynomial in BDD size
- **Precise reasoning**: No approximation means no false positives in verification results
- **Automatic simplification**: Constraint propagation happens implicitly through BDD operations

## Project Structure

```text
src/
├── ast.rs              # Abstract syntax tree definitions
├── cfg.rs              # Control flow graph representation
├── state.rs            # Symbolic state management
├── executor.rs         # Symbolic execution engine
├── counterexample.rs   # Test case generation from failures
├── lib.rs              # Public API
└── bin/
    └── symexec.rs      # Command-line interface
```

## Configuration

The execution engine can be configured with:

```rust
ExecutionConfig {
    max_loop_unroll: 10,    // Maximum loop iterations
    max_paths: 1000,        // Maximum paths to explore
    counterexample_config: CounterexampleConfig {
        minimize: false,    // Generate minimal test cases
        prefer_false: true, // Prefer false for unconstrained inputs
    }
}
```

## Limitations & Design Choices

- **Boolean domain only**: Currently supports only boolean variables (no integers or other types)
- **Bounded loop unrolling**: Loops are unrolled up to a fixed limit, which may miss bugs requiring many iterations
- **No function abstraction**: The language doesn't support function calls or recursion
- **Explicit concurrency**: Thread interleavings must be explicitly modeled (no automatic interleaving enumeration)

## Applications

This symbolic execution engine demonstrates practical applications of BDDs in:

- **Bug detection**: Automatically find inputs that violate assertions
- **Property verification**: Prove correctness properties hold for all inputs
- **Test generation**: Extract concrete test cases from symbolic execution traces
- **Program analysis**: Compute reachable states and feasible paths
- **Concurrency verification**: Verify mutual exclusion and other synchronization properties

## Counterexample Generation

When an assertion can fail, the engine automatically generates **test cases** showing concrete input values that trigger the failure.

### Key Concepts

- **Input Variables**: Variables that are read before being assigned (automatically inferred from the program)
- **Program Variables**: Intermediate values computed during execution
- **Test Case**: A concrete assignment of boolean values to input variables that demonstrates the bug

### Example: Finding a Bug

Consider this buggy program where inputs get mutated:

```rust
if x && y {
  z = true;
  x = false;  // Bug: input mutation!
  y = false;  // Bug: input mutation!
} else {
  z = false;
}
assert !z;  // This assertion fails
```

The engine produces this output:

```text
=== Counterexamples (Test Cases) ===

Test Case #1 (triggers: assert !z):
  Input assignments:
    x = true
    y = true

=== Detailed Failure Information ===

Failure #1: assert !z
  Variable values on failing path:
    x = false
    y = false
    z = true
```

**Key insight**: The test case shows the **original input values** (`x=true, y=true`) needed to trigger the bug, while the failure information shows **final values after execution** (`x=false, y=false, z=true`). This distinction is crucial when inputs are mutated during execution.

### Implementation Details

The counterexample generator:

- Preserves original symbolic BDD references for input variables (before any mutations)
- Queries the path condition to determine which input assignments lead to assertion failures
- Correctly handles programs that modify their inputs during execution
- Produces minimal test cases that developers can use to reproduce bugs

## Future Directions

- [ ] Integer and bitvector support via bit-blasting to boolean formulas
- [ ] SMT solver integration for theories beyond pure boolean logic
- [x] **Counterexample generation from assertion failures** ✓
- [ ] Coverage-guided test suite generation (branch/path coverage)
- [ ] Program slicing to reduce verification complexity
- [ ] Function summaries for compositional verification
- [ ] Automatic thread interleaving enumeration for concurrency

## Further Reading

- **Symbolic Execution**: James C. King, "Symbolic Execution and Program Testing" (CACM 1976)
- **BDD-based Model Checking**: J. R. Burch et al., "Symbolic Model Checking: 10^20 States and Beyond" (LICS 1990)
- **Symbolic Model Checking**: Edmund M. Clarke et al., "Model Checking" (MIT Press 1999)
