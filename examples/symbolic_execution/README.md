# Symbolic Execution with BDDs

A symbolic execution engine for a simple imperative language, demonstrating how BDDs can be used for formal verification.

## Overview

This tool performs symbolic execution on programs written in a simple boolean imperative language. It uses Binary Decision Diagrams (BDDs) to:

- Track symbolic states efficiently
- Represent path conditions compactly
- Detect assertion violations
- Explore multiple execution paths

## Language Features

The language supports:

- **Boolean variables** and literals (`true`, `false`)
- **Boolean expressions**: `&&` (AND), `||` (OR), `!` (NOT), `^` (XOR), `=>` (IMPLIES), `==` (EQUALS)
- **Assignments**: `x = expr;`
- **Conditionals**: `if expr { stmt } else { stmt }`
- **Loops**: `while expr { stmt }` (bounded unrolling)
- **Assertions**: `assert expr;` (verification property)
- **Assumptions**: `assume expr;` (path constraint)

## Usage

```bash
# Run built-in examples
cargo run -p symbolic_execution --bin symexec -- example <name>

# Available examples: simple, branch, xor, mutex, loop
cargo run -p symbolic_execution --bin symexec -- example mutex
```

## Examples

### 1. Simple Sequential Program

```text
x = true;
y = x;
assert y;
```

**Result**: ✓ All assertions passed (1 path)

### 2. Branching with Equivalence

```text
if x {
  y = true;
} else {
  y = false;
}
assert (x == y);
```

**Result**: ✓ All assertions passed (2 paths)

### 3. XOR Property Verification

```text
z = x ^ y;
assert (z == ((x || y) && !(x && y)));
```

**Result**: ✓ XOR equivalence verified

### 4. Mutual Exclusion Bug Detection

```text
req1 = true;
if req2 {
  skip;
} else {
  acquire1 = true;
}
req2 = true;
if req1 {
  skip;
} else {
  acquire2 = true;
}
assert !(acquire1 && acquire2);
```

**Result**: ✗ Found 2 assertion failures - detects race condition where both threads can acquire the lock!

## Technical Details

### Symbolic State

Each execution state consists of:

- **Variable map**: Program variables → BDD variable indices
- **Symbolic store**: Program variables → BDD expressions (their symbolic values)
- **Path condition**: BDD representing constraints accumulated along the execution path

### Execution Strategy

1. **Path exploration**: Uses worklist algorithm to explore all feasible paths
2. **Branch handling**: On conditionals, fork into two paths with complementary constraints
3. **Loop unrolling**: Bounded unrolling (default: 10 iterations)
4. **Assertion checking**: Tests if `path_condition ∧ ¬assertion` is satisfiable

### BDD Benefits

- **Compact representation**: Equivalent states are automatically shared
- **Efficient operations**: Boolean operations are canonical
- **Precise reasoning**: No false positives from overapproximation
- **Path condition management**: Implicit constraint propagation

## Architecture

```text
examples/symbolic_execution/
├── src/
│   ├── ast.rs        # Language AST (Expr, Stmt, Program)
│   ├── state.rs      # Symbolic state (VarMap, SymbolicState)
│   ├── executor.rs   # Symbolic execution engine
│   ├── main.rs       # CLI tool
│   └── lib.rs        # Module exports
├── programs/         # Example programs
└── Cargo.toml
```

## Configuration

```rust
ExecutionConfig {
    max_loop_unroll: 10,    // Maximum loop iterations
    max_paths: 1000,        // Maximum paths to explore
}
```

## Limitations

- Boolean domain only (no integers)
- Bounded loop unrolling (may miss bugs in deep loops)
- No function calls or recursion
- No concurrency primitives (interleaving must be explicit)

## Research Applications

This demonstrates BDD usage in:

- **Software verification**: Detect bugs via symbolic execution
- **Test generation**: Path conditions give test inputs
- **Program analysis**: Compute reachable states
- **Concurrency verification**: Detect race conditions and deadlocks

## Counterexample Generation

The engine automatically generates **test cases** (counterexamples) when assertion failures are detected:

### Input vs Program Variables

- **Input Variables**: Variables read before being assigned (inferred automatically)
- **Program Variables**: Variables computed during execution
- **Test Case**: Concrete Boolean assignments to input variables

### Example

For this buggy program:

```rust
if x && y {
  z = true;
  x = false;  // Mutation!
  y = false;  // Mutation!
} else {
  z = false;
}
assert !z;
```

The engine produces:

```text
Test Case #1 (triggers: assert !z):
  Input assignments:
    x = true
    y = true

Variable values on failing path:
  x = false
  y = false
  z = true
```

Note: The **test case** shows original input values (`x=true, y=true`) needed to trigger the bug, while the **failing path** shows final values after mutations.

### Implementation

- Tracks original symbolic values for input variables separately
- Queries path conditions to extract concrete input assignments
- Handles input mutations correctly by preserving initial symbolic references

## Future Extensions

- [ ] Integer/bitvector support (via bit-blasting)
- [ ] SMT solver integration for richer theories
- [x] Counterexample generation (concrete inputs for failures) ✓
- [ ] Test suite generation (coverage-guided)
- [ ] Program slicing based on relevant variables
- [ ] Compositional verification (function summaries)
- [ ] Concurrency: explicit thread interleaving

## References

- Symbolic Execution: Clarke, "Symbolic Model Checking" (1999)
- BDD-based Verification: Burch et al., "Symbolic Model Checking: 10^20 States and Beyond" (1990)
- Path Conditions: King, "Symbolic Execution and Program Testing" (1976)
