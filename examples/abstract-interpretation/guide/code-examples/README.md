# Guide Code Examples

This directory contains tested, runnable code examples that accompany the *Abstract Interpretation with BDDs* guide.
All examples are complete, self-contained, and directly executable.

## Organization Philosophy

Examples are organized **by topic** rather than by chapter number.
This design makes the codebase resilient to guide restructuring while maintaining clear semantic relationships between related concepts.

### Directory Structure

```
code-examples/
├── domains/              # Abstract domain implementations
│   ├── sign.rs           # Sign abstraction domain
│   ├── interval.rs       # Interval domain with arithmetic
│   └── combined.rs       # Reduced product of multiple domains
├── control_flow/         # Control flow analysis
│   └── cfg_builder.rs    # Building control flow graphs
├── bdd_fundamentals/     # Core BDD operations
│   ├── basics.rs         # Creating and manipulating BDDs
│   ├── boolean_ops.rs    # AND, OR, NOT, XOR operations
│   └── manager_demo.rs   # BDD manager and hash consing
├── bdd_advanced/         # Advanced BDD techniques
│   ├── quantification.rs  # Existential/universal quantification
│   └── variable_ordering.rs  # Impact of variable ordering on size
├── integration/          # Combining BDDs with abstract domains
│   └── sign_with_bdd.rs  # Sign domain with BDD-based control
└── symbolic_execution/   # Complete symbolic execution engines
    ├── executor.rs       # Full symbolic executor implementation
    ├── path_exploration.rs  # Path-sensitive analysis with BDDs
    └── verifier.rs       # Complete verifier with Interval domain
```

## Running Examples

Each example can be run individually using its semantic name:

```bash
# Abstract domains
cargo run --example sign_domain
cargo run --example interval_domain
cargo run --example combined_domain

# Control flow
cargo run --example cfg_builder

# BDD fundamentals
cargo run --example bdd_basics
cargo run --example bdd_boolean_ops
cargo run --example bdd_manager

# Advanced BDD techniques
cargo run --example bdd_quantification
cargo run --example bdd_variable_ordering

# Integration
cargo run --example sign_with_bdd

# Symbolic execution
cargo run --example symbolic_executor
cargo run --example path_exploration
cargo run --example verifier
```

## Example Features

Each example is designed to:

- **Stand alone**: Complete with all necessary imports and setup
- **Demonstrate concepts**: Focus on specific techniques from the guide
- **Show output**: Include print statements showing expected behavior
- **Be tested**: Compile and run successfully as part of CI

## Cross-References with the Guide

The guide uses several methods to reference these examples:

### 1. Inline Code Example Links

Small clickable badges that link directly to the source:

```typst
The complete implementation is available as #code-example("domains", "sign.rs").
```

### 2. Example Reference Blocks

Highlighted blocks with run instructions:

```typst
#example-reference(
  "domains",
  "sign.rs",
  "sign_domain",
  [
    A complete sign domain implementation with join, meet, and widening operators.
    Demonstrates how to abstract integer values into signs.
  ],
)
```

### 3. Quick Inline References

For casual mentions in explanatory text:

```typst
For the full implementation, #inline-example("domains", "sign.rs", "sign_domain").
```

## Adding New Examples

When adding a new example:

1. **Choose the right topic directory** (or create a new one if needed)
2. **Use a descriptive filename** that indicates the concept (not a chapter number)
3. **Register in `Cargo.toml`** under the appropriate section with a semantic name
4. **Add comprehensive doc comments** at the top explaining:
   - What concept this demonstrates
   - Which parts of the guide it relates to
   - Expected output and behavior
5. **Include inline comments** clarifying key implementation details
6. **Test that it runs**: `cargo run --example <your-name>`

### Example Template

```rust
//! Sign Domain Implementation
//!
//! Demonstrates abstract interpretation with the sign domain {⊥, -, 0, +, ⊤}.
//! Related to guide chapters on abstract domains and lattice theory.
//!
//! This example shows:
//! - Domain element representation
//! - Lattice operations (join, meet)
//! - Abstract transformers for arithmetic
//! - Widening operator for convergence
//!
//! Expected output:
//! - Demonstrates join: (-) ⊔ (+) = ⊤
//! - Shows abstract addition: (-) + (-) = (-)
//! - Illustrates widening for loops

use std::fmt;

// ... implementation ...

fn main() {
    println!("Sign Domain Example");
    println!("===================\n");

    // ... demo code with explanatory output ...
}
```

## Testing

All examples are tested to ensure they compile and run:

```bash
# Test that all examples compile
cargo test

# Run all examples (useful for verification)
for example in sign_domain interval_domain cfg_builder bdd_basics bdd_boolean_ops \
               bdd_manager bdd_quantification bdd_variable_ordering combined_domain \
               sign_with_bdd symbolic_executor path_exploration verifier; do
    echo "Running $example..."
    cargo run --example $example
done
```

## Benefits of Topic-Based Organization

1. **Renumbering-proof**: Guide chapters can be reordered without affecting code structure
2. **Semantic grouping**: Related examples are together, making them easier to find
3. **Discoverable**: Clear topic names indicate what each example demonstrates
4. **Scalable**: Easy to add new examples without restructuring existing ones
5. **Maintainable**: Changes to one example don't cascade to others
6. **Intuitive**: Developers can find examples by concept, not by chapter memory

## Relationship to Guide Structure

The guide is organized in three parts:

- **Part I: Gentle Introduction** (Chapters 0-6) uses examples from:
  - `domains/`
  - `control_flow/`
  - `bdd_fundamentals/`
  - `integration/`
  - `symbolic_execution/`

- **Part II: Deep Dive** (Chapters 7-15) extends these with:
  - Advanced lattice constructions
  - Sophisticated domain combinations
  - Precision techniques

- **Part III: Applications** (Chapters 16-20) shows real-world usage:
  - Security analysis
  - Interprocedural analysis
  - Performance optimization

Examples can be referenced by multiple chapters, emphasizing that concepts build on each other rather than being strictly linear.

## Contributing

Contributions are welcome! When submitting new examples:

- Follow the existing code style and documentation patterns
- Ensure examples are self-contained and runnable
- Add clear output showing expected behavior
- Update this README with the new example
- Update `Cargo.toml` with the new entry
- Consider which guide sections should reference it

## License

All examples are part of the bdd-rs project and follow the same license.
