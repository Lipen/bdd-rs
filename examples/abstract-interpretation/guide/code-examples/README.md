# Guide Code Examples

This directory contains tested, runnable code examples corresponding to each chapter of the Abstract Interpretation guide.

## Structure

Each chapter has its own directory with focused examples:

- **chapter01/**: Sign domain, interval domain implementations
- **chapter02/**: Control flow graph construction
- **chapter03/**: Basic BDD operations
- **chapter04/**: BDD programming (quantification, variable ordering)
- **chapter05/**: Combined BDD + data domains
- **chapter06/**: Symbolic execution implementation

## Running Examples

Each example can be run individually:

```bash
cargo run --example ch01_sign_domain
cargo run --example ch03_bdd_basics
cargo run --example ch04_quantification
```

## Cross-References

Examples are designed to be read alongside the guide chapters. Each file contains:

- Doc comments explaining the connection to the chapter
- Inline comments clarifying key concepts
- Output showing expected behavior

## Testing

All examples are tested to ensure they compile and run correctly:

```bash
cargo test
```

## Contributing

When adding new examples:

1. Add the example to `Cargo.toml`
2. Include comprehensive doc comments
3. Reference the specific chapter/section
4. Add output examples showing expected behavior
5. Test that the example runs successfully
