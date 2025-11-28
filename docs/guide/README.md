# Binary Decision Diagrams: Theory, Implementation, and Applications

A comprehensive guide to Binary Decision Diagrams (BDDs) — from theoretical foundations to practical implementation.

## Building the Guide

This guide is written in [Typst](https://typst.app/). To compile:

```bash
# Install Typst (if not already installed)
# See https://github.com/typst/typst#installation

# Compile the guide
typst compile main.typ

# Or watch for changes
typst watch main.typ
```

## Structure

The guide is organized into five parts:

### Part I: Foundations

Theoretical foundations of BDDs — Boolean functions, Shannon expansion, canonical form, and core operations.

### Part II: Implementation

Practical implementation details — architecture, node representation, unique tables, caching, and complement edges.

### Part III: Advanced Topics

Advanced techniques — variable ordering, garbage collection, quantification, and BDD variants (ZDDs, ADDs).

### Part IV: Applications

Real-world applications — model checking, combinatorial problems, symbolic execution, and configuration management.

### Part V: Ecosystem and Comparison

Survey of BDD libraries, design trade-offs, and future research directions.

## Prerequisites

Readers should have:

- Basic understanding of Boolean algebra
- Familiarity with graph data structures
- Some programming experience (examples use Rust)

## Accompanying Code

This guide accompanies the [`bdd-rs`](https://github.com/Lipen/bdd-rs) library.
Code examples throughout the text use Rust, but concepts are language-agnostic.

## Contributing

Contributions are welcome! Please see the main repository for guidelines.

## License

This guide is part of the bdd-rs project. See the repository root for license information.
