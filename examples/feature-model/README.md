# Feature Model Analyzer

A tool for analyzing feature models using Binary Decision Diagrams (BDDs).

## Overview

Feature models are used in software product line engineering to represent variability in configurable systems. This tool uses BDDs to efficiently encode and analyze feature models, answering questions about valid configurations, dependencies, and feature relationships.

## Building

```bash
cd examples/feature_model
cargo build --release
```

## Usage

```bash
# Show statistics
cargo run --release -- -i examples/mobile.fm stats

# Count valid configurations
cargo run --release -- -i examples/automotive.fm count

# Find core features (mandatory in all configurations)
cargo run --release -- -i examples/webserver.fm core

# Find dead features (impossible to select)
cargo run --release -- -i examples/dead_feature.fm dead

# Check if a configuration is valid
cargo run --release -- -i examples/mobile.fm check "1=true,2=true,9=true"

# Show feature commonality (percentage of configs with each feature)
cargo run --release -- -i examples/automotive.fm commonality

# Check if two features are mutually exclusive
cargo run --release -- -i examples/automotive.fm excludes 3 4

# Check if one feature implies another
cargo run --release -- -i examples/automotive.fm implies 12 10
```

## Input Formats

### Simple Format

Human-readable format with one constraint per line:

```text
feature <id> <name>
root <id>
mandatory <id>
requires <f1> <f2>
excludes <f1> <f2>
atleastone <f1> <f2> ...
exactlyone <f1> <f2> ...
```

Example:

```text
feature 1 Base
feature 2 FeatureA
feature 3 FeatureB
root 1
excludes 2 3
```

### DIMACS CNF Format

Standard format for boolean formulas:

```text
c feature <id> <name>
p cnf <num_vars> <num_clauses>
<literal> <literal> ... 0
```

Example:

```text
c feature 1 Base
c feature 2 FeatureA
p cnf 2 2
1 0
-1 2 0
```

## Examples

### Mobile Phone Configuration

Run: `cargo run --release -- -i examples/mobile.fm stats`

Models a smartphone with:

- Mandatory base and screen
- Optional camera (front/rear)
- Storage options (32GB, 64GB, 128GB - exactly one)
- Connectivity features (GPS, Bluetooth, WiFi)

### Automotive Configuration

Run: `cargo run --release -- -i examples/automotive.fm count`

Models a car with:

- Engine types (petrol, diesel, electric)
- Transmission (manual, automatic)
- Interior options (leather/cloth seats, heated seats)
- Safety features (ABS, airbags, lane assist)

### Web Server Configuration

Run: `cargo run --release -- -i examples/webserver.fm core`

Models a web server with:

- HTTP/HTTPS modules
- Database options (MySQL, PostgreSQL)
- Caching (Redis, Memcached)
- Load balancer
- Logging options

## Analysis Queries

### Statistics

Shows comprehensive statistics including:

- Number of features and constraints
- Number of valid configurations
- Configuration space coverage
- Core, dead, and optional features
- BDD size

### Core Features

Features that appear in **all** valid configurations (mandatory features).

### Dead Features

Features that appear in **no** valid configuration (impossible to select due to constraints).

### Optional Features

Features that are neither core nor dead (truly optional).

### Commonality

Percentage of valid configurations that include each feature.

### Relationship Checks

- **Mutual Exclusion**: Check if two features never appear together
- **Implication**: Check if selecting one feature requires another

## Performance

The BDD-based approach scales well:

- **Small models** (< 20 features): instant analysis
- **Medium models** (20-50 features): seconds
- **Large models** (50-100 features): depends on constraint structure

BDD size can be controlled with the `--bdd-size` parameter (default: 20 bits = 1M nodes).

### Benchmark Results

From testing the included examples:

```text
# Mobile phone: 120 valid configs out of 2048 possible (5.86% coverage)
$ cargo run --release -- -i examples/mobile.fm stats
Features:       11
Valid configs:  120
Core features:  2  (Base, Screen)
BDD size:       10 nodes

# Automotive: 16 features compressed to 22 BDD nodes
$ cargo run --release -- -i examples/automotive.fm stats
Features:       16
Core features:  4  (BaseCar, Engine, Transmission, Interior)
BDD size:       22 nodes
```

**Key insight**: BDDs provide exponential compression. 11 features (2048 possible configurations) → 10 nodes.

## Applications

Feature model analysis is used in:

- **Software Product Lines**: Automotive, embedded systems, cloud services
- **Configuration Management**: Build systems, deployment configurations
- **Variability Analysis**: Understanding dependencies and conflicts
- **Product Derivation**: Generating valid products from a product line

## Technical Details

### BDD Encoding

Each constraint type is encoded as follows:

- **Requires** (f1 → f2): `¬f1 ∨ f2`
- **Excludes** (f1 ⊕ f2): `¬(f1 ∧ f2)`
- **AtLeastOne**: Direct OR of all features
- **ExactlyOne**: AtLeastOne AND pairwise exclusion
- **Clause**: Direct OR of literals (supports negation)

All constraints are combined with AND operations to form the complete BDD representing all valid configurations.

### Query Implementation

All queries operate **symbolically** on the BDD:

- **Core features**: Check if `valid_configs ∧ ¬feature = ∅` (feature required everywhere)
- **Dead features**: Check if `valid_configs ∧ feature = ∅` (feature impossible)
- **Mutual exclusion**: Check if `valid_configs ∧ f1 ∧ f2 = ∅`
- **Implication**: Check if `valid_configs ∧ f1 ∧ ¬f2 = ∅`

No explicit enumeration needed - operates on millions of configurations efficiently.

### Implementation Modules

- **`model.rs`**: Feature model data structures (FeatureModel, Constraint enum)
- **`parser.rs`**: DIMACS CNF and simple text format parsers
- **`encoder.rs`**: Constraint-to-BDD encoding
- **`queries.rs`**: Analysis operations (11 different queries)
- **`main.rs`**: CLI interface with clap

## Extension Ideas

This implementation can be extended with:

1. **More constraint types**: Cardinality constraints (at-most-k, at-least-k)
2. **Optimization queries**: Find configuration minimizing/maximizing a cost function
3. **Diff analysis**: Compare two feature models, show added/removed features
4. **Export formats**: Generate valid configurations in JSON/YAML/TOML
5. **Interactive wizard**: Step-by-step configuration builder
6. **Benchmark suite**: Compare with SAT solvers (Z3, MiniSat), CSP solvers

## Research Context

Feature model analysis with BDDs is an active research area:

- Benavides et al. "Automated analysis of feature models 20 years later" (2010)
- Thüm et al. "A classification and survey of analysis strategies for software product lines" (2014)

This implementation demonstrates practical BDD applications in software engineering and can serve as:

- Teaching tool for BDD concepts
- Research platform for comparing symbolic techniques
- Production tool for configuration management
