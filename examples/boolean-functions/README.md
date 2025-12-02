# Boolean Functions

Exploring the Boolean function space via BDD size distribution analysis.

## Overview

For `n` variables, there are `2^(2^n)` distinct Boolean functions — a double-exponential growth that makes exhaustive enumeration infeasible beyond small `n`.

This case study uses Monte Carlo sampling with statistical analysis to characterize:

- Distribution of BDD sizes across random Boolean functions
- Statistical bounds using Chebyshev, Hoeffding, CLT, and bootstrap methods
- Structural properties of typical vs. extremal functions

## Structure

```
src/
  lib.rs       — Module exports
  function.rs  — Truth table representation and BDD construction
  stats.rs     — Statistical analysis (CI, bootstrap, tail bounds)
  sampling.rs  — Monte Carlo sampling strategies
  analysis.rs  — Size distribution analysis and theoretical bounds
  viz.rs       — ASCII visualization utilities (histograms, sparklines)

examples/
  exhaustive.rs  — Exhaustive enumeration for n ≤ 4
  monte_carlo.rs — Monte Carlo sampling with confidence intervals
  explore.rs     — Find functions with extreme BDD sizes
  statistics.rs  — Demonstrate statistical analysis methods
```

## Quick Start

```bash
# Exhaustive enumeration for n=3 (256 functions)
cargo run -p boolean-functions --release --example exhaustive -- -n 3

# Monte Carlo sampling for n=5 (4 billion functions)
cargo run -p boolean-functions --release --example monte_carlo -- -n 5 -s 10000

# Find functions with extreme BDD sizes
cargo run -p boolean-functions --release --example explore -- -n 4 --exhaustive

# Demonstrate statistical methods
cargo run -p boolean-functions --release --example statistics -- -n 4 -s 5000
```

## Examples

### Exhaustive Enumeration

For small `n` (≤ 4), enumerate all functions:

```bash
cargo run -p boolean-functions --release --example exhaustive -- -n 4 -v
```

Output includes complete size distribution, statistics, and histogram.

### Monte Carlo Sampling

For larger `n`, use statistical sampling:

```bash
cargo run -p boolean-functions --release --example monte_carlo -- -n 6 -s 50000 --seed 42
```

Provides confidence intervals via CLT, t-distribution, and bootstrap.

### Statistical Analysis

Demonstrates confidence intervals, tail bounds, and sample size planning:

```bash
cargo run -p boolean-functions --release --example statistics -- -n 5 -s 10000 -v
```

## Key Results

| n | Total Functions | Mean BDD Size | Mode | Max Observed |
|---|-----------------|---------------|------|--------------|
| 2 | 16 | 2.50 | 3 | 3 |
| 3 | 256 | 4.28 | 5 | 5 |
| 4 | 65,536 | 7.34 | 8 | 9 |
| 5 | ~4.3×10⁹ | 12.63 | 13 | 15 |

## Key Facts

- Total functions on n variables: `2^(2^n)`
- Expected BDD size for random function: `Θ(2^n / n)` (Shannon)
- Most functions have "large" BDDs — small BDDs are rare
- Distribution is concentrated and slightly left-skewed
