# BDD Size Distribution

This document analyzes how BDD sizes are distributed across the space of Boolean functions.

## Overview

The **BDD size** of a Boolean function is the number of internal nodes in its reduced ordered BDD for a fixed variable ordering.

### Key Questions

1. What is the expected BDD size for a random Boolean function?
2. What does the distribution look like?
3. How rare are functions with small BDDs?
4. How does the distribution change with $n$?

## Theoretical Bounds

### Maximum BDD Size

For $n$ variables, the maximum BDD size is:

$$\text{max size} = 2^n - 1$$

This occurs for functions like the "middle bit" function.

### Minimum BDD Size

The minimum is 0, achieved only by the constant functions $f \equiv 0$ and $f \equiv 1$.

### Expected Size (Shannon's Bound)

For a random Boolean function on $n$ variables:

$$\mathbb{E}[\text{BDD size}] = \Theta\left(\frac{2^n}{n}\right)$$

More precisely, for large $n$:

$$\mathbb{E}[\text{BDD size}] \approx \frac{2^n}{n} \cdot \left(1 - o(1)\right)$$

## Distribution Shape

### Concentration

The BDD size of random functions is **concentrated** around its mean.

By a counting argument, for most functions:

$$\text{size}(f) \in \left[\frac{2^n}{2n}, \frac{2 \cdot 2^n}{n}\right]$$

Functions with BDD size $o(2^n / n)$ are extremely rare.

### Asymmetry

The distribution is **right-skewed**:

- Mode < Median < Mean
- Long right tail from functions with near-maximal BDD size
- Sharp cutoff on the left (size ≥ 0)

### Small Functions

Functions with small BDDs are combinatorially rare:

| Size $k$ | Meaning | Exact count for any $n$ |
|----------|---------|------------------------|
| 1 | Constants only | 2 |
| 2 | Variable projections | $2n$ |
| $k$ | General | $O((nk^2)^k)$ upper bound |

Compare to $2^{2^n}$ total functions!

Percentage of functions with size ≤ 2 (constants + projections):

| n | Size ≤ 2 | Total | Percentage |
|---|----------|-------|------------|
| 2 | 6 | 16 | 37.5% |
| 3 | 8 | 256 | 3.1% |
| 4 | 10 | 65,536 | 0.015% |
| 5 | 12 | ~4.3×10⁹ | ~2.8×10⁻⁷% |

Note: Size ≤ 2 means constants (2 functions) plus projections and their negations (2n functions), giving $2 + 2n$ total.

## Empirical Observations

**Note**: BDD size as reported here includes the terminal node, so:

- Constants (0 and 1) have size 1
- Single variable projections have size 2

### n = 2 (16 functions)

Complete enumeration:

| Size | Count | Percentage | Examples |
|------|-------|------------|----------|
| 1 | 2 | 12.50% | Constants 0, 1 |
| 2 | 4 | 25.00% | $x_1$, $\neg x_1$, $x_2$, $\neg x_2$ |
| 3 | 10 | 62.50% | AND, OR, XOR, NAND, NOR, etc. |

Mean: 2.50, Median: 3, Mode: 3

### n = 3 (256 functions)

Complete enumeration:

| Size | Count | Percentage |
|------|-------|------------|
| 1 | 2 | 0.78% |
| 2 | 6 | 2.34% |
| 3 | 30 | 11.72% |
| 4 | 98 | 38.28% |
| 5 | 120 | 46.88% |

Mean: 4.28, Median: 4, Mode: 5

### n = 4 (65,536 functions)

Complete enumeration:

| Size | Count | Percentage |
|------|-------|------------|
| 1 | 2 | 0.00% |
| 2 | 8 | 0.01% |
| 3 | 60 | 0.09% |
| 4 | 392 | 0.60% |
| 5 | 2,074 | 3.16% |
| 6 | 8,400 | 12.82% |
| 7 | 23,880 | 36.44% |
| 8 | 24,960 | 38.09% |
| 9 | 5,760 | 8.79% |

Mean: 7.34, Median: 7, Mode: 8

### n = 5 (~4.3 billion functions)

Monte Carlo sampling (100,000 samples):

| Size | Count | Percentage |
|------|-------|------------|
| 7 | 11 | 0.01% |
| 8 | 97 | 0.10% |
| 9 | 699 | 0.70% |
| 10 | 3,265 | 3.27% |
| 11 | 11,178 | 11.18% |
| 12 | 26,353 | 26.35% |
| 13 | 36,071 | 36.07% |
| 14 | 19,473 | 19.47% |
| 15 | 2,853 | 2.85% |

Mean: 12.63, Median: 13, Min: 7, Max: 15
95% CI for mean: [12.626, 12.640]

### Summary Across n

| n | Total Functions | Mean Size | Median | Mode | Max Observed |
|---|-----------------|-----------|--------|------|--------------|
| 2 | 16 | 2.50 | 3 | 3 | 3 |
| 3 | 256 | 4.28 | 4 | 5 | 5 |
| 4 | 65,536 | 7.34 | 7 | 8 | 9 |
| 5 | ~4.3×10⁹ | 12.63 | 13 | 13 | 15 |

## Functions with Extreme BDD Size

### Smallest BDDs (size 1-3)

- **Size 1**: Constants only (0 and 1) — just the terminal node
- **Size 2**: Single variable projections and their negations ($x_i$, $\neg x_i$)
- **Size 3**: Simple gates (AND, OR, XOR, NAND, NOR of 2 variables)

These have highly regular structure.

### Largest BDDs

Observed maximum sizes:

| n | Theoretical Max ($2^n - 1$) | Observed Max |
|---|----------------------------|--------------|
| 2 | 3 | 3 |
| 3 | 7 | 5 |
| 4 | 15 | 9 |
| 5 | 31 | 15 (in 100k samples) |

Functions with near-maximal BDD size are characterized by:

- High sensitivity (many variables matter)
- Little internal structure to exploit
- "Random-looking" truth tables

Note: The observed maximum is less than the theoretical maximum because:

1. Functions achieving the theoretical maximum are extremely rare
2. For n=5, we only sampled 100k out of ~4.3 billion functions

## Variable Ordering Effects

BDD size depends critically on variable ordering. For the same function:

- Best ordering: $O(n)$ for some functions
- Worst ordering: $O(2^n)$ for the same functions

Example: The "middle bit" adder has:

- Linear size with optimal ordering
- Exponential size with worst ordering

For random functions, all orderings give similar size (within constant factors).

## Correlation with Other Measures

### Minterm Count

**Observation**: BDD size has weak correlation with minterm count.

- Balanced functions (50% minterms) tend to have larger BDDs
- Very sparse or very dense functions tend to have smaller BDDs

### Sensitivity

Higher sensitivity correlates with larger BDD size, but the relationship is not deterministic.

### Algebraic Degree

Functions with low algebraic degree tend to have smaller BDDs, but this is not a tight bound.

## Implications

### For BDD Users

1. Most functions have large BDDs — small BDDs are special
2. If a function has a small BDD, it has exploitable structure
3. Variable ordering matters enormously for some functions

### For Analysis

1. Monte Carlo sampling is necessary for $n > 4$
2. Distribution is concentrated — moderate sample sizes suffice
3. Tail bounds are useful for guarantees

## References

1. R. Bryant, "On the Complexity of VLSI Implementations and Graph Representations of Boolean Functions"
2. I. Wegener, "Branching Programs and Binary Decision Diagrams"
3. S. Jukna, "Boolean Function Complexity"
