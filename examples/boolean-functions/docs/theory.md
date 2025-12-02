# Boolean Function Theory

This document provides the theoretical foundation for understanding the landscape of Boolean functions.

## What is a Boolean Function?

A **Boolean function** of $n$ variables is a mapping $f: \{0,1\}^n \to \{0,1\}$.

Each Boolean function can be uniquely represented by its **truth table** — a vector of $2^n$ bits that specifies the output for each possible input.

### Counting Boolean Functions

For $n$ variables:

- There are $2^n$ possible inputs
- Each input can map to 0 or 1
- Therefore, there are $2^{2^n}$ distinct Boolean functions

This is **double-exponential growth**:

| n | Inputs ($2^n$) | Functions ($2^{2^n}$) |
|---|----------------|----------------------|
| 1 | 2 | 4 |
| 2 | 4 | 16 |
| 3 | 8 | 256 |
| 4 | 16 | 65,536 |
| 5 | 32 | 4,294,967,296 |
| 6 | 64 | ~$1.8 \times 10^{19}$ |
| 7 | 128 | ~$3.4 \times 10^{38}$ |

Beyond $n = 5$, exhaustive enumeration becomes impractical.

## Representations of Boolean Functions

### Truth Table

The most direct representation. For $n$ variables, store $2^n$ bits.

Example for $f(x_1, x_2) = x_1 \land x_2$:

| $x_2$ | $x_1$ | $f$ |
|-------|-------|-----|
| 0 | 0 | 0 |
| 0 | 1 | 0 |
| 1 | 0 | 0 |
| 1 | 1 | 1 |

Truth table (reading bottom-to-top): `1000` = 8 in decimal.

### Algebraic Normal Form (ANF)

Every Boolean function can be written as a polynomial over $\mathbb{F}_2$ (the field with two elements):

$$f(x_1, \ldots, x_n) = \bigoplus_{S \subseteq \{1,\ldots,n\}} a_S \prod_{i \in S} x_i$$

where $a_S \in \{0, 1\}$ and $\oplus$ denotes XOR.

The **algebraic degree** is the size of the largest set $S$ with $a_S = 1$.

### Binary Decision Diagram (BDD)

A BDD is a directed acyclic graph with:

- Two terminal nodes: $\bot$ (false) and $\top$ (true)
- Internal nodes labeled with variables
- Each internal node has two outgoing edges: low (0) and high (1)

For a fixed variable ordering, the **reduced ordered BDD (ROBDD)** is canonical — each Boolean function has exactly one representation.

## Special Classes of Boolean Functions

### Symmetric Functions

A function is **symmetric** if its output depends only on the Hamming weight (number of 1s) of the input, not on which variables are set.

Examples:

- AND: $f = 1$ iff all inputs are 1
- OR: $f = 1$ iff at least one input is 1
- Parity: $f = 1$ iff odd number of 1s
- Threshold: $f = 1$ iff at least $k$ inputs are 1

For $n$ variables, there are $2^{n+1}$ symmetric functions.

### Monotone Functions

A function is **monotone** if increasing any input can only increase the output:

$$x \leq y \implies f(x) \leq f(y)$$

The number of monotone functions is the **Dedekind number** $D(n)$, which grows super-exponentially but slower than all functions.

### Linear Functions

A function is **linear** (affine) if it can be written as:

$$f(x_1, \ldots, x_n) = a_0 \oplus a_1 x_1 \oplus \cdots \oplus a_n x_n$$

There are exactly $2^{n+1}$ linear functions. These have the smallest possible BDDs (size $n$ or less).

### Balanced Functions

A function is **balanced** if exactly half of its outputs are 1:

$$|f^{-1}(1)| = 2^{n-1}$$

**How many Boolean functions are balanced?**

The number of balanced functions on $n$ variables is:

$$\binom{2^n}{2^{n-1}}$$

since we choose which $2^{n-1}$ of the $2^n$ inputs map to 1.

The fraction of balanced functions is:

$$\frac{\binom{2^n}{2^{n-1}}}{2^{2^n}}$$

**Stirling approximation**: For large $N$, $\binom{N}{N/2} \approx \frac{2^N}{\sqrt{\pi N / 2}}$.

Let $N = 2^n$. Then:

$$\binom{2^n}{2^{n-1}} \approx \frac{2^{2^n}}{\sqrt{\pi \cdot 2^{n-1}}}$$

So the fraction of balanced functions is approximately:

$$\frac{1}{\sqrt{\pi \cdot 2^{n-1}}} = \sqrt{\frac{2}{\pi}} \cdot 2^{-n/2}$$

**As $n \to \infty$, this fraction tends to 0.**

| n | Fraction of balanced functions |
|---|-------------------------------|
| 2 | ~56% |
| 3 | ~27% |
| 4 | ~14% |
| 5 | ~7% |
| 10 | ~1.1% |
| 20 | ~0.03% |

**Almost no Boolean functions are balanced!** The balanced functions, while numerous in absolute count, become vanishingly rare as $n$ grows.

## Complexity Measures

### BDD Size

The **BDD size** is the number of internal nodes in the reduced ordered BDD. This depends on the variable ordering.

- Minimum possible: 0 (for constants)
- Maximum possible: $2^n - 1$ (for pathological functions)

For a **random** Boolean function, Shannon's counting argument gives:

$$\text{Expected BDD size} = \Theta\left(\frac{2^n}{n}\right)$$

### Sensitivity and Influence

The **sensitivity** of a function at input $x$ is the number of variables $i$ such that $f(x) \neq f(x^{\oplus i})$ where $x^{\oplus i}$ differs from $x$ only in bit $i$.

The **influence** of variable $i$ is:

$$I_i(f) = \Pr_x[f(x) \neq f(x^{\oplus i})]$$

The **total influence** is $I(f) = \sum_i I_i(f)$.

## Shannon's Counting Argument

**Theorem (Shannon)**: Almost all Boolean functions on $n$ variables have BDD size $\Omega(2^n / n)$ for any variable ordering.

**Proof sketch**:

1. **Count BDDs with at most $m$ nodes**:
   Each internal node requires:
   - A variable label: $n$ choices
   - A low child: at most $m + 2$ choices (any of $m$ nodes, or terminals $\bot$, $\top$)
   - A high child: at most $m + 2$ choices

   So the number of labeled DAGs with $m$ nodes is at most:
   $$n^m \cdot (m+2)^{2m} \leq (n(m+2)^2)^m$$

   For large $m$, this is roughly $O((nm^2)^m)$ or more loosely $O((nm)^{2m})$.

2. **Count Boolean functions**: $2^{2^n}$

3. **Pigeonhole principle**: If all functions had BDDs of size $\leq m$, we'd need:
   $$(nm^2)^m \geq 2^{2^n}$$

4. **Taking logs**: $m \log(nm^2) \geq 2^n$, which gives $m = \Omega(2^n / \log(nm^2))$

5. **For $m \ll 2^n$**: The $\log(nm^2)$ term is $O(n + \log m) = O(n)$, so $m = \Omega(2^n / n)$

**Implication**: Most Boolean functions have exponentially large BDDs. Small BDDs are the exception, not the rule.

## Random Boolean Functions

A **uniformly random** Boolean function assigns each output bit independently with probability 1/2.

Properties of random functions:

- Expected number of minterms: $2^{n-1}$
- With high probability, balanced (by Chernoff)
- With high probability, has large BDD size
- With high probability, has sensitivity $\Theta(n/2)$

## References

1. D. E. Knuth, "The Art of Computer Programming, Volume 4A: Combinatorial Algorithms"
2. I. Wegener, "BDDs: Design, Analysis, Complexity, and Applications"
3. R. Bryant, "Graph-Based Algorithms for Boolean Function Manipulation"
4. C. Shannon, "A Mathematical Theory of Communication"
