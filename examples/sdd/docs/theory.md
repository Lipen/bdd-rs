# Sentential Decision Diagrams: Theory

## Introduction

Sentential Decision Diagrams (SDDs) are a **canonical representation** of propositional formulas that support **tractable logical operations**. Introduced by Adnan Darwiche in 2011, SDDs generalize Ordered Binary Decision Diagrams (OBDDs) while often providing more compact representations.

## Formal Definition

### Vtree (Variable Tree)

A **vtree** for a set of variables $X = \{x_1, \ldots, x_n\}$ is a full binary tree whose leaves are the variables in $X$. Each internal node $v$ partitions the variables into:

- **Left variables**: $\text{vars}(v_L)$ — variables in the left subtree
- **Right variables**: $\text{vars}(v_R)$ — variables in the right subtree

The vtree structure determines the SDD's decomposition.

### SDD Nodes

An SDD normalized for a vtree node $v$ takes one of these forms:

1. **Terminal nodes**:
   - $\top$ (true) — satisfied by all assignments
   - $\bot$ (false) — satisfied by no assignment

2. **Literal nodes**: A variable $x_i$ or its negation $\neg x_i$

3. **Decision nodes**: A disjunction of (prime, sub) pairs:
   $$\{(p_1, s_1), (p_2, s_2), \ldots, (p_k, s_k)\}$$

   This represents: $(p_1 \land s_1) \lor (p_2 \land s_2) \lor \cdots \lor (p_k \land s_k)$

   Where:
   - Each $p_i$ (prime) is an SDD over left variables
   - Each $s_i$ (sub) is an SDD over right variables
   - Primes form a **partition** of $\top$: mutually exclusive and exhaustive

### Canonical Properties

For SDDs to be canonical (unique per function), they must satisfy:

1. **Compression**: No two elements share the same sub
   $$\forall i \neq j: s_i \neq s_j$$

2. **Trimming**: No element has sub equal to $\bot$
   $$\forall i: s_i \neq \bot$$

3. **Normalization**: The SDD is normalized for a specific vtree

## The Apply Algorithm

The core operation for combining SDDs is the **apply** algorithm. Given SDDs $\alpha$ and $\beta$ normalized for vtree node $v$, we compute $\alpha \circ \beta$ (for operations like $\land$, $\lor$, $\oplus$):

```
Apply(α, β, op, v):
    // Terminal cases
    if α and β are terminals:
        return op(α, β)

    // Get elements
    let {(p₁, s₁), ..., (pₘ, sₘ)} = elements(α, v)
    let {(q₁, t₁), ..., (qₙ, tₙ)} = elements(β, v)

    // Combine all pairs
    result = {}
    for each (pᵢ, sᵢ) in α:
        for each (qⱼ, tⱼ) in β:
            new_prime = Apply(pᵢ, qⱼ, AND, v_L)
            if new_prime ≠ ⊥:
                new_sub = Apply(sᵢ, tⱼ, op, v_R)
                result.add((new_prime, new_sub))

    return Compress(result)
```

Time complexity: $O(|α| \cdot |β|)$ per vtree node, polynomial overall.

## Model Counting

SDDs support **tractable weighted model counting (WMC)**:

Given weight functions $w^+: X \to \mathbb{R}$ (weight of positive literal) and $w^-: X \to \mathbb{R}$ (weight of negative literal), the weighted model count is:

$$\text{WMC}(f) = \sum_{m \models f} \prod_{x_i \in m} w^+(x_i) \cdot \prod_{x_i \notin m} w^-(x_i)$$

For SDDs, this can be computed in **O(|SDD|)** time:

```
WMC(node):
    if node = ⊤: return 1
    if node = ⊥: return 0
    if node = literal(x, polarity):
        return w⁺(x) if polarity else w⁻(x)
    if node = decision{elements}:
        return Σᵢ WMC(pᵢ) × WMC(sᵢ)
```

## Comparison with BDDs

| Property | BDD | SDD |
|----------|-----|-----|
| Decomposition | If-then-else (Shannon) | (prime, sub) partition |
| Variable structure | Linear ordering | Binary tree (vtree) |
| Canonicity | Per variable order | Per vtree |
| Size relationship | — | BDD ⊆ SDD (every BDD is an SDD) |
| Best case | Functions matching order | Hierarchical functions |

SDDs can be **exponentially more succinct** than BDDs for certain functions, particularly those with natural hierarchical structure.

## Key Theorems

### Succinctness

**Theorem (Darwiche, 2011)**: For any variable ordering $\pi$, there exists a vtree such that the SDD size is at most the OBDD size under $\pi$.

**Corollary**: SDDs are at least as succinct as OBDDs.

### Canonicity

**Theorem**: For a fixed vtree, every Boolean function has exactly one reduced, normalized SDD.

### Tractability

SDDs support the following operations in polynomial time:

- Conjunction (∧)
- Disjunction (∨)
- Negation (¬)
- Model counting
- Satisfiability checking
- Forgetting (existential quantification)

## References

1. Darwiche, A. (2011). SDD: A New Canonical Representation of Propositional Knowledge Bases. *Proceedings of IJCAI-11*, 819-826.

2. Darwiche, A., & Marquis, P. (2002). A Knowledge Compilation Map. *Journal of Artificial Intelligence Research*, 17, 229-264.

3. Choi, A., & Darwiche, A. (2013). Dynamic Minimization of Sentential Decision Diagrams. *Proceedings of AAAI-13*, 187-194.
