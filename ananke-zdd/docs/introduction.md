# Introduction to Zero-Suppressed Decision Diagrams

## The Problem They Solve

Suppose you want to represent "all valid 8-Queens solutions." There are exactly 92 solutions on an 8×8 board.

**Naive approach**: Store all 92 solutions as bit vectors (one per queen position).

- Storage: 92 × 64 bits = 5,888 bits
- Problem: What about all the *invalid* placements? The representation carries no structure.

**BDD approach**: Build a binary decision tree encoding the constraints.

- Potentially exponential: 2^64 nodes in the worst case
- Reality: BDDs compress well for many problems, but this particular problem (constraint satisfaction with positional variables) creates large intermediate BDDs

**ZDD approach**: Represent the 92 solutions as a family of sets, exploiting a mathematical property called **zero-suppression**.

- For N-Queens: 373 nodes (8×8 board)
- Property: Directly encodes "which positions are occupied" rather than "which queen is at which row"
- Compact: Because most positions are unoccupied, the structure is sparse

## What Are ZDDs?

A **ZDD** (Zero-Suppressed Decision Diagram) is a DAG (directed acyclic graph) that represents a **family of sets**.

**Formal definition**: A ZDD is a rooted DAG where:

- Each non-terminal node is labeled with a variable v and has two edges: **lo** (sets without v) and **hi** (sets with v)
- There are two terminal nodes: **⊥** (empty family: ∅) and **⊤** (family containing only ∅: {∅})
- **Zero-suppression rule**: Any node where `hi = ⊥` is eliminated (replaced by its `lo` child)

**Why this matters**: The zero-suppression rule means we never represent "sets that definitely don't contain this variable" separately. This is fundamentally different from BDDs and makes ZDDs perfect for sparse set families.

### Simple Example

Let's represent: F = {{}, {1}, {2}, {1,2}}

```
             ┌──────┐
             │ Var1 │
             └─┬─┬──┘
               │ │
            lo │ │ hi
             ┌─┴─┴──┐
             │ Var2 │
             └─┬─┬──┘
               │ │
            lo │ │ hi
            ┌──┴─┴──┐
            │ ┌───┐ │
            └─│⊤ ⊥│─┘
              └───┘

Reading paths:
- ∅        : go lo from Var1, lo from Var2 → ⊤
- {1}      : go hi from Var1, lo from Var2 → ⊤
- {2}      : go lo from Var1, hi from Var2 → ⊤
- {1,2}    : go hi from Var1, hi from Var2 → ⊤
- Any path ending at ⊥ represents a set NOT in the family
```

The ZDD has only 2 nodes (plus terminals). A naive representation would need 4 separate entries.

## Key Properties

### 1. Canonicity

Each family of sets has **exactly one** ZDD representation (given a fixed variable ordering). This means:

- Two ZDDs are equal if and only if they represent the same family
- We can safely cache and reuse computed results

### 2. Sparsity Exploitation

The zero-suppression rule specifically targets sparse families:

- If most sets are missing a variable, that variable's node is eliminated
- For combinatorial problems (subsets, partitions), this creates exponentially smaller representations than alternatives

### 3. Natural Operations

Set operations map directly to ZDD structure:

- **Union**: Merge two families
- **Intersection**: Keep only common sets
- **Join**: $\{ S \cup T \mid S \in F, T \in G \}$ - the cross product, fundamental for combinatorics
- **Change**: Toggle a variable in all sets
- **Onset/Offset**: Filter by membership

## ZDDs vs BDDs vs Other Data Structures

| Property | ZDD | BDD | Trie | Hash Table |
|----------|-----|-----|------|------------|
| **Set family operations** | Native O(n) | Requires encoding | Slower search | No structure |
| **Canonicity** | ✓ | ✓ | ✗ | ✗ |
| **Sparse families** | Excellent | Good | Fair | Poor |
| **Dense families** | Poor | Better | Fair | Good |
| **Join operation** | Fast | Awkward | Slow | Not applicable |
| **Constraint solving** | Needs encoding | Native | N/A | N/A |

**When to use ZDDs:**

- You have a family of sets (not just one set)
- The family is relatively sparse
- You need flexible operations (union, intersection, join)
- You need to enumerate all sets

**When NOT to use ZDDs:**

- Dense families (use hash tables)
- Single sets (use bit vectors)
- Need constraint satisfaction directly (use SAT solvers with BDD backend)

## Design Philosophy

This implementation (ananke-zdd) follows principles learned from decades of BDD research:

1. **Hash consing**: Identical nodes are shared, enabling structural sharing
2. **Memoization**: Cache operation results to avoid recomputation
3. **Per-level subtables**: Fast O(1) node lookup within each variable level
4. **Manager-centric design**: All operations go through the manager; nodes are opaque references
5. **Composability**: Complex operations build from simple primitives (union, intersection, join)

## Complexity Analysis

For a ZDD representing n variables and m sets:

| Operation | Time | Space |
|-----------|------|-------|
| Base set construction | O(1) | O(1) |
| Union/Intersection | O(nm) | O(nm) |
| Join (cross product) | O(n²m) | O(n²m) |
| Counting sets | O(n) | O(n) |
| Enumerate all sets | O(n + m) | O(n) |
| Member test | O(n) | O(1) |

These are *typical* complexities; actual performance depends on the structure of your specific families.

---

Next: [Deep dive into theory →](theory.md)
