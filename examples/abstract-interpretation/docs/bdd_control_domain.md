# BDD Control Domain: Formal Design & Specification

**Date:** November 18, 2025
**Status:** Design Phase
**Author:** Research Team

---

## 1. Motivation & Problem Statement

### 1.1 The Problem: Path-Insensitive Numeric Analysis

Consider this simple program:

```c
int x = 0;
bool flag = true;

if (flag) {
    x = 5;      // Path 1: x = 5
} else {
    x = -10;    // Path 2: x = -10
}

// What is x here?
```

**Path-Insensitive Analysis (Current Approach):**

- Interval domain: `x ∈ [-10, 5]`
- Sign domain: `x ∈ Top` (could be negative, zero, or positive)
- **Problem:** Imprecise! We know `x ≠ 0` and the flag determines which path.

**Path-Sensitive Analysis (Goal):**

- When `flag = true`: `x = 5` (Sign: Pos, Interval: [5,5])
- When `flag = false`: `x = -10` (Sign: Neg, Interval: [-10,-10])
- **Benefit:** Separate invariants per control path → precise!

### 1.2 The Solution: BDD-Guided Partitioning

**Key Insight:** Use BDDs to represent Boolean control state, partition numeric invariants by control state.

**Domain Structure:**

```text
D = BDD(control) × NumericDomain(data)

State = Map[BDD → NumericElement]
```

Each BDD represents a set of control paths, each with its own numeric invariant.

---

## 2. Formal Semantics

### 2.1 Control State Representation

**Definition 2.1 (Boolean Control Variables):**
A program has a finite set of Boolean control variables:

- `CV = {b₁, b₂, ..., bₙ}` where each `bᵢ ∈ {true, false}`

**Examples:**

- Branch conditions: `flag`, `is_active`, `error`
- Mode indicators: `mode == INIT`, `state == READY`
- Phase markers: `initialized`, `locked`

**Definition 2.2 (Control State):**
A control state `c ∈ 2^CV` is an assignment of truth values to control variables.

**Representation:** BDD `φ: 2^CV → {0,1}`

- `φ = 1` (BDD true) represents the constraint "this path is reachable"
- `φ = 0` (BDD false) represents "unreachable/infeasible path"

### 2.2 Abstract Domain Definition

**Definition 2.3 (BDD Control Domain):**

The BDD Control Domain `D_BDD` is defined as:

```text
D_BDD = (E_BDD, ⊑, ⊔, ⊓, ∇, ⊥, ⊤)
```

Where:

- **Elements:** `E_BDD = {φ | φ is a BDD over CV}`
- **Partial Order:** `φ₁ ⊑ φ₂ ⟺ φ₁ ⇒ φ₂` (logical implication)
- **Join:** `φ₁ ⊔ φ₂ = φ₁ ∨ φ₂` (disjunction)
- **Meet:** `φ₁ ⊓ φ₂ = φ₁ ∧ φ₂` (conjunction)
- **Widening:** `φ₁ ∇ φ₂ = φ₁ ∨ φ₂` (same as join, finite height)
- **Bottom:** `⊥ = false` (unreachable)
- **Top:** `⊤ = true` (all paths reachable)

**Lemma 2.1 (Complete Lattice):**
`(D_BDD, ⊑)` forms a complete lattice with finite height `2^|CV|`.

*Proof:* Boolean formulas over `n` variables have at most `2^n` distinct equivalence classes under logical equivalence. The lattice has finite ascending chains, guaranteeing termination. □

### 2.3 Product Domain with Numeric Invariants

**Definition 2.4 (Control-Flow Sensitive Product Domain):**

Given a numeric domain `D_NUM = (E_NUM, ⊑_NUM, ⊔_NUM, ...)`, define:

```text
D_PROD = D_BDD × D_NUM
```

**Elements:**

```text
E_PROD = Map[BDD → E_NUM]
```

Each element `M ∈ E_PROD` maps control states (BDDs) to numeric invariants.

**Interpretation:**

- `M(φ) = e` means "when control state satisfies `φ`, numeric state is `e`"
- Disjoint control states have independent numeric invariants
- Overlapping control states must join their numeric invariants

**Example:**

| Control State (BDD) | Numeric Invariant |
|---------------------|-------------------|
| `flag = true` | `x ∈ [5, 5]` |
| `flag = false` | `x ∈ [-10, -10]` |
| `true` (both paths) | `x ∈ [-10, 5]` |

### 2.4 Lattice Operations on Product Domain

**Definition 2.5 (Product Lattice Operations):**

Given `M₁, M₂ ∈ E_PROD`:

1. **Bottom:**

   ```text
   ⊥_PROD = λφ. ⊥_NUM
   ```

   All control states map to numeric bottom (unreachable).

2. **Top:**

   ```text
   ⊤_PROD = {true ↦ ⊤_NUM}
   ```

   All control states merged, numeric top (unknown).

3. **Partial Order:** `M₁ ⊑ M₂` iff:

   ```text
   ∀φ₁ ∈ dom(M₁). ∃φ₂ ∈ dom(M₂).
       (φ₁ ⇒ φ₂) ∧ (M₁(φ₁) ⊑_NUM M₂(φ₂))
   ```

   *Intuition:* Every control path in `M₁` is covered by a more general path in `M₂` with a looser numeric invariant.

4. **Join:** `M₁ ⊔ M₂ = merge(M₁, M₂)` where:

   ```text
   For each (φ₁, e₁) ∈ M₁ and (φ₂, e₂) ∈ M₂:
       - If φ₁ ∧ φ₂ = false: keep both entries
       - If φ₁ ∧ φ₂ ≠ false: create entry (φ₁ ∨ φ₂) ↦ (e₁ ⊔_NUM e₂)
   ```

   *Intuition:* Merge overlapping control paths, join their numeric invariants.

5. **Meet:** `M₁ ⊓ M₂` intersects control states:

   ```text
   {(φ₁ ∧ φ₂) ↦ (e₁ ⊓_NUM e₂) | (φ₁, e₁) ∈ M₁, (φ₂, e₂) ∈ M₂, φ₁ ∧ φ₂ ≠ false}
   ```

**Theorem 2.1 (Soundness):**
The product domain `D_PROD` forms a complete lattice with finite ascending chains.

*Proof Sketch:* BDD domain has finite height. Numeric domain must be chosen with widening to ensure termination. Product inherits both properties. □

---

## 3. Transfer Functions

### 3.1 Control Variable Assignment

**Operation:** `b := expr` where `b ∈ CV` and `expr` is a Boolean expression.

**Semantics:**

```rust
fn assign_control(M: Map[BDD → NumericElem], var: &str, expr: BoolExpr)
    -> Map[BDD → NumericElem]
{
    let mut result = Map::new();

    for (φ, e) in M {
        // Evaluate expr in context φ
        match eval_bool(expr, φ) {
            Some(true) => {
                // expr is definitely true: set var to true
                let φ_new = φ ∧ (var = true);
                result.insert(φ_new, e);
            }
            Some(false) => {
                // expr is definitely false: set var to false
                let φ_new = φ ∧ (var = false);
                result.insert(φ_new, e);
            }
            None => {
                // expr is unknown: split into both cases
                let φ_true = φ ∧ (var = true);
                let φ_false = φ ∧ (var = false);
                result.insert(φ_true, e.clone());
                result.insert(φ_false, e);
            }
        }
    }

    result
}
```

**Example:**

```text
Before: {true ↦ x ∈ [0, 10]}
Assign: flag := (x > 5)

After: {
    (flag = true) ∧ (x > 5) ↦ x ∈ [6, 10],
    (flag = false) ∧ (x ≤ 5) ↦ x ∈ [0, 5]
}
```

### 3.2 Numeric Variable Assignment (Control-Sensitive)

**Operation:** `x := expr` where `x` is numeric, `expr` is a numeric expression.

**Semantics:**

```rust
fn assign_numeric(M: Map[BDD → NumericElem], var: &str, expr: NumExpr)
    -> Map[BDD → NumericElem]
{
    M.map(|(φ, e)| {
        // Evaluate numeric expr in context e
        let e_new = numeric_domain.assign(e, var, expr);
        (φ, e_new)
    })
}
```

**Key Insight:** Numeric assignments don't affect control state partitioning!

**Example:**

```text
Before: {
    flag = true ↦ x ∈ [0, 10],
    flag = false ↦ x ∈ [-5, 5]
}
Assign: x := x + 1

After: {
    flag = true ↦ x ∈ [1, 11],
    flag = false ↦ x ∈ [-4, 6]
}
```

### 3.3 Conditional (Assume)

**Operation:** `assume(cond)` refines the state with constraint `cond`.

**Two Cases:**

1. **Pure Control Condition:** `assume(b)` where `b ∈ CV`

   ```rust
   fn assume_control(M: Map[BDD → NumericElem], var: &str)
       -> Map[BDD → NumericElem]
   {
       M.filter_map(|(φ, e)| {
           let φ_refined = φ ∧ var;
           if φ_refined == false { None } else { Some((φ_refined, e)) }
       })
   }
   ```

2. **Numeric Condition:** `assume(x < 10)`

   ```rust
   fn assume_numeric(M: Map[BDD → NumericElem], pred: NumPred)
       -> Map[BDD → NumericElem]
   {
       M.map(|(φ, e)| {
           let e_refined = numeric_domain.assume(e, pred);
           (φ, e_refined)
       })
   }
   ```

3. **Mixed Condition:** `assume(b && x < 10)`

   ```rust
   fn assume_mixed(M: Map[BDD → NumericElem],
                   control_part: BoolExpr,
                   numeric_part: NumPred)
       -> Map[BDD → NumericElem]
   {
       let M1 = assume_control(M, control_part);
       assume_numeric(M1, numeric_part)
   }
   ```

**Example (Control Refinement):**

```text
Before: {true ↦ x ∈ [0, 10]}
Assume: flag = true

After: {flag = true ↦ x ∈ [0, 10]}
```

**Example (Numeric Refinement):**

```text
Before: {
    flag = true ↦ x ∈ [0, 10],
    flag = false ↦ x ∈ [0, 10]
}
Assume: x > 5

After: {
    flag = true ↦ x ∈ [6, 10],
    flag = false ↦ x ∈ [6, 10]
}
```

---

## 4. Partition Management

### 4.1 Partition Explosion Problem

**Problem:** After many branches, we may have exponentially many partitions.

**Example:**

```c
if (b1) { ... }  // 2 partitions
if (b2) { ... }  // 4 partitions
if (b3) { ... }  // 8 partitions
...
if (b10) { ... } // 1024 partitions!
```

**Solutions:**

1. **Partition Merging (Widening in Control Space):**
   - When partition count exceeds threshold `K`, merge similar partitions
   - Strategy: Merge partitions with similar numeric invariants

2. **BDD Variable Ordering:**
   - Use FORCE/SIFTING algorithms to minimize BDD size
   - Group related control variables together

3. **Selective Tracking:**
   - Only track "relevant" control variables
   - Relevance: control variable appears in conditions affecting numeric variables

### 4.2 Partition Merging Algorithm

**Algorithm 4.1 (Partition Merging):**

```rust
fn merge_partitions(M: Map[BDD → NumericElem], threshold: usize)
    -> Map[BDD → NumericElem]
{
    if M.len() <= threshold {
        return M; // No merging needed
    }

    // Find two most similar partitions
    let (φ₁, e₁, φ₂, e₂) = find_most_similar(M);

    // Merge them
    let φ_merged = φ₁ ∨ φ₂;
    let e_merged = e₁ ⊔_NUM e₂;

    // Replace in map
    let mut M_new = M.remove(φ₁).remove(φ₂);
    M_new.insert(φ_merged, e_merged);

    // Recurse if still too many
    merge_partitions(M_new, threshold)
}

fn find_most_similar(M: Map[BDD → NumericElem])
    -> (BDD, NumericElem, BDD, NumericElem)
{
    // Heuristics:
    // 1. Smallest numeric distance (e.g., interval width difference)
    // 2. Most overlapping control states (BDD intersection size)
    // 3. Least recently created partitions
    ...
}
```

### 4.3 Partition Size Metrics

**Definition 4.1 (Partition Complexity):**

Given `M = {(φ₁, e₁), ..., (φₖ, eₖ)}`:

1. **Partition Count:** `|M| = k`
2. **BDD Complexity:** `size(M) = Σᵢ |nodes(φᵢ)|`
3. **Numeric Complexity:** `cost(M) = Σᵢ cost_NUM(eᵢ)`

**Target Bounds:**

- Partition count: `|M| ≤ 100` (configurable)
- BDD size: `size(M) ≤ 10,000 nodes`
- Total memory: `< 100 MB`

---

## 4.5 Deep Connection: BDDs, Shannon Expansion, and ITE

### 4.5.1 The Insight: Maps as Generalized ITEs

**Observation:** The partition representation `Map[BDD → NumericElem]` is isomorphic to a generalized if-then-else (ITE) structure.

**Example:**

```text
Current representation (Map):
{
    flag = true  ↦ x ∈ [0, 10],
    flag = false ↦ x ∈ [-5, 5]
}

Equivalent ITE representation:
ITE(flag,
    x ∈ [0, 10],      // then-branch
    x ∈ [-5, 5]       // else-branch
)

Shannon Expansion (BDD basis):
f(x₁,...,xₙ) = x₁ · f(1,x₂,...,xₙ) + x̄₁ · f(0,x₂,...,xₙ)
               ↑                      ↑
               then-branch            else-branch
```

**SMT-LIB Form:**

```smtlib
(ite flag
     (and (>= x 0) (<= x 10))
     (and (>= x -5) (<= x 5)))
```

### 4.5.2 Why Not Use BDD Nodes Directly?

**The Natural Question:** Since BDDs already encode ITE structures internally, why maintain a separate `Map[BDD → Value]`? Why not embed values directly in BDD nodes?

**Answer:** We hit fundamental **type system and algorithmic** limitations.

#### Limitation 1: BDD Canonicity Requires Uniform Node Types

**Standard BDD Node:**

```rust
struct BddNode {
    var: VarId,           // Decision variable
    low: NodeRef,         // Else-branch (var = false)
    high: NodeRef,        // Then-branch (var = true)
}
```

**Key Property:** Canonicity requires **structural sharing**.

- Nodes `(x₁, low, high)` are deduplicated via hash-consing
- Two nodes with same `(var, low, high)` must be **identical**
- This enables `O(1)` equality checking and efficient operations

**Problem with Embedded Values:**

```rust
struct ValueBddNode<V> {
    var: VarId,
    low: NodeRef,
    high: NodeRef,
    value: V,              // ⚠️ Breaks canonicity!
}
```

If different BDD paths lead to the same boolean structure but different values, we get:

```text
Node₁: (x₁, false, true, value=Interval[0,10])
Node₂: (x₁, false, true, value=Interval[5,15])

Problem: Same structure (x₁, false, true) but different values!
```

We lose canonical form → no more structural sharing → exponential blowup.

#### Limitation 2: Abstract Domain Operations Don't Respect BDD Structure

**BDD Operations Are Boolean:**

- `and(φ₁, φ₂)` → produces BDD for `φ₁ ∧ φ₂`
- `or(φ₁, φ₂)` → produces BDD for `φ₁ ∨ φ₂`
- Result structure determined by **boolean formula**, not values

**Abstract Domain Operations Need Different Merge Logic:**

```text
Join (⊔) example:

Map₁: { x>5 ↦ [10,20] }
Map₂: { x>5 ↦ [15,25] }

BDD level:   x>5 ∧ x>5 = x>5        (structure unchanged)
Value level: [10,20] ⊔ [15,25] = [10,25]  (interval join)

Result: { x>5 ↦ [10,25] }
```

The value merge `[10,20] ⊔ [15,25]` is **independent** of the BDD structure. We can't derive it from Shannon expansion alone.

#### Limitation 3: Non-Boolean Values Have No Natural BDD Encoding

**Shannon Expansion Only Works for Boolean Functions:**

```text
f: Bool^n → Bool    ✓ Can represent as BDD
g: Bool^n → Interval ✗ Interval is not {0,1}
```

**Numeric domains are not Boolean:**

- `Interval[0,10]` has infinitely many concrete values
- Cannot enumerate as Boolean formula
- No natural "true" vs "false" interpretation

**Multi-valued Decision Diagrams (MDDs)?**

Yes, but:

- Lose canonicity (no unique representation)
- Lose efficient operations (no hash-consing)
- Explosion in node count

### 4.5.3 What We Gain by Separation

**Current Design:**

```rust
struct ControlSensitiveElement<N> {
    partitions: Map[BDD → N::Element],
    //              ↑          ↑
    //           Boolean    Arbitrary domain
}
```

**Benefits:**

1. **BDD Layer:**
   - Maintains canonical form
   - Efficient boolean operations
   - Structural sharing (exponential savings)
   - Standard BDD algorithms apply

2. **Value Layer:**
   - Arbitrary abstract domains (intervals, octagons, polyhedra)
   - Domain-specific operations (widening, narrowing)
   - Independent of control structure

3. **Clean Separation:**
   - `control_domain.and(φ₁, φ₂)` → pure BDD operation
   - `numeric_domain.join(n₁, n₂)` → pure domain operation
   - Map manages correspondence

### 4.5.4 Alternative: Functional Representation

**Theoretical Alternative:** Represent as a function `φ → N::Element`.

```rust
struct FunctionalElement<N> {
    f: Box<dyn Fn(&ControlState) -> N::Element>
}
```

**Problems:**

1. **No Equality:** Functions aren't comparable
   - Can't check `elem₁ == elem₂`
   - Breaks lattice theory requirements

2. **No Enumeration:** Can't list all partitions
   - Fixpoint algorithms need to iterate partitions
   - Join/meet need explicit partition sets

3. **No Optimization:** Can't detect redundant partitions
   - `{ x>5 ↦ [0,10], x>5 ↦ [0,10] }` → should merge
   - Function representation hides this

### 4.5.5 Future Direction: Algebraic Decision Diagrams (ADDs)

**Closer to Your Vision:** ADDs extend BDDs with terminal values.

```text
ADD Node:
  if terminal: return Value
  else: ITE(var, high_subtree, low_subtree)

Example ADD for our domain:
        x>5?
       /    \
   [10,20]  [0,5]

Directly encodes: ITE(x>5, [10,20], [0,5])
```

**Why We Don't Use ADDs (Yet):**

1. **Library Support:**
   - `bdd-rs` doesn't support ADDs
   - Would need custom implementation

2. **Canonicity Still Limited:**
   - ADDs lose full canonicity when values aren't totally ordered
   - Intervals/polyhedra don't have canonical normal form

3. **Operation Complexity:**
   - ADD operations more complex than BDD + Map
   - Need to handle value merge at every node

**When ADDs Make Sense:**

- When values are **enumerable** (finite domain)
- When values have **total order** (e.g., min/max of integers)
- When terminal count is **small** (< 100 distinct values)

**Our Case:**

- Intervals: ✓ Totally ordered (by inclusion)
- Polyhedra: ✗ Partial order only
- Terminal count: Potentially large (every partition can have unique interval)

### 4.5.6 Summary: Why the Map Abstraction?

| Aspect | Direct BDD Embedding | Map[BDD → Value] | ADD |
|--------|---------------------|------------------|-----|
| **Canonicity** | ✗ Broken | ✓ BDD layer canonical | △ Limited |
| **Arbitrary Domains** | ✗ Boolean only | ✓ Any domain | △ Enumerable only |
| **Efficient Ops** | ✗ Lost sharing | ✓ Both layers efficient | △ Complex |
| **Equality** | ✗ No comparison | ✓ Partition-wise | △ Requires value order |
| **Implementation** | ✗ Requires BDD rewrite | ✓ Uses std library | ✗ Custom code |

**Conclusion:** The `Map[BDD → Value]` representation is a **pragmatic engineering choice** that:

- Leverages existing BDD libraries
- Supports arbitrary abstract domains
- Maintains both BDD and domain operations efficiently
- Provides clean separation of concerns

The ITE connection you identified is **correct** — it's the underlying mathematical structure. The Map representation is the **practical realization** that navigates the constraints of canonical forms, type systems, and algorithmic efficiency.

---

## 5. Control Variable Discovery

### 5.1 Static Analysis

**Goal:** Automatically identify relevant Boolean control variables.

**Sources:**

1. **Explicit Boolean Variables:**

   ```c
   bool flag = ...;
   if (flag) { ... }
   ```

2. **Comparison Predicates:**

   ```c
   if (x > 0) { ... }
   // Introduce: ctrl_x_gt_0 ∈ CV
   ```

3. **Enum/Mode Variables:**

   ```c
   enum Mode { INIT, READY, ACTIVE };
   Mode mode;
   if (mode == ACTIVE) { ... }
   // Introduce: ctrl_mode_is_ACTIVE ∈ CV
   ```

**Algorithm 5.1 (Control Variable Extraction):**

```rust
fn extract_control_vars(program: &CFG) -> Set<String> {
    let mut cv = Set::new();

    for stmt in program.statements() {
        match stmt {
            // Explicit boolean variables
            Stmt::Decl(ty, name) if ty.is_bool() => {
                cv.insert(name);
            }

            // Branch conditions
            Stmt::If(cond, _, _) => {
                if let Some(var) = extract_bool_var(cond) {
                    cv.insert(var);
                } else {
                    // Create synthetic control variable
                    let synth = format!("ctrl_{}", hash(cond));
                    cv.insert(synth);
                }
            }

            // Switch cases (enum modes)
            Stmt::Switch(expr, cases) => {
                for (value, _) in cases {
                    let synth = format!("ctrl_{}_{}", expr, value);
                    cv.insert(synth);
                }
            }

            _ => {}
        }
    }

    cv
}
```

### 5.2 Dynamic Refinement

**Idea:** Start with coarse partitioning, refine when needed.

**CEGAR-Style Approach:**

1. Begin with `M = {true ↦ ⊤_NUM}`
2. Run analysis
3. If false alarm detected:
   - Identify relevant control variable causing imprecision
   - Refine partition at that variable
   - Re-run analysis
4. Repeat until no false alarms or budget exhausted

---

## 6. Implementation Strategy

### 6.1 Module Structure

```text
src/bdd_control.rs       (800-1000 lines)
├── ControlVariable       // Struct: name, bdd_var_id
├── ControlState          // BDD wrapper with control semantics
├── BddControlDomain      // AbstractDomain implementation
├── ControlSensitiveProd  // Product with numeric domains
└── PartitionManager      // Merging, size tracking

src/control_transfer.rs  (400-600 lines)
├── assign_control()      // Control variable assignment
├── assume_control()      // Control constraint
├── mixed_transfer()      // Control + numeric interaction

tests/bdd_control_tests.rs (600-800 lines)
├── Unit tests            // Each operation
├── Integration tests     // State machine examples
├── Property tests        // Lattice axioms
```

### 6.2 Data Structures

**ControlState:**

```rust
pub struct ControlState {
    /// BDD representing the control constraint
    bdd: Ref,
    /// Shared BDD manager
    manager: Rc<Bdd>,
    /// Human-readable description (for debugging)
    description: String,
}
```

**BddControlDomain:**

```rust
pub struct BddControlDomain {
    /// Shared BDD manager
    manager: Rc<Bdd>,
    /// Control variable to BDD variable mapping
    var_map: HashMap<String, u32>,
    /// Next available BDD variable ID
    next_var: u32,
}
```

**ControlSensitiveProduct:**

```rust
pub struct ControlSensitiveProduct<N: NumericDomain> {
    /// Control domain
    control: BddControlDomain,
    /// Numeric domain
    numeric: N,
    /// Partition threshold
    max_partitions: usize,
}

pub struct ProductElement<N: NumericDomain> {
    /// Map from control states to numeric states
    partitions: Vec<(ControlState, N::Element)>,
    /// Bottom flag
    is_bottom: bool,
}
```

### 6.3 Key Design Decisions

**Decision 6.1 (BDD Sharing):**

- **Choice:** Single shared BDD manager for all control states
- **Rationale:** Maximize BDD sharing, reduce memory
- **Trade-off:** Requires careful manager lifetime management

**Decision 6.2 (Partition Representation):**

- **Choice:** `Vec<(BDD, NumericElem)>` instead of `HashMap<BDD, NumericElem>`
- **Rationale:** Small partition counts (<100), linear search acceptable
- **Benefit:** Simpler iteration, no hash function needed for BDDs

**Decision 6.3 (Eager vs. Lazy Merging):**

- **Choice:** Eager merging when threshold exceeded
- **Rationale:** Predictable memory usage, bounded complexity
- **Alternative:** Lazy merging (on-demand) could be future optimization

---

## 7. Correctness & Soundness

### 7.1 Soundness Theorem

**Theorem 7.1 (Soundness of BDD Control Domain):**

Let `γ: D_PROD → ℘(Σ)` be the concretization function mapping abstract states to concrete states. Then:

1. **Local Soundness:** For all concrete states `σ` and abstract operations `op`:

   ```text
   σ ∈ γ(M) ⇒ ⟦op⟧(σ) ∈ γ(⟦op⟧#(M))
   ```

2. **Global Soundness:** For all programs `P` and initial states `σ₀ ∈ γ(M₀)`:

   ```text
   ⟦P⟧(σ₀) ∈ γ(⟦P⟧#(M₀))
   ```

*Proof Obligations:*

- Transfer functions over-approximate concrete semantics
- Partition merging preserves soundness (joins are sound)
- BDD operations correctly represent Boolean formulas

### 7.2 Precision Guarantees

**Theorem 7.2 (Relative Precision):**

The BDD control domain is strictly more precise than path-insensitive analysis for control-dependent programs.

*Formal Statement:*

```text
Let M_sens be control-sensitive analysis result
Let M_insens be path-insensitive result
Then: γ(M_sens) ⊆ γ(M_insens)
```

**When Equality Holds:**

- Programs with no Boolean control variables
- All control variables irrelevant to numeric properties

**When Strict Improvement:**

- State machines with mode-dependent invariants
- Programs with boolean flags controlling numeric updates

---

## 8. Examples & Case Studies

### 8.1 Example 1: Simple Flag

**Program:**

```c
int x = 0;
bool flag = false;

if (input > 10) {
    flag = true;
    x = 5;
}

if (flag) {
    x = x + 10;  // Only executed if flag=true
}

assert(x == 15 || x == 0);
```

**Path-Insensitive Analysis:**

- After line 4: `x ∈ [0, 5]`, `flag ∈ {true, false}`
- After line 8: `x ∈ [0, 15]` (join of [10,15] and [0,0])
- **Result:** Cannot prove assertion! `x` could be in `[0,15]`

**BDD Control Analysis:**

| Line | Control State | Numeric State |
|------|---------------|---------------|
| 1 | `true` | `x = 0` |
| 3 | `true` | `x = 0` |
| 4 (then) | `flag = true` | `x = 5` |
| 4 (else) | `flag = false` | `x = 0` |
| 8 (then) | `flag = true` | `x = 15` |
| 8 (skip) | `flag = false` | `x = 0` |

**Final State:**

```text
{
    flag = true ↦ x = 15,
    flag = false ↦ x = 0
}
```

**Result:** ✓ Assertion proven! `x ∈ {0, 15}` exactly.

### 8.2 Example 2: State Machine

**Program:**

```c
enum State { INIT, READY, ACTIVE, ERROR };
State state = INIT;
int counter = 0;

while (counter < 100) {
    switch (state) {
        case INIT:
            if (sensor_ok()) state = READY;
            counter = 0;
            break;
        case READY:
            if (counter > 10) state = ACTIVE;
            counter++;
            break;
        case ACTIVE:
            if (counter > 50) state = ERROR;
            counter++;
            break;
        case ERROR:
            counter = 0;
            break;
    }
}

// Property: In ACTIVE state, counter is always > 10
assert(state != ACTIVE || counter > 10);
```

**Control Variables:**

- `state_is_INIT`, `state_is_READY`, `state_is_ACTIVE`, `state_is_ERROR`

**BDD Control Analysis Maintains:**

| Control State | Numeric Invariant |
|---------------|-------------------|
| `state_is_INIT` | `counter = 0` |
| `state_is_READY` | `counter ∈ [1, 10]` |
| `state_is_ACTIVE` | `counter ∈ [11, 50]` |
| `state_is_ERROR` | `counter = 0` |

**Result:** ✓ Property verified! In `ACTIVE` state, `counter > 10` always holds.

---

## 9. Performance Characteristics

### 9.1 Time Complexity

**Operations:**

| Operation | Complexity | Notes |
|-----------|------------|-------|
| `bottom()` | O(1) | Create empty BDD |
| `top()` | O(1) | Create true BDD |
| `le(M₁, M₂)` | O(\|M₁\| × \|M₂\| × B) | B = BDD implication check |
| `join(M₁, M₂)` | O(\|M₁\| × \|M₂\| × B) | Merge partitions |
| `meet(M₁, M₂)` | O(\|M₁\| × \|M₂\| × B) | Intersect partitions |
| `assign_control` | O(\|M\| × B) | Per partition BDD update |
| `assume_control` | O(\|M\| × B) | Filter partitions |

Where:

- `|M|` = partition count (typically < 100)
- `B` = BDD operation cost (typically O(|nodes|²) worst case, O(|nodes|) average)

**Overall:** Linear in partition count, polynomial in BDD size.

### 9.2 Space Complexity

**Memory Usage:**

```text
Space(M) = |M| × (sizeof(BDD) + sizeof(NumericElem))
         ≈ |M| × (100 bytes + N bytes)
```

Where `N` depends on numeric domain:

- Interval: ~50 bytes
- Octagon: ~1 KB
- Polyhedra: ~10 KB

**Typical:** `|M| = 50`, Interval domain → ~7.5 KB per abstract state.

### 9.3 Scalability Targets

**Small Programs (<1000 LOC):**

- Control variables: < 10
- Partition count: < 50
- Analysis time: < 1 second

**Medium Programs (1000-10000 LOC):**

- Control variables: < 20
- Partition count: < 100
- Analysis time: < 10 seconds

**Large Programs (>10000 LOC):**

- Requires partition merging strategies
- Selective control variable tracking
- May need CEGAR refinement

---

## 10. Testing Strategy

### 10.1 Unit Tests (Per Operation)

**Test Coverage:**

1. **Lattice Properties (15 tests):**
   - `test_control_bottom_is_least`
   - `test_control_top_is_greatest`
   - `test_control_join_commutative`
   - `test_control_join_associative`
   - `test_control_join_idempotent`
   - `test_control_meet_commutative`
   - `test_control_meet_associative`
   - `test_control_le_reflexive`
   - `test_control_le_transitive`
   - `test_control_le_antisymmetric`
   - `test_control_widen_termination`
   - `test_control_absorption_laws`
   - `test_control_bottom_annihilates_meet`
   - `test_control_top_annihilates_join`
   - `test_control_distributivity`

2. **BDD Operations (10 tests):**
   - `test_bdd_var_allocation`
   - `test_bdd_conjunction`
   - `test_bdd_disjunction`
   - `test_bdd_negation`
   - `test_bdd_implication`
   - `test_bdd_equivalence`
   - `test_bdd_sat_count`
   - `test_bdd_tautology_detection`
   - `test_bdd_contradiction_detection`
   - `test_bdd_variable_ordering`

3. **Transfer Functions (20 tests):**
   - `test_assign_control_var_true`
   - `test_assign_control_var_false`
   - `test_assign_control_expr_simple`
   - `test_assign_control_expr_complex`
   - `test_assume_control_true`
   - `test_assume_control_false`
   - `test_assume_control_contradiction`
   - `test_assume_numeric_refinement`
   - `test_assign_numeric_independent_paths`
   - `test_assign_numeric_dependent_paths`
   - `test_conditional_split`
   - `test_conditional_merge`
   - `test_nested_conditionals`
   - `test_sequential_conditionals`
   - `test_loop_with_control_flag`
   - `test_state_transition_single`
   - `test_state_transition_multiple`
   - `test_state_machine_cycle`
   - `test_control_independence`
   - `test_control_numeric_interaction`

4. **Partition Management (10 tests):**
   - `test_partition_count_tracking`
   - `test_partition_merge_threshold`
   - `test_partition_merge_similarity`
   - `test_partition_explosion_prevention`
   - `test_partition_bdd_size_limit`
   - `test_partition_memory_limit`
   - `test_partition_normalization`
   - `test_partition_deduplication`
   - `test_empty_partition_elimination`
   - `test_unreachable_partition_detection`

**Total Unit Tests: ~55**

### 10.2 Integration Tests (Full Programs)

**Test Programs:**

1. **Flag Example (as above)** - Simple control dependency
2. **Mode Controller** - State machine with 4 states
3. **Traffic Light** - Cyclic state machine
4. **Nested Flags** - Multiple Boolean variables
5. **Loop with Flag** - Control-dependent iteration
6. **Error Handling** - Error flag propagation

**Each test verifies:**

- Precision improvement over path-insensitive
- Correctness of final invariants
- Partition count reasonable (<100)
- No false alarms

### 10.3 Property-Based Tests (QuickCheck-style)

**Properties to Test:**

```rust
#[quickcheck]
fn prop_join_commutative(φ1: ControlState, φ2: ControlState) -> bool {
    domain.join(&φ1, &φ2) == domain.join(&φ2, &φ1)
}

#[quickcheck]
fn prop_le_antisymmetric(φ1: ControlState, φ2: ControlState) -> bool {
    if domain.le(&φ1, &φ2) && domain.le(&φ2, &φ1) {
        φ1 == φ2
    } else {
        true
    }
}

#[quickcheck]
fn prop_assume_refines(M: ProductElement, cond: BoolExpr) -> bool {
    let M_refined = assume_control(M, cond);
    domain.le(&M_refined, &M)  // Refinement ⇒ smaller state
}
```

---

## 11. Documentation Plan

### 11.1 API Documentation

**Module-level Docs (src/bdd_control.rs):**

- Overview of BDD control domain
- Theoretical foundations (lattice structure)
- When to use vs. path-insensitive analysis
- Performance characteristics
- Usage examples

**Struct/Function Docs:**

- Each public item documented
- Examples for complex operations
- Links to related functions
- Time/space complexity notes

### 11.2 Tutorial Examples

**Example 1: Basic Usage**

```rust
/// # Example: Simple Flag Analysis
///
/// Analyze a program with a boolean flag controlling numeric updates.
```

**Example 2: State Machine**

```rust
/// # Example: Mode Controller
///
/// Demonstrate analysis of a 4-state finite state machine.
```

**Example 3: Custom Control Variables**

```rust
/// # Example: Derived Control Variables
///
/// Show how to create synthetic control variables from predicates.
```

### 11.3 Design Diagrams

**Diagram 11.1: Domain Hierarchy**

```text
    AbstractDomain
         ↑
         |
    BddControlDomain ──────┐
         ↑                 |
         |                 | uses
    ControlSensitiveProd   |
         ↑                 |
         |                 |
    NumericDomain ─────────┘
```

**Diagram 11.2: Partition Structure**

```text
ProductElement
│
├─ partition[0]: (BDD: flag=true,  Numeric: x ∈ [5,5])
├─ partition[1]: (BDD: flag=false, Numeric: x ∈ [0,0])
└─ is_bottom: false
```

**Diagram 11.3: Transfer Function Pipeline**

```text
Input State → Control Constraint → Numeric Constraint → Output State
     M      →    assume(b=true)   →    assume(x>0)    →    M'
```

---

## 12. Implementation Phases

### Phase 1: Core BDD Control Domain (Week 1)

**Tasks:**

1. Define `ControlState` and `BddControlDomain`
2. Implement `AbstractDomain` trait
3. Basic BDD operations (and, or, not, implies)
4. Unit tests for lattice operations (15 tests)

**Deliverable:** Working BDD control domain with lattice operations.

### Phase 2: Product Domain (Week 2)

**Tasks:**

1. Define `ControlSensitiveProduct`
2. Implement partition management
3. Product lattice operations (join, meet, le)
4. Unit tests for product operations (10 tests)

**Deliverable:** Product domain combining control and numeric.

### Phase 3: Transfer Functions (Week 2-3)

**Tasks:**

1. Control variable assignment
2. Control assume/refinement
3. Numeric operations with control context
4. Mixed control-numeric operations
5. Transfer function tests (20 tests)

**Deliverable:** Complete transfer function suite.

### Phase 4: Examples & Validation (Week 3)

**Tasks:**

1. Implement 6 example programs
2. Validate precision improvement
3. Performance profiling
4. Documentation completion

**Deliverable:** Working examples demonstrating effectiveness.

---

## 13. Success Criteria

### 13.1 Functional Requirements

- ✅ BDD control domain implements `AbstractDomain` trait
- ✅ Product domain combines control + numeric domains
- ✅ Transfer functions handle control, numeric, and mixed operations
- ✅ Partition merging prevents explosion (count < 100)
- ✅ All 55+ unit tests pass
- ✅ 6 integration tests demonstrate precision improvement

### 13.2 Performance Requirements

- ✅ Simple programs (<100 LOC) analyze in < 1 second
- ✅ Medium programs (<1000 LOC) analyze in < 10 seconds
- ✅ Memory usage < 100 MB for typical programs
- ✅ BDD size < 10,000 nodes

### 13.3 Quality Requirements

- ✅ 100% documentation coverage (public items)
- ✅ Zero clippy warnings
- ✅ Formatted with rustfmt
- ✅ Comprehensive examples with explanations
- ✅ Design decisions documented with rationale

---

## 14. Open Questions & Future Work

### 14.1 Research Questions

1. **Optimal Partition Merging Strategy:**
   - How to choose which partitions to merge?
   - Numeric similarity vs. control similarity trade-off?

2. **Control Variable Selection:**
   - Which Boolean variables are most "relevant"?
   - Can we learn relevance dynamically?

3. **Relation to Predicate Abstraction:**
   - How does BDD control domain relate to CEGAR?
   - Can we integrate refinement loops?

### 14.2 Extensions

1. **Relational Control Domains:**
   - Track relationships between control variables
   - E.g., `flag1 ⇒ ¬flag2` (mutual exclusion)

2. **Temporal Control Properties:**
   - Track control state history
   - E.g., "flag was true in the past"

3. **Probabilistic Control:**
   - Extend to probabilistic Boolean variables
   - Weighted BDDs for probability distributions

4. **Multi-threaded Programs:**
   - Control state includes thread interleavings
   - Synchronization primitives as control variables

---

## 15. Conclusion

The BDD Control Domain provides a **principled, sound, and precise** approach to path-sensitive static analysis. By partitioning numeric invariants based on Boolean control state, we achieve:

1. **Precision:** Separate invariants per control path
2. **Efficiency:** BDD representation scales to many Boolean variables
3. **Modularity:** Composes with any numeric abstract domain
4. **Soundness:** Formal semantics with proven correctness

**Next Steps:** Implement Phase 1 (Core BDD Control Domain) and validate with unit tests!

---

**Document Status:** Design Complete
**Ready for Implementation:** ✅ YES
**Estimated Implementation Time:** 3-4 weeks
**Lines of Code:** ~2000-2500 (including tests and docs)
