#import "../../theme.typ": *

= Enter Binary Decision Diagrams <enter-bdds>

We've seen why path explosion is a problem and glimpsed that BDDs solve it.
Now we examine _how_ BDDs achieve this compression.

Binary Decision Diagrams are a data structure for representing Boolean functions.
Despite worst-case exponential size, they often provide dramatic compression for structured problems.

== Boolean Functions: The Foundation

A Boolean function maps Boolean inputs to a Boolean output.

#definition(title: "Boolean Function")[
  A function $f : bb(B)^n arrow.r bb(B)$ where $bb(B) = {0, 1}$.

  With $n$ inputs, there are $2^n$ possible input combinations and $2^(2^n)$ possible functions.
]

Examples:

```rust
// AND: f(x, y) = x ∧ y
fn and(x: bool, y: bool) -> bool {
    x && y
}

// XOR: f(x, y) = x ⊕ y = (x ∧ ¬y) ∨ (¬x ∧ y)
fn xor(x: bool, y: bool) -> bool {
    x != y
}

// Majority: f(x, y, z) = (x ∧ y) ∨ (x ∧ z) ∨ (y ∧ z)
fn majority(x: bool, y: bool, z: bool) -> bool {
    (x && y) || (x && z) || (y && z)
}
```

Representation options:
- *Truth tables:* $2^n$ rows, exponential size
- *Boolean formulas:* Size varies, but no canonical form
- *BDDs:* Often compact, _canonical_ form

== Decision Trees: The Starting Point

A decision tree evaluates a Boolean function by testing variables sequentially.

[Decision tree diagram for AND(x,y) would go here]

```
       x?
      /  \
    0/    \1
    /      \
   0        y?
           /  \
         0/    \1
         /      \
        0        1
```

Each path from root to leaf represents one input combination.
Leaves are labeled with output values (0 or 1).

For function $f(x, y) = x and y$:
- Path `x=0`: Output 0 (regardless of y)
- Path `x=1, y=0`: Output 0
- Path `x=1, y=1`: Output 1

#info-box(title: "Decision Tree Properties")[
  - Size: $O(2^n)$ nodes for $n$ variables
  - Evaluation: $O(n)$ time (one test per variable)
  - No sharing: Same subtrees may appear multiple times
]

== From Trees to DAGs: Sharing Structure

Key observation: decision trees have redundancy.

In the AND tree above:
- The left subtree (when x=0) always outputs 0
- We don't need to test y

We can _share_ subtrees that compute the same function.

#definition(title: "Binary Decision Diagram (BDD)")[
  A directed acyclic graph (DAG) representing a Boolean function where:
  - Each non-terminal node tests one variable
  - Two outgoing edges: low (dashed, variable=0) and high (solid, variable=1)
  - Terminal nodes (leaves) are labeled 0 or 1
  - All paths testing variables in the same order
]

[BDD diagram for AND would go here showing node sharing]

```
       x
      / \
    0/   \1
    /     \
   [0]     y
          / \
        0/   \1
        /     \
      [0]    [1]
```

Here both "0" leaves are the _same node._
The left subtree when x=0 directly points to the 0 terminal.

== Reduced Ordered BDDs (ROBDDs)

Two reduction rules transform decision trees into canonical BDDs:

#definition(title: "Reduction Rules")[
  1. *Merge:* If two nodes compute identical functions, merge them into one
  2. *Eliminate:* If a node's low and high edges point to the same child, bypass the node
]

Apply these exhaustively to get a _Reduced Ordered BDD_ (ROBDD).

#example-box(number: "3.1", title: "Reduction in Action")[
  Original decision tree for $f(x, y) = x$:

  ```
         x
        / \
      0/   \1
      /     \
     y       y
    / \     / \
  0/   \1 0/   \1
  /     \ /     \
  0      1 0      1
  ```

  After merging: Both y nodes are identical, merge them.
  After elimination: The y node's output doesn't depend on y, eliminate it.

  Final ROBDD:
  ```
       x
      / \
    0/   \1
    /     \
   [0]    [1]
  ```

  Reduced from 7 nodes to 3 nodes!
]

== Canonicity: The Magic Property

#theorem(title: "ROBDD Canonicity")[
  Given a fixed variable ordering, every Boolean function has a unique ROBDD representation.

  This means: $f = g$ if and only if their ROBDDs are identical (same graph structure).
]

*Why this matters:*
- Equality checking is $O(1)$: just compare pointers
- No need to reason about logical equivalence
- Hash consing prevents duplicate nodes

This is _enormous_ for verification.
Checking if two complex formulas are equivalent is normally expensive (co-NP-complete).
With ROBDDs, it's free.

#insight-box[
  *Canonicity is the killer feature.*
  Most data structures for Boolean functions have multiple representations for the same function.
  ROBDDs have exactly one.
  This makes many operations trivial.
]

== Variable Ordering: The Achilles Heel

ROBDDs are canonical _given a fixed variable ordering._
Different orderings produce different (but equivalent) BDDs.

#warning-box[
  *ROBDD size is extremely sensitive to variable ordering.*
  Bad ordering: exponential size.
  Good ordering: polynomial or even linear size.
]

#example-box(number: "3.2", title: "Ordering Matters")[
  Consider $f(x_1, x_2, x_3, x_4) = (x_1 and x_2) or (x_3 and x_4)$.

  *Good ordering:* $x_1 < x_2 < x_3 < x_4$

  The BDD can test $x_1, x_2$ together, then $x_3, x_4$ together.
  Result: Small BDD (around 6-8 nodes).

  *Bad ordering:* $x_1 < x_3 < x_2 < x_4$

  Must interleave testing different subformulas.
  Result: Larger BDD (around 10-12 nodes).

  For extreme cases (like integer comparison), bad ordering creates exponential blowup.
]

Famous example: integer comparison.

Consider testing if two $n$-bit integers are equal: $f = (x_1 = y_1) and dots.h.c and (x_n = y_n)$.

Good ordering: $x_1 < y_1 < x_2 < y_2 < dots.h.c < x_n < y_n$
- ROBDD size: $O(n)$ nodes

Bad ordering: $x_1 < x_2 < dots.h.c < x_n < y_1 < y_2 < dots.h.c < y_n$
- ROBDD size: $O(2^n)$ nodes (exponential!)

Finding optimal ordering is NP-complete.
In practice:
- Use heuristics (group related variables)
- Dynamic reordering for iterative improvement
- Accept that some functions are inherently hard

#info-box(title: "Variable Ordering in Practice")[
  For program analysis:
  - Group variables from the same statement
  - Order program counters before data variables
  - Use domain knowledge about structure

  The `bdd-rs` library doesn't yet support dynamic reordering, so choose wisely upfront.
]

== BDD Operations

The power of BDDs comes from efficient operations.

=== Basic Operations

*Apply:* Combine two BDDs with a binary operator (∧, ∨, ⊕, etc.)

```rust
let f = bdd.mk_var(1);  // Variable x₁
let g = bdd.mk_var(2);  // Variable x₂
let h = bdd.apply_and(f, g);  // x₁ ∧ x₂
```

*Not:* Complement a BDD

```rust
let not_f = bdd.apply_not(f);  // ¬x₁
```

*If-Then-Else (ITE):* $"ITE"(f, g, h) = (f and g) or (not f and h)$

This is the universal operator; all other operations can be expressed via ITE.

```rust
// AND: f ∧ g = ITE(f, g, 0)
// OR:  f ∨ g = ITE(f, 1, g)
// XOR: f ⊕ g = ITE(f, ¬g, g)
```

=== Complexity

With memoization (caching intermediate results):

- *Apply:* $O(|f| dot.op |g|)$ where $|f|$ is number of nodes
- *Not:* $O(1)$ (flip terminal labels or use complement edges)
- *ITE:* $O(|f| dot.op |g| dot.op |h|)$

In practice, these are much faster due to sharing and caching.

#info-box(title: "Memoization is Critical")[
  Without caching:
  - Each operation might recompute the same subproblems
  - Complexity becomes exponential

  With caching:
  - Each unique subproblem computed once
  - Polynomial complexity in BDD size

  The `bdd-rs` library uses hash-based memoization internally.
]

=== Quantification

*Existential quantification:* $exists x . f$

"Is there any value of $x$ that makes $f$ true?"

Computed as: $f[x arrow.l 0] or f[x arrow.l 1]$

```rust
let f = bdd.mk_and(x, y);  // x ∧ y
let exists_x = bdd.exists(f, 1);  // ∃x. (x ∧ y) = y
```

*Universal quantification:* $forall x . f$

"Does $f$ hold for all values of $x$?"

Computed as: $f[x arrow.l 0] and f[x arrow.l 1]$

```rust
let forall_x = bdd.forall(f, 1);  // ∀x. (x ∧ y) = 0
```

Quantification is crucial for symbolic model checking.

== Why BDDs Work for Program Analysis

BDDs compress structured Boolean functions.
Program path conditions have structure:

1. *Locality:* Conditions often involve few variables
2. *Repetition:* Same conditions appear on many paths
3. *Hierarchy:* Outer conditions constrain inner ones

Example from Chapter 2:

```rust
if mode == Mode::Off {
    return Action::Off;  // Condition: mode=Off
}

if temp < TEMP_MIN {
    if time > EMERGENCY_TIME {
        return Action::EmergencyHeat;  // Condition: mode≠Off ∧ temp<MIN ∧ time>EMERG
    }
    return Action::HeatOn;  // Condition: mode≠Off ∧ temp<MIN ∧ time≤EMERG
}
```

All paths except the first share `mode≠Off`.
Paths 2-3 share `mode≠Off ∧ temp<MIN`.

BDD exploits this sharing:
- `mode≠Off` appears once in the BDD
- Paths branch only where they differ

[BDD diagram showing path condition sharing would go here]

Result: 6 explicit paths represented with far fewer BDD nodes.

#example-box(number: "3.3", title: "Real-World Compression")[
  Bryant's original paper (1986) showed:
  - Combinational circuit verification with 100+ gates
  - Explicit truth table: $2^(100)$ rows (impossible)
  - BDD representation: ~10,000 nodes (feasible)

  In symbolic model checking:
  - State spaces with $10^(20)$ states
  - BDD representation: millions of nodes (manageable)
]

== Historical Context

#historical-note(
  person: "Randal Bryant",
  year: "1986",
  title: "Graph-Based Algorithms for Boolean Function Manipulation",
)[
  Bryant introduced ROBDDs and proved canonicity.
  This foundational work enabled efficient symbolic manipulation of Boolean functions.

  Key contributions:
  - Reduction rules ensuring canonical form
  - Algorithms for apply and ITE operations
  - Demonstration of practical efficiency
]

#historical-note(
  person: "Burch et al.",
  year: "1990",
  title: "Symbolic Model Checking: $10^(20)$ States and Beyond",
)[
  Applied BDDs to model checking hardware systems.
  Showed that BDDs could represent state spaces with $10^(20)$ states using only millions of nodes.

  This work launched the field of _symbolic model checking_ and revolutionized hardware verification.
]

== BDDs in the Wild

BDDs are used in:

*Hardware verification:* Checking circuits for correctness
- Intel, AMD, IBM use BDD-based tools
- Critical for processor design

*Formal verification:* Model checkers like NuSMV, SPIN
- Verify concurrent systems
- Protocol verification

*Software analysis:* Static analysis tools
- Data flow analysis
- Security vulnerability detection

*SAT solving:* Some SAT solvers use BDD techniques
- Hybrid approaches combining BDDs and CDCL

*Program synthesis:* Generating programs from specifications
- BDDs encode constraints

== When BDDs Fail

Not all Boolean functions compress well.

#warning-box[
  *Functions with exponential BDD size (for any ordering):*
  - Integer multiplication (proven exponential)
  - Some cryptographic functions
  - Random Boolean functions (no structure)
]

For these, BDDs are impractical.
Alternative approaches:
- SAT solvers (work on formula directly)
- And-Inverter Graphs (AIGs)
- Specialized data structures

But for _structured_ problems (like program control flow), BDDs excel.

== Summary

BDDs are a canonical representation for Boolean functions.
They achieve compression by sharing common substructures.
Operations (∧, ∨, ¬, quantification) are efficient.

Key insights:
- Canonicity enables $O(1)$ equality checking
- Variable ordering critically affects size
- Memoization makes operations polynomial in BDD size
- Structure in problems (like program paths) leads to compression

BDDs transform intractable path-sensitive analysis into a practical technique.

In the next chapter, we see how to use the `bdd-rs` library to build BDDs and manipulate them programmatically.

#chapter-summary(
  [
    *Boolean functions map ${0,1}^n arrow.r {0,1}$.*
    With $n$ inputs, there are $2^(2^n)$ possible functions. Representing them efficiently is crucial.
  ],
  [
    *Decision trees evaluate functions but have exponential size.*
    Each path from root to leaf is one input combination. No sharing between paths.
  ],
  [
    *BDDs are DAGs with shared structure.*
    Reduction rules (merge identical nodes, eliminate redundant tests) compress trees into DAGs.
  ],
  [
    *ROBDDs are canonical.*
    Given fixed variable ordering, each function has exactly one ROBDD. Equality checking is $O(1)$.
  ],
  [
    *Variable ordering critically affects BDD size.*
    Good ordering: polynomial size. Bad ordering: exponential size. Finding optimal ordering is NP-complete.
  ],
  [
    *BDD operations are efficient with memoization.*
    Apply, ITE, quantification run in polynomial time in BDD size when cached.
  ],
  [
    *BDDs excel on structured problems.*
    Program path conditions exhibit locality, repetition, hierarchy. BDDs exploit this structure.
  ],
  [
    *Not all functions compress.*
    Integer multiplication, random functions have exponential BDD size for any ordering.
  ],
  [
    *Main Insight:*
    BDDs provide canonical, compact representations for structured Boolean functions, enabling efficient manipulation critical for symbolic program analysis.
  ],
)

#v(2em)
