#import "../../theme.typ": *

= Symbolic Reasoning with BDDs <ch-bdds>

@ch-control-flow showed that tracking every execution path individually leads to *path explosion*.

To build a scalable verifier, we need a mechanism representing *sets of states* efficiently.

This chapter introduces the *Binary Decision Diagram (BDD)*, the core data structure powering our Symbolic Analyzer.

Instead of enumerating states as lists, we represent them as *Boolean functions*.

== From Sets to Functions

A fundamental insight: sets and functions correspond.

We represent any subset $S$ of universe $U$ using a *characteristic function* $f_S : U -> {0, 1}$:

$ f_S (x) = cases(1 &"if" x in S, 0 &"if" x in.not S) $

If we can represent $f_S$ compactly, we effectively represent the set $S$ compactly.

=== Constraints as Boolean Formulas

In a CFG, a path is determined by decisions made at branch points.

By assigning Boolean variables to branch conditions, we encode paths as logical formulas.

Consider the following IMP snippet:

```rust
if x > 0 {  // Decision A
    // ...
} else {
    // ...
}
if y == 5 { // Decision B
    valid = true;
}
```

Let $A$ represent the condition `x > 0` and $B$ represent `y == 5`.

Each path through the program corresponds to a conjunction of these Boolean variables.
We have four possible paths:

+ When both conditions are true (`x > 0` and `y == 5`): represented by $A and B$
+ When the first is true but second is false (`x > 0` and `y != 5`): represented by $A and not B$
+ When the first is false but second is true (`x <= 0` and `y == 5`): represented by $not A and B$
+ When both conditions are false (`x <= 0` and `y != 5`): represented by $not A and not B$

The set of all valid paths through the program is the disjunction (logical OR) of these four formulas.

To represent the set of states where `valid = true` (i.e., where decision $B$ is true), we write:
$ (A and B) or (not A and B) $

Using Boolean algebra, this simplifies to just $B$.

#insight-box[
  Set operations on states correspond directly to Boolean operations on formulas:
  - *Union* ($union$) $->$ Logical OR ($or$)
  - *Intersection* ($inter$) $->$ Logical AND ($and$)
  - *Empty Set* ($emptyset$) $->$ False ($0$)
  - *Universal Set* ($U$) $->$ True ($1$)
]

== Formal Definition of BDDs

A *Binary Decision Diagram (BDD)* is a graph-based data structure representing Boolean function $f: {0, 1}^n -> {0, 1}$.

Construction relies on the *Shannon Expansion*.

#definition(title: "Shannon Expansion")[
  Any Boolean function $f(x_1, ..., x_n)$ can be decomposed with respect to a variable $x_i$:
  $ f = (x_i and f_(x_i=1)) or (not x_i and f_(x_i=0)) $
  where:
  - $f_(x_i=1)$ is the function $f$ with $x_i$ set to True (Positive Cofactor).
  - $f_(x_i=0)$ is the function $f$ with $x_i$ set to False (Negative Cofactor).
]

Recursively applying this expansion yields a *Decision Tree*.

Since trees grow exponentially with variable count ($2^n$ leaves), we transform the tree into a *Directed Acyclic Graph (DAG)* for compactness.

=== Ordered Binary Decision Diagrams (OBDD)

A BDD is *Ordered* (OBDD) if variables appear in the same fixed order on all root-to-terminal paths.

For instance, given ordering $A < B < C$, every path tests $A$ before $B$, and $B$ before $C$.

#pitfall-box[
  *Variable Ordering Matters!*
  The size of a BDD depends heavily on the variable order.
  A good order keeps related variables close together.
  A bad order can cause exponential blowup.
  For example, for the function $(a_1 and b_1) or (a_2 and b_2) or ...$, the order $a_1, b_1, a_2, b_2...$ is linear, while $a_1, a_2, ..., b_1, b_2...$ is exponential.
]

=== Reduced BDDs

A BDD is *Reduced* (ROBDD) if it contains no redundant information.

We achieve this by repeatedly applying two reduction rules until the graph is minimal:

+ *Merge Isomorphic Nodes*:
  If two nodes $u$ and $v$ represent the same variable and have identical high and low children, they are equivalent.
  We keep one and redirect all edges pointing to the other.

+ *Eliminate Redundant Tests*:
  If a node $u$ has identical high and low children ($"high"(u) = "low"(u)$), the decision at $u$ does not affect the outcome.
  We remove $u$ and redirect incoming edges directly to its child.

#info-box(title: "Canonicity Property")[
  For a fixed variable ordering, the reduced OBDD for any Boolean function is *unique*.

  This property is crucial for verification: checking the equivalence of two functions $f equiv g$ reduces to checking if their BDD root nodes are identical (pointer equality), which is an $O(1)$ operation.
]

== ROBDD Invariants <sec-robdd-invariants>

The reduced ordered BDD representation satisfies three core invariants that guarantee canonicity:

+ *Invariant 1 (Ordering)*: Variables appear in strictly ascending order along every root-to-terminal path.
+ *Invariant 2 (No Redundant Tests)*: No internal node has identical high and low children.
+ *Invariant 3 (No Duplicate Nodes)*: No two distinct nodes share the same variable and identical child pair ("low", "high").

Together, these invariants ensure a one-to-one mapping between Boolean functions and their graph representation under a fixed order.

#definition(title: "Canonicity of ROBDDs")[
  Let $f$ be a Boolean function and let $pi$ be a fixed total order over its variables.
  There exists exactly one ROBDD $B$ such that $B$ represents $f$ and respects $pi$.
]

#intuition-box[
  The uniqueness result turns semantic equivalence checking into pointer equality, allowing $O(1)$ functional equivalence tests and enabling aggressive memoization.
]

=== Practical Check List

Before committing a node to the unique table we must enforce:
- Ordering: Reject construction if a child violates variable order.
- Redundancy: Collapse a node whose children match.
- Duplication: Reuse existing canonical node if present.

#implementation-box[
  The `Bdd` manager uses a hash consing table keyed by `(var, low, high)`.
  After computing low and high references for an apply step, it calls an insertion routine returning an existing node reference when possible.
]

Before diving deeper into BDD theory, it's worth getting hands-on experience with basic BDD operations.

The following example demonstrates variable creation, boolean operations, and the canonicity property in action:

#example-reference(
  "bdd_fundamentals",
  "basics.rs",
  "bdd_basics",
  [
    Hands-on introduction to BDD operations: creating variables, applying boolean operations (AND, OR, NOT, XOR), and observing canonicity.
    Perfect starting point for understanding BDDs practically.
  ],
)

== Visualizing Reduction

To illustrate these concepts, let us visualize the reduction of the decision tree for the function $(A and B) or C$, using the variable ordering $A < B < C$.

#figure(
  caption: [Comparison: Full Decision Tree vs. Reduced BDD for $(A and B) or C$],
  cetz.canvas({
    import cetz.draw: *

    let style-node = (fill: white, stroke: colors.primary + 1.5pt)
    let style-term-0 = (fill: colors.error.lighten(80%), stroke: colors.error + 1.5pt)
    let style-term-1 = (fill: colors.success.lighten(80%), stroke: colors.success + 1.5pt)

    let draw-node(pos, label, name) = {
      circle(pos, radius: 0.35, name: name, ..style-node)
      content(pos, text(weight: "bold")[#label])
    }

    let draw-term(pos, label, name) = {
      let s = if label == "0" { style-term-0 } else { style-term-1 }
      let (x, y) = pos
      let r = 0.3
      rect((x - r, y - r), (x + r, y + r), name: name, ..s, radius: 0.1)
      content(pos, text(weight: "bold")[#label])
    }

    let draw-edge(from, to, type) = {
      let s = if type == "high" {
        (paint: colors.primary)
      } else {
        (paint: colors.secondary, dash: "dashed")
      }
      line(from, to, stroke: s, mark: (end: ">", size: 0.15, stroke: (dash: "solid"), fill: s.paint))
    }

    // --- LEFT: Full Decision Tree ---
    let x-left = -5
    content((x-left, 4), text(weight: "bold")[Full Decision Tree])

    // Level 0: A
    draw-node((x-left, 3), [A], "t_root")

    // Level 1: B
    draw-node((x-left - 2, 1.5), [B], "t_b0")
    draw-node((x-left + 2, 1.5), [B], "t_b1")

    draw-edge("t_root", "t_b0", "low")
    draw-edge("t_root", "t_b1", "high")

    // Level 2: C
    draw-node((x-left - 3, 0), [C], "t_c00")
    draw-node((x-left - 1, 0), [C], "t_c01")
    draw-node((x-left + 1, 0), [C], "t_c10")
    draw-node((x-left + 3, 0), [C], "t_c11")

    draw-edge("t_b0", "t_c00", "low")
    draw-edge("t_b0", "t_c01", "high")
    draw-edge("t_b1", "t_c10", "low")
    draw-edge("t_b1", "t_c11", "high")

    // Level 3: Terminals
    let terminals = (0, 1, 0, 1, 0, 1, 1, 1)
    let x-start = x-left - 3.5
    for (i, val) in terminals.enumerate() {
      let name = "tt" + str(i)
      let x-pos = x-start + i * 1.0
      draw-term((x-pos, -1.5), str(val), name)

      // Connect to parent
      let parent-idx = int(i / 2)
      let parent-name = "t_c" + str(int(parent-idx / 2)) + str(int(calc.rem(parent-idx, 2)))
      let type = if calc.rem(i, 2) == 0 { "low" } else { "high" }
      draw-edge(parent-name, name, type)
    }

    content((x-left, -2.5), text(size: 0.8em, style: "italic")[Exponential growth: $2^n$ paths])

    // --- RIGHT: Reduced BDD ---
    let x-right = 4
    content((x-right, 4), text(weight: "bold")[Reduced BDD])

    draw-node((x-right, 3), [A], "r_a")
    draw-node((x-right + 1.5, 1.5), [B], "r_b")
    draw-node((x-right, 0), [C], "r_c")

    draw-term((x-right - 1.5, -1.5), "0", "r_0")
    draw-term((x-right + 1.5, -1.5), "1", "r_1")

    // Edges for Reduced
    // A low -> C
    draw-edge("r_a", "r_c", "low")
    // A high -> B
    draw-edge("r_a", "r_b", "high")

    // B low -> C (Sharing!)
    draw-edge("r_b", "r_c", "low")
    // B high -> 1
    draw-edge("r_b", "r_1", "high")

    // C low -> 0
    draw-edge("r_c", "r_0", "low")
    // C high -> 1
    draw-edge("r_c", "r_1", "high")

    content((x-right, -2.5), text(size: 0.8em, style: "italic")[Shared nodes C and 1])
  }),
) <fig:bdd-comparison>

@fig:bdd-comparison demonstrates the dramatic difference between the tree and graph representations:

- *Left (Decision Tree)*: The tree explicitly enumerates all 8 paths.
  Note the redundancy: the subtrees for $C$ are repeated multiple times.
- *Right (Reduced BDD)*: The graph is significantly more compact due to reduction:
  - *Isomorphism*: The node $C$ is shared by both branches of $B$.
  - *Redundant Test Elimination*: Notice the edge from $A$ (low) directly to $C$.
    If $A$ is false, the expression $(A and B) or C$ simplifies to $(0 and B) or C$, which equals $C$.
    This means the value of $B$ is irrelevant.
    The redundant $B$ node is removed, and $A$ connects directly to $C$.


== Complexity of Core Operations <sec-bdd-complexity>

Operation cost depends on input BDD sizes and variable ordering quality, not raw path count.
Let $n$ be variable count and $|B|$ denote node count.

#table(
  columns: (auto, 1fr),
  align: (left, left),
  [*Operation*], [*Complexity*],
  [Apply (Binary Boolean)], [$O(|B_f| times |B_g|)$ worst case; typically near-linear with caching],
  [Negation], [$O(|B|)$ via complement edge toggling],
  [Restriction / Cofactor], [$O(|B|)$ traversing affected nodes],
  [Quantification], [Potentially $O(|B| times n)$; reduced by variable clustering],
  [Variable Reordering], [Heuristic sifting $O(n^2)$ swaps],
)

#pitfall-box[
  *Worst Case Alert*: Adversarial formulas destroy sharing and approach exponential size, e.g., integer multiplication bit level carry dependencies.
]

#implementation-box[
  Performance hotspots concentrate in apply and quantification routines.
  Instrument counters for cache hit ratio and node creation frequency to guide reordering heuristics.
]

== Research Spotlight: Variable Ordering Heuristics <sec-ordering-spotlight>

Variable ordering dominates BDD size, thus memory and time.
Several approaches exist:

=== Static Heuristics

Apply domain-driven grouping once at initialization.
For example, place related bitfields adjacent to each other.
This leverages problem structure without runtime overhead.

=== Dynamic Sifting

Iteratively move a variable up and down through the ordering to minimize BDD size.
At each position, measure the total node count and keep the best placement.
This local optimization works well in practice.

=== Genetic and Annealing Approaches

Use global stochastic search to explore the space of variable permutations.
Suitable for stable benchmarks where investment in finding good orderings pays off.
These methods can escape local minima that trap greedy approaches.

=== Machine Learning Guidance

Extract features from BDD structure (node fanout, support size, etc.) and feed them to ranking models.
The model predicts which variable swap is most promising.
This combines the power of search with learned heuristics from previous problems.

#historical-note(person: "R. E. Bryant", year: 1986, title: "Graph Based Algorithms for Boolean Function Manipulation")[
  Bryant's seminal work introduced reduced ordered BDDs and established foundational complexity tradeoffs still optimized with modern heuristics.
]

#implementation-box[
  Integrate a *lazy sifting trigger*: when node count crosses a threshold factor versus baseline, schedule a limited window reordering batch.
]

== Exercises <sec-bdd-exercises>

#exercise-box(difficulty: "Easy")[
  Construct the full decision tree and reduced BDD for $(A or B) and (C or D)$ under order $A < B < C < D$.
  Count nodes and compare reduction ratio.
]
#exercise-box(difficulty: "Medium")[
  Show that two distinct Boolean formulas can share an identical ROBDD when variable ordering differs.
  Provide explicit counterexample and explain resolution.
]
#exercise-box(difficulty: "Medium")[
  Instrument the `apply` operation to record cache hits and misses for random 50 variable CNF instances.
  Plot hit ratio vs clause density.
]
#exercise-box(difficulty: "Hard")[
  Propose a scoring function for dynamic ordering decisions using features: variable level, node fanout, subtree size.
  Evaluate on synthetic benchmark set.
]
#exercise-box(difficulty: "Hard")[
  Implement existential quantification of a subset of variables and empirically measure node count delta for structured vs random formulas.
]

== The `SymbolicManager`

In our Analyzer, we bridge the gap between the "semantic" AST world (nodes like `x > 0`) and the "numeric" BDD library world (integer variables like 1, 2, 3).

We implement a `SymbolicManager` to handle translation and ensure consistency.

#info-box(title: "Design Pattern")[
  The `SymbolicManager` acts as a facade over the raw BDD manager.
  It~maintains a `HashMap<Condition, Ref>` to ensure that identical AST conditions always map to the same BDD variable.
]

The structure is defined as follows:

```rust
// Ensure Condition derives Hash and Eq!
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Condition {
    // ... variants ...
}

pub struct SymbolicManager {
    bdd: Bdd,
    mapping: HashMap<Condition, usize>, // Maps AST conditions to BDD variable IDs
    next_var_id: usize,
}

impl SymbolicManager {
    /// Get or create the BDD variable for a condition
    pub fn get_condition(&mut self, c: &Condition) -> Ref {
        if let Some(&id) = self.mapping.get(c) {
            return self.bdd.mk_var(id as u32);
        }

        let id = self.next_var_id;
        self.next_var_id += 1;
        self.mapping.insert(c.clone(), id);
        self.bdd.mk_var(id as u32)
    }
}
```

#intuition-box[
  *What is a `Ref`?*
  A `Ref` is just a lightweight integer handle (like a pointer or an ID).
  It has no meaning on its own.
  You must always pass it back to the `Bdd` manager to perform operations.
  Think of it like a "file descriptor" --- you need the OS (Manager) to read the file.
]

The workflow:
+ When analyzer encounters a condition (e.g., `x > 0`) for the first time, manager allocates a new BDD variable (e.g., index 1) and stores the mapping.
+ When the same condition appears later, manager retrieves existing mapping and returns the same BDD variable.

This guarantees the *same* logical condition always gets the *same* BDD variable, preserving logical consistency.

== Why BDDs Solve State Explosion

@ch-control-flow showed: $N$ branches can create $2^N$ paths.

BDDs mitigate this by exploiting structure and independence.

When decisions don't interact (e.g., independent checks), BDD size grows *linearly* with variable count, not exponentially.

For example, consider 100 independent `if` statements:
Consider the difference in representation size:

With explicit path enumeration, we would need to store $2^100$ distinct paths.
This number is astronomically large --- more than the number of atoms in the observable universe.
Storing this explicitly is computationally intractable.

With the BDD representation, we only need $2 times 100 = 200$ nodes.
Each chain contributes exactly 2 nodes (one decision node pointing to True, one to False).
This linear size makes the representation trivial to store and manipulate.

The BDD automatically factors out independence.

Explosion typically occurs only when variables are heavily correlated in complex ways (e.g., cryptographic hashes).
This is less common in typical control logic.


#chapter-summary[
  This chapter introduced Binary Decision Diagrams as the symbolic representation backbone for path-sensitive analysis.

  The fundamental insight is that *sets of program states can be represented as Boolean functions*, mapping variable valuations to true (state included) or false (state excluded).
  *BDDs provide compact, canonical graph representations* of these functions through systematic sharing of common substructure.

  Two *reduction rules* --- eliminating isomorphic subgraphs and removing redundant tests --- enable exponential compression while preserving canonicity.
  This means equivalent Boolean functions always produce identical BDD structures, making equality testing trivial.

  The *`SymbolicManager`* bridges program syntax and BDD representation by mapping conditions to BDD variables consistently.
  This canonicalization ensures that identical program conditions always map to the same BDD variable, enabling efficient reuse and comparison.

  With these foundations in place, we're ready to implement the concrete analysis infrastructure that leverages BDDs for symbolic program analysis.
]

#info-box(title: "Explore BDD Operations")[
  To see boolean operations in action, check out the example demonstrating AND, OR, XOR, and their algebraic properties like De Morgan's laws and absorption.
]

#example-reference(
  "bdd_fundamentals",
  "boolean_ops.rs",
  "bdd_boolean_ops",
  [
    Demonstration of standard boolean operations on BDDs.
    Includes verification of De Morgan's laws and other identities.
  ],
)
