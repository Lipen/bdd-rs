#import "../../theme.typ": *

= Introduction <ch-introduction>

Binary Decision Diagrams have become one of the most successful data structures in computer science.
Since their introduction in the 1980s, they have enabled breakthroughs in hardware verification, transformed how we reason about Boolean functions, and found applications from configuration management to artificial intelligence.

This chapter introduces BDDs, explains why they matter, and provides historical context for understanding their development and impact.

== The Challenge of Boolean Reasoning

Boolean functions are everywhere.
A digital circuit computes a Boolean function.
A software condition evaluates to true or false.
A configuration is valid or invalid.
A formal specification is satisfied or violated.

Yet reasoning about Boolean functions is surprisingly hard.
Consider a simple question: given two Boolean formulas, do they compute the same function?

#example-box(title: "The Equivalence Problem")[
  Are these two formulas equivalent?
  $ f = (a and b) or (a and c) or (b and c) $
  $ g = (a or b) and (a or c) and (b or c) $

  To check by enumeration, we need $2^3 = 8$ evaluations.
  For $n$ variables, we need $2^n$ evaluations --- exponential growth.
]

This exponential blowup is not an artifact of naive algorithms.
Boolean satisfiability (SAT) is NP-complete, and equivalence checking is co-NP-complete.
No polynomial-time algorithm exists unless P = NP.

Yet practical systems routinely reason about Boolean functions with hundreds or thousands of variables.
How is this possible?

The answer lies in *representation*.
While the worst case is exponential, many practical Boolean functions have structure that admits compact representation.
BDDs exploit this structure, providing polynomial-time operations for functions that would be intractable otherwise.

=== What is a BDD?

A *Binary Decision Diagram* (BDD) represents a Boolean function as a directed acyclic graph.
Each internal node corresponds to a Boolean variable and has two outgoing edges: one for the case where the variable is false (the *low* edge), and one for the case where it is true (the *high* edge).
Terminal nodes represent the constant functions $0$ and $1$.

To evaluate a BDD on an input assignment, start at the root and follow edges according to the variable values until reaching a terminal.
The terminal's label gives the function's value.

The key insight is that BDDs can share common subgraphs.
If two paths lead to the same subfunction, they point to the same node.
This *sharing* is what makes BDDs compact.

== A Brief History

The history of BDDs begins before the term was coined.

=== Early Work (1959--1978)

In 1959, *C. Y. Lee* introduced *binary decision programs* for representing switching circuits.
His work laid the groundwork for decision-diagram-based representations but did not address the representation's uniqueness.

In 1978, *S. B. Akers* formalized *Binary Decision Diagrams* and studied their properties.
However, these early BDDs could represent the same function in many different ways, making equivalence checking expensive.

=== Bryant's Breakthrough (1986)

The transformative contribution came from *Randal Bryant* in 1986.
His paper "Graph-Based Algorithms for Boolean Function Manipulation" introduced two crucial refinements:

+ *Ordering*: Variables appear in the same order on all paths from root to terminal.
+ *Reduction*: Eliminate redundant nodes and merge isomorphic subgraphs.

These constraints yield *Reduced Ordered Binary Decision Diagrams* (ROBDDs), which have a remarkable property: for a fixed variable ordering, every Boolean function has exactly one ROBDD.
This *canonicity* means equivalence checking becomes trivial --- two functions are equivalent if and only if their ROBDDs are identical (pointer comparison!).

Bryant also provided efficient algorithms for Boolean operations, running in time proportional to the product of the input BDD sizes.

#insight-box[
  Bryant's 1986 paper is one of the most cited in computer science.
  The combination of canonicity and efficient algorithms made BDDs practical for industrial-scale verification.
]

=== The Verification Revolution (1987--1995)

BDDs immediately found application in hardware verification.
In 1987, *Burch, Clarke, McMillan, Dill, and Hwang* demonstrated *symbolic model checking*, verifying systems with $10^20$ states --- far beyond what explicit enumeration could handle.

This work launched a revolution in formal verification.
Suddenly, it was possible to automatically verify properties of complex digital circuits.
Companies like Intel adopted BDD-based tools to catch bugs before silicon fabrication.

=== Maturation and Alternatives (1995--present)

By the mid-1990s, BDDs had become a standard tool, but their limitations were also understood.
Some functions have exponentially large BDDs regardless of variable ordering.
Memory consumption can be unpredictable.

Alternative approaches emerged:
- *SAT solvers* using conflict-driven clause learning (CDCL) proved effective for many problems where BDDs struggle.
- *BDD variants* like ZDDs (for combinatorial sets) and ADDs (for multi-valued functions) extended the paradigm.
- *Hybrid methods* combining BDDs with SAT solvers leverage the strengths of each.

Today, BDDs remain essential where their strengths matter: canonical representation, efficient counting, all-solutions enumeration, and symbolic manipulation of state spaces.

== What Makes BDDs Special?

Three properties distinguish BDDs from other Boolean function representations:

=== Canonicity

For a fixed variable ordering, every Boolean function has exactly one reduced ordered BDD.
This property is powerful:

- *Equivalence checking*: Two BDDs represent the same function if and only if they are identical.
  With hash consing, this reduces to pointer comparison: $O(1)$.

- *Satisfiability*: A function is unsatisfiable if and only if its BDD is the $0$-terminal.
  This is also $O(1)$ after construction.

- *Tautology checking*: A function is a tautology if and only if its BDD is the $1$-terminal.

No other compact representation offers these constant-time queries.
Truth tables are canonical but exponentially large.
CNF and DNF are compact but non-canonical.

=== Efficient Operations

BDD operations have polynomial complexity in the sizes of the input BDDs:

#table(
  columns: (auto, auto),
  align: (left, center),
  table.header([*Operation*], [*Complexity*]),
  [Negation (with complement edges)], [$O(1)$],
  [AND, OR, XOR, etc.], [$O(|f| dot |g|)$],
  [Equivalence check], [$O(1)$],
  [Satisfiability check], [$O(1)$],
  [Model counting], [$O(|f|)$],
)

The $O(|f| dot |g|)$ bound for binary operations comes from memoization: each pair of nodes from the two BDDs is processed at most once.

=== Sharing

BDDs naturally share common subfunctions.
When building $f and g$ and $f or g$, the subgraph for $f$ is constructed once and reused.
This sharing arises automatically from *hash consing*: before creating a node, we check if an identical node already exists.

In a manager-centric implementation like `bdd-rs`, all BDDs share a single node pool.
Memory is proportional to the total number of distinct subfunctions, not the total number of BDDs.

== When BDDs Work Well

BDDs excel when the Boolean function has structure that permits compact representation:

*Sequential circuits and finite-state machines.*
Transition relations of digital circuits often have small BDDs because related bits are tested together.
State reachability can be computed symbolically, avoiding enumeration of individual states.

*Configuration constraints.*
Feature models and product line constraints typically yield manageable BDDs.
The hierarchical structure of features often suggests good variable orderings.

*Symmetric and threshold functions.*
Functions like "at least $k$ of $n$ variables are true" have polynomial-size BDDs.
Many constraints arising in combinatorial problems have this form.

*Problems requiring counting or enumeration.*
When you need to count satisfying assignments or enumerate all solutions, BDDs shine.
SAT solvers can find *one* solution quickly but struggle with *all* solutions.

== When BDDs Struggle

BDDs have well-known limitations:

*Integer multiplication.*
The function "output bits of $n$-bit multiplier" requires exponential BDD size regardless of variable ordering.
This is not a limitation of the algorithm but a fundamental property of the function.

*Large unstructured problems.*
Random Boolean functions or problems without exploitable structure tend to produce large BDDs.

*Dynamic problems.*
If the optimal variable ordering changes as constraints are added, maintaining good BDD size requires expensive reordering operations.

*Memory consumption.*
BDD operations can create many intermediate nodes.
Without garbage collection, memory can grow rapidly.

#warning-box(title: "No Silver Bullet")[
  BDDs are not universally superior to SAT solvers or other techniques.
  The choice depends on the problem structure and the queries needed.
  For single satisfiability queries on large formulas, modern SAT solvers often win.
  For repeated queries, counting, or symbolic state-space exploration, BDDs often win.
]

== The bdd-rs Library

This guide accompanies `bdd-rs`, a BDD library written in Rust.
Its design reflects lessons from decades of BDD research:

```rust
use bdd_rs::bdd::Bdd;

// Create a BDD manager
let bdd = Bdd::default();

// Variables are 1-indexed
let x = bdd.mk_var(1);
let y = bdd.mk_var(2);
let z = bdd.mk_var(3);

// Build a formula: (x ∧ y) ∨ z
let f = bdd.apply_or(bdd.apply_and(x, y), z);

// Constant-time queries
assert!(!bdd.is_zero(f));  // satisfiable?
assert!(!bdd.is_one(f));   // tautology?

// Count solutions (8 total assignments, how many satisfy f?)
let count = bdd.sat_count(f, 3);
println!("Solutions: {}", count);  // 5
```

Key design choices in `bdd-rs`:

- *Manager-centric architecture*: All operations go through the `Bdd` manager, ensuring hash consing and canonical form.
- *Complement edges*: Negation is $O(1)$, implemented as a single bit flip.
- *Type-safe handles*: `Ref` is a 32-bit handle; accidental misuse is caught at compile time.
- *Rust's safety guarantees*: Memory safety without garbage collector overhead.

== Guide Overview

The remainder of this guide is organized as follows:

*Part I (Chapters 2--5)* establishes the theoretical foundations: Boolean functions, Shannon expansion, the formal BDD definition, the canonicity theorem, and core algorithms.

*Part II (Chapters 6--11)* covers implementation: manager architecture, node representation, unique tables, the Apply algorithm, caching, and complement edges.

*Part III (Chapters 12--15)* explores advanced topics: variable ordering, garbage collection, quantification, and BDD variants.

*Part IV (Chapters 16--19)* demonstrates applications: model checking, combinatorial problems, symbolic execution, and configuration management.

*Part V (Chapters 20--22)* surveys the ecosystem: library comparisons, design trade-offs, and future directions.

Each chapter builds on previous ones, but readers with specific interests can skip ahead using the cross-references provided.
