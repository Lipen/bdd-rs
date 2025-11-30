#import "../theme.typ": *

#counter(heading).update(0)

#heading(numbering: none)[Preface] <preface>

== Why This Guide Exists

In 1994, a single floating-point division bug cost Intel \$475 million.
The Pentium FDIV error slipped past traditional testing because exhaustive checking was impossible --- billions of input combinations existed.
After that expensive lesson, Intel turned to *formal verification*, and Binary Decision Diagrams became essential infrastructure.

BDDs are one of computer science's quiet success stories.
They power hardware verification at Intel, AMD, and every major chip manufacturer.
They enable SAT solvers to prune search spaces.
They verify protocols, validate configurations, and solve combinatorial puzzles.
Yet despite their importance, good learning resources are scarce.

This guide fills that gap.
Whether you are a student encountering formal methods for the first time, an engineer building verification tools, or a researcher pushing the boundaries of symbolic computation, you will find what you need here.

== What You Will Learn

By working through this guide, you will understand:

- *Theory*: The mathematical foundations --- Boolean algebra, Shannon expansion, the canonicity theorem that makes BDDs magical.

- *Implementation*: How to build an efficient BDD library from scratch, including data structures, algorithms, and the non-obvious engineering decisions.

- *Applications*: Where BDDs shine --- model checking, configuration management, combinatorial optimization --- and where they struggle.

- *Trade-offs*: When to reach for BDDs versus SAT solvers, and how design choices (variable ordering, complement edges, caching strategies) affect performance by orders of magnitude.

== How to Read This Guide

There is no single "right" path.
Choose based on your goals:

*Path 1: Theory First*

Read @part-foundations thoroughly, then @part-implementation.
Build understanding from first principles.
Best for students and those who want the complete picture.

*Path 2: Implementation Focus*

Skim @part-foundations for notation, dive into @part-implementation.
Reference @part-advanced when you hit advanced techniques.
Best for engineers building BDD-based systems.

*Path 3: Application-Driven*

Start with @part-applications to see BDDs solving real problems.
Backtrack to earlier parts when curiosity strikes.
Best for practitioners with specific use cases in mind.

*Path 4: Comparative Analysis*

Jump to @part-ecosystem for the lay of the land.
Use earlier chapters as reference material.
Best for those evaluating BDD libraries or architectural approaches.

== The bdd-rs Library

This guide accompanies `bdd-rs`, a BDD library written in Rust.
The code examples use Rust syntax, but the concepts are universal --- they apply to CUDD, BuDDy, or any BDD implementation.

```rust
use bdd_rs::bdd::Bdd;

let bdd = Bdd::default();
let x = bdd.mk_var(1);
let y = bdd.mk_var(2);
let f = bdd.apply_and(x, -y);  // f = x ∧ ¬y

// O(1) checks after construction
assert!(!bdd.is_zero(f));  // Satisfiable
assert!(!bdd.is_one(f));   // Not a tautology
```

== A Note on Style

This guide prioritizes *understanding* over encyclopedic coverage.
When a choice exists between being comprehensive and being clear, clarity wins.

You will find:
- *Diagrams* that visualize concepts
- *Code* that shows how ideas become implementations
- *Examples* that ground abstractions in concrete problems
- *Insights* that explain *why*, not just *how*

== Acknowledgments

BDDs emerged from decades of research, starting with Lee's 1959 work on decision programs and crystallizing in Bryant's landmark 1986 paper.
This guide builds on that foundation and on the practical wisdom embodied in libraries like CUDD, BuDDy, and Sylvan.

We thank the formal methods community for creating such a rich field to explore.
