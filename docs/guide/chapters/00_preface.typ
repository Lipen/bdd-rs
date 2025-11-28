#import "../theme.typ": *

#counter(heading).update(0)

#heading(numbering: none)[Preface] <preface>

== Purpose of This Guide

This guide provides a comprehensive treatment of *Binary Decision Diagrams (BDDs)* --- from theoretical foundations to practical implementation.

Whether you are a student learning about formal methods, a practitioner building verification tools, or a researcher exploring symbolic computation, this guide offers the depth and breadth you need.

== What You Will Learn

By the end of this guide, you will understand:

- *Theory*: The mathematical foundations of BDDs, including Boolean algebra, canonical forms, and complexity properties.

- *Implementation*: How to build an efficient BDD library, covering data structures, algorithms, and engineering trade-offs.

- *Applications*: Where BDDs excel in practice --- model checking, configuration management, combinatorial optimization, and beyond.

- *Trade-offs*: When to use BDDs versus alternatives like SAT solvers, and how different design choices affect performance.

== How to Read This Guide

*Path 1: Foundations First*

Read sequentially through Parts I and II.
This builds complete understanding from first principles.
Best for students and those new to BDDs.

*Path 2: Implementation Focus*

Skim Part I for notation, then dive into Part II.
Reference Part III for advanced techniques as needed.
Best for engineers building BDD-based systems.

*Path 3: Application-Driven*

Start with Part IV to see BDDs in action.
Return to earlier parts when you encounter unfamiliar concepts.
Best for practitioners with specific use cases.

*Path 4: Comparative Analysis*

Jump to Part V for ecosystem overview and comparisons.
Use earlier parts as reference.
Best for those evaluating BDD libraries or approaches.

== Accompanying Code

This guide is developed alongside the `bdd-rs` library.
Code examples throughout use Rust, but concepts transfer to any language.

```rust
// A taste of what's to come
use bdd_rs::bdd::Bdd;

let bdd = Bdd::default();
let x = bdd.mk_var(1);
let y = bdd.mk_var(2);
let f = bdd.apply_and(x, bdd.apply_not(y));  // f = x ∧ ¬y
```

== Acknowledgments

This guide builds upon decades of BDD research, starting with Randal Bryant's seminal 1986 paper.
We acknowledge the contributions of the formal methods community and the developers of BDD libraries that informed this work.
