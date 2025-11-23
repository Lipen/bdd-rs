#import "../theme.typ": *

#import "@preview/numbly:0.1.0"
#set heading(outlined: false)
#set heading(numbering: numbly.numbly(
  "",
  "{2}.",
  "{2}.{3}",
))

#heading(numbering: none, outlined: true)[Preface]

#reading-path(path: "essential")

Welcome to this comprehensive guide on abstract interpretation combined with Binary Decision Diagrams (BDDs).
Whether you're a student encountering formal methods for the first time, a practitioner seeking to apply verification techniques, or a researcher exploring new analysis approaches, this guide meets you where you are and takes you further.

== Who This Guide Is For

This guide serves multiple audiences with diverse backgrounds and goals:

*Complete Beginners:*
New to program verification and formal methods?
Start with @part-i.
The guide builds intuition through concrete examples before introducing mathematical formalism.
No prior knowledge of abstract interpretation or BDDs assumed --- just basic programming experience and curiosity.

*Practitioners:*
Software engineers interested in applying verification techniques?
Focus on @part-i for conceptual understanding, then jump to @part-iii (@ch-security, @ch-performance) for implementation details and benchmarks.

*Researchers and Graduate Students:*
Already familiar with program analysis basics?
Skim @part-i and dive into @part-ii, which provides complete mathematical foundations, formal proofs, and connections to research literature.

*Educators:*
This guide is structured to support a one-semester graduate course on program analysis, with progressive exercises, worked examples, and discussion prompts throughout.

== What Makes This Guide Different

Unlike traditional academic papers or reference manuals, this guide:

- *Tells a story*: Concepts build progressively, motivating each idea before formalizing it.
- *Shows real code*: Every concept is backed by working Rust implementations from the `bdd-rs` library.
- *Balances rigor and intuition*: Mathematical precision maintained while providing accessible explanations.
- *Connects to practice*: Real-world applications --- from security analysis to smart contracts --- demonstrate where these techniques shine.
- *Provides multiple paths*: Skip sections that don't match your goals, or deep-dive into formal theory where interested.

== Structure of This Guide

This guide is organized into three parts, each serving a distinct purpose:

*@part-i: Gentle Introduction* (@ch-abstraction through @ch-symbolic-executor) starts from first principles.
We build intuition about program abstraction, control flow, and symbolic representations through concrete examples.
Core concepts like abstract domains, lattice operations, and BDD-based path sensitivity emerge naturally from practical problems.
This part is accessible to anyone with programming background.

*@part-ii: Deep Dive* (@ch-lattice-theory through @ch-precision-techniques) provides rigorous mathematical foundations.
We develop complete lattice theory, fixpoint theorems, Galois connections, and domain combination operators.
Each chapter includes formal definitions, proofs, and implementation guidance.
Topics include abstract transformers (@ch-advanced-galois), reduced products (@ch-domain-combinations), BDD path sensitivity (@ch-bdd-path), and specialized domains for strings (@ch-strings-automata), pointers (@ch-points-types), and precision refinement (@ch-precision-techniques).

*@part-iii: Applications & Future Directions* (@ch-security through @ch-conclusion) bridges theory and practice.
We explore security analysis with taint tracking, inter-procedural analysis with context sensitivity, performance optimization techniques, and the emerging integration of AI with formal methods.
The guide concludes with a complete case study analyzing an access control system and directions for future research.

== How to Use This Guide

=== For Learning (First Time Through)

+ Start with the *Prologue* to understand why static analysis matters.
+ Work through *@part-i* sequentially --- concepts build on each other.
+ Try the code examples from the `bdd-rs` repository as you go.
+ When encountering formalism in @part-ii, don't panic --- intuition comes first, rigor follows.
+ Use the *exercises* (marked with difficulty levels) to test understanding.
+ Skip @part-ii proofs on first reading if they feel overwhelming --- return when ready.

=== For Reference (Coming Back)

- Use the *table of contents* and *cross-references* to navigate directly to topics.
- *Info boxes* and *margin notes* provide quick refreshers on key concepts.
- *Example references* link to concrete code in the repository.
- The *index* (when complete) will enable rapid lookup of specific terms.

=== Reading Paths

We've marked sections with icons to help you navigate:

#grid(
  columns: 2,
  column-gutter: 1em,
  inset: 5pt,

  reading-path(path: "essential"), [Must-read for everyone],

  reading-path(path: "beginner"), [Gentler content for newcomers],

  reading-path(path: "advanced"), [Formal details and proofs],

  reading-path(path: "implementation"), [Code and practical details],
)

== Prerequisites

*Assumed knowledge:*
- Basic programming experience (preferably in Rust, but examples are explained).
- Undergraduate discrete mathematics (sets, functions, relations, basic logic).
- Familiarity with graphs and trees.

*Helpful but not required:*
- Understanding of compilers or program analysis.
- Experience with functional programming patterns.
- Exposure to Boolean algebra or propositional logic.

*For @part-ii (advanced readers):*
- Mathematical maturity for reading proofs.
- Comfort with order theory (partially ordered sets, lattices).
- Familiarity with fixpoint theorems.

Don't let prerequisites intimidate you --- the guide builds concepts incrementally.
When mathematical background is needed, we provide intuition before formalism.

== Companion Resources

This guide is part of a comprehensive ecosystem:

- *`bdd-rs` library*: Open-source Rust implementation at #link("https://github.com/Lipen/bdd-rs")[github.com/Lipen/bdd-rs].
- *Code examples*: All examples from this guide are in the `bdd-rs/examples/abstract-interpretation/` directory.
- *Test suite*: Comprehensive tests validate correctness of implementations.

All code is open-source and contributions are welcome.

== Acknowledgments

This guide builds on decades of foundational research.
Abstract interpretation was pioneered by Patrick and Radhia Cousot in their seminal work.
Binary Decision Diagrams were introduced by Randal Bryant, revolutionizing symbolic verification.
Countless researchers have extended these foundations --- their work is cited throughout.

The `bdd-rs` library represents a modern synthesis of these ideas, optimized for Rust's ownership model and designed for practical deployment.

Thank you to the open-source community for feedback, bug reports, and contributions that have improved both the library and this guide.

== Let's Begin

Program verification is not just an academic exercise --- it's a necessity for building reliable, secure systems.
Testing alone cannot guarantee correctness in modern software.
We need tools that reason about *all* possible behaviors, not just sampled executions.

This guide equips you with the theory and practice of BDD-guided abstract interpretation:
- *Theory*: Understand why these techniques work and when they apply.
- *Practice*: Implement analyses using the `bdd-rs` library.
- *Applications*: Apply these tools to real security and verification problems.

Whether you're here to understand how verification works, to apply these techniques to your own code, or to advance the state of the art, this guide aims to be your companion.

Let's dive in!
