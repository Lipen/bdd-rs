#import "theme.typ": *

// ============================================================================
// Abstract Interpretation with BDDs: A Gentle Guide
// ============================================================================

#show: apply-guide-theme.with(
  title: "Abstract Interpretation with BDDs",
  subtitle: "A Gentle Guide to Program Verification",
  authors: ("The bdd-rs Contributors",),
  date: datetime.today().display("[month repr:long] [day], [year]"),
  header-title: "Abstract Interpretation with BDDs",
)

// ============================================================================
// Title Page
// ============================================================================

#make-title(
  [Abstract Interpretation with BDDs],
  subtitle: [A Gentle Guide to Program Verification],
  authors: ("The bdd-rs Contributors",),
  date: datetime.today().display("[month repr:long] [day], [year]"),
)

// ============================================================================
// Preface
// ============================================================================

#set page(numbering: "i")
#counter(page).update(1)

= Preface

#reading-path(path: "essential")

Welcome to this comprehensive guide on abstract interpretation combined with Binary Decision Diagrams (BDDs).
Whether you're a student encountering formal methods for the first time, a practitioner seeking to apply verification techniques, or a researcher exploring new analysis approaches, this guide is designed to meet you where you are and take you further.

== Who This Guide Is For

This guide serves multiple audiences, each with different backgrounds and goals:

*Complete Beginners* #reading-path(path: "beginner"):
If you're new to program verification and formal methods, start with Part I.
We'll build intuition through concrete examples before introducing mathematical formalism.
No prior knowledge of abstract interpretation or BDDs is assumed—just basic programming experience and curiosity.

*Practitioners* #reading-path(path: "implementation"):
If you're a software engineer interested in applying verification techniques to real systems, focus on Part I (Chapters 1-5) for conceptual understanding, then jump to Part II (Chapter 12) for implementation details and benchmarks.

*Researchers and Students* #reading-path(path: "advanced"):
If you're already familiar with program analysis basics, you might skim Part I and dive into Part II, which provides complete mathematical foundations, proofs, and connections to research literature.

*Educators*: This guide is structured to support a one-semester course on program analysis, with progressive exercises, worked examples, and discussion prompts throughout.

== What Makes This Guide Different

Unlike traditional academic papers or reference manuals, this guide:

- *Tells a story*:
  We build concepts progressively, motivating each idea before formalizing it
- *Shows real code*:
  Every concept is backed by working Rust implementations in the bdd-rs library
- *Balances rigor and intuition*:
  We maintain mathematical precision while providing accessible explanations
- *Connects to practice*:
  Real-world applications and case studies demonstrate where these techniques shine
- *Provides multiple paths*:
  Skip sections that don't match your goals, or deep-dive where interested

== Structure of This Guide

This guide is organized into three parts:

*Part I: Gentle Introduction (Chapters 1-6)* starts from first principles, building intuition about program abstraction, control flow, and symbolic representations.
Through running examples like heater controllers and traffic lights, we motivate why BDD-based path-sensitive analysis matters.
This part is accessible to anyone with programming background.

*Part II: Deep Dive (Chapters 7-15)* provides complete theoretical foundations, formal proofs, implementation techniques, and research connections.
This part enables readers to understand the mathematics deeply and implement their own analyses.

*Part III: Appendices* offer reference material: mathematical prerequisites, complete code walkthroughs, benchmark specifications, and an annotated bibliography.

== How to Use This Guide

=== For Learning (First Time Through)

+ Start with the *Prologue* to understand the motivation
+ Work through *Part I* sequentially, trying the examples
+ When you encounter formalism in Part II, don't panic—we build intuition first
+ Use the *exercises* to test your understanding
+ Refer to *appendices* when you need background material

=== For Reference (Coming Back)

- Use the *table of contents* and *index* to find specific topics
- *Margin notes* provide quick refreshers on key concepts
- *Cross-references* link related sections
- The *glossary* defines all technical terms

=== Reading Paths

We've marked sections with icons to help you navigate:

#grid(
  columns: 2,
  column-gutter: 1em,
  row-gutter: 0.8em,

  reading-path(path: "essential"), [Must-read for everyone],

  reading-path(path: "beginner"), [Gentler content for newcomers],

  reading-path(path: "advanced"), [Formal details and proofs],

  reading-path(path: "implementation"), [Code and practical details],
)

== Prerequisites

*Assumed knowledge:*
- Basic programming experience (any language)
- Undergraduate-level discrete mathematics (sets, functions, logic)
- Familiarity with graphs and trees

*Helpful but not required:*
- Experience with Rust or functional programming
- Previous exposure to program analysis or compilers
- Basic understanding of logic and Boolean algebra

If you're missing background in any area, Appendix A provides concise summaries of mathematical prerequisites.

== Companion Resources

This guide is part of a larger ecosystem:

- *bdd-rs library*: Open-source Rust implementation at #link("https://github.com/Lipen/bdd-rs")
- *Code examples*: All examples from this guide are in the repository
- *Research paper*: A concise academic paper presents the core contributions
- *Benchmarks*: Complete benchmark suite for reproducing results

== Acknowledgments

This guide builds on decades of research in abstract interpretation, pioneered by Patrick and Radhia Cousot, and symbolic verification using BDDs, advanced by Randal Bryant and many others.
We're grateful to the formal methods community for creating the foundations on which this work stands.

The bdd-rs library and this guide are open-source projects, welcoming contributions from the community.
Thank you to everyone who has contributed code, feedback, and insights.

== Let's Begin

Program verification is a journey from informal reasoning to mathematical certainty.
This guide will equip you with powerful tools for analyzing programs automatically, guaranteeing properties that testing alone cannot ensure.

Whether you're here to understand how verification works, to apply these techniques to your own code, or to advance the state of the art, we hope you find this guide valuable.

Let's dive in!

#pagebreak()

// ============================================================================
// Table of Contents
// ============================================================================

#set page(numbering: "i")

#outline(
  title: text(
    font: fonts.heading,
    weight: "bold",
    fill: colors.primary,
    [Contents],
  ),
  indent: auto,
  depth: 2,
)

#pagebreak()

// ============================================================================
// Part I: Gentle Introduction
// ============================================================================

#set page(numbering: "1")
#counter(page).update(1)

#include "chapters/part1_introduction/00_prologue.typ"

#include "chapters/part1_introduction/01_abstraction.typ"

#include "chapters/part1_introduction/02_control_flow.typ"

#include "chapters/part1_introduction/03_bdds.typ"

#include "chapters/part1_introduction/04_bdd_programming.typ"

#include "chapters/part1_introduction/05_combining.typ"

#include "chapters/part1_introduction/06_symbolic_executor.typ"

// Additional chapters will be included as we create them
// #include "chapters/part1_introduction/01_abstract_interpretation.typ"
// ... etc

// ============================================================================
// Part II: Deep Dive
// ============================================================================

// #include "chapters/part2_deep_dive/07_lattice_theory.typ"
// ... etc

// ============================================================================
// Part III: Appendices
// ============================================================================

// #include "chapters/part3_appendices/a_math_preliminaries.typ"
// ... etc

// ============================================================================
// Bibliography
// ============================================================================

// #bibliography("refs.yaml")
