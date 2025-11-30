#import "theme.typ": *

// ============================================================================
// Binary Decision Diagrams: Theory and Practice
// A Comprehensive Guide
// ============================================================================

#show: apply-guide-theme.with(
  title: "Binary Decision Diagrams",
  subtitle: "Theory, Implementation, and Applications",
  authors: ([The #link("https://github.com/Lipen/bdd-rs")[bdd-rs] contributors],),
  date: datetime.today().display("[month repr:long] [day], [year]"),
  header-title: "Binary Decision Diagrams",
)

// ============================================================================
// Title Page
// ============================================================================

#make-title()

#set page(numbering: "i")
#counter(page).update(1)

// ============================================================================
// Preface
// ============================================================================

#include "chapters/00_preface.typ"

// ============================================================================
// Table of Contents
// ============================================================================

#outline(depth: 2, indent: auto)

#pagebreak()

#set page(numbering: "1")
#counter(page).update(1)

// ============================================================================
// Part I: Foundations
// ============================================================================

#part[Foundations] <part-foundations>

// This part establishes the theoretical foundations of Binary Decision Diagrams.
// We begin with motivation and intuition, then develop the formal mathematical framework.
// By the end, you will understand what BDDs are, why they work, and when to use them.

#include "chapters/part1_foundations/01_introduction.typ"

#include "chapters/part1_foundations/02_boolean_functions.typ"

#include "chapters/part1_foundations/03_bdd_definition.typ"

#include "chapters/part1_foundations/04_canonical_form.typ"

#include "chapters/part1_foundations/05_operations.typ"

// ============================================================================
// Part II: Implementation
// ============================================================================

#part[Implementation] <part-implementation>

// This part covers practical implementation of a BDD library.
// We examine data structures, algorithms, and engineering trade-offs.
// The discussion is grounded in the `bdd-rs` library architecture.

#include "chapters/part2_implementation/06_architecture.typ"

#include "chapters/part2_implementation/07_node_representation.typ"

#include "chapters/part2_implementation/08_unique_table.typ"

#include "chapters/part2_implementation/09_apply_algorithm.typ"

#include "chapters/part2_implementation/10_caching.typ"

#include "chapters/part2_implementation/11_complement_edges.typ"

// ============================================================================
// Part III: Advanced Topics
// ============================================================================

#part[Advanced Topics] <part-advanced>

// This part explores advanced BDD techniques and extensions.
// We cover variable ordering, garbage collection, and variants like ZDDs and ADDs.

#include "chapters/part3_advanced/12_variable_ordering.typ"

#include "chapters/part3_advanced/13_garbage_collection.typ"

#include "chapters/part3_advanced/14_quantification.typ"

#include "chapters/part3_advanced/15_bdd_variants.typ"

// ============================================================================
// Part IV: Applications
// ============================================================================

#part[Applications] <part-applications>

This part demonstrates BDDs in practice across various domains.
From hardware verification to combinatorial problems, BDDs prove their versatility.

#include "chapters/part4_applications/16_model_checking.typ"

#include "chapters/part4_applications/17_combinatorial_problems.typ"

#include "chapters/part4_applications/18_symbolic_execution.typ"

#include "chapters/part4_applications/19_configuration.typ"

// ============================================================================
// Part V: Ecosystem and Comparison
// ============================================================================

#part[Ecosystem and Comparison] <part-ecosystem>

This part surveys the BDD landscape.
We compare approaches, examine existing libraries, and discuss design trade-offs.

#include "chapters/part5_ecosystem/20_library_comparison.typ"

#include "chapters/part5_ecosystem/21_design_tradeoffs.typ"

#include "chapters/part5_ecosystem/22_future_directions.typ"

// ============================================================================
// Appendices
// ============================================================================

#set heading(numbering: "A.1", supplement: "Appendix")
#counter(heading).update(0)

#include "chapters/appendices/a_api_reference.typ"

#include "chapters/appendices/b_complexity_analysis.typ"

#include "chapters/appendices/c_bibliography.typ"
