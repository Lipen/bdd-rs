#import "theme.typ": *

// ============================================================================
// Abstract Interpretation with BDDs: A Gentle Guide
// ============================================================================

#show: apply-guide-theme.with(
  title: "Abstract Interpretation with BDDs",
  subtitle: "A Gentle Guide to Program Verification",
  authors: ([The #link("https://github.com/Lipen/bdd-rs")[bdd-rs] contributors],),
  date: datetime.today().display("[month repr:long] [day], [year]"),
  header-title: "Abstract Interpretation with BDDs",
)

// ============================================================================
// Title Page
// ============================================================================

#set page(numbering: none)

#make-title()

// ============================================================================
// Preface
// ============================================================================

#set page(numbering: "i")
#counter(page).update(1)

#include "chapters/preface.typ"

// ============================================================================
// Table of Contents
// ============================================================================

#outline(depth: 2)

#set page(numbering: "1")
#counter(page).update(1)

// ============================================================================
// Part I: Gentle Introduction
// ============================================================================

#part[Gentle Introduction] <part-i>

This part starts from first principles, building intuition about program abstraction, control flow, and symbolic representations.
Through running examples like heater controllers and traffic lights, we motivate why BDD-based path-sensitive analysis matters.
This part is accessible to anyone with programming background.

#include "chapters/part1_introduction/00_prologue.typ"

#include "chapters/part1_introduction/01_abstraction.typ"

#include "chapters/part1_introduction/02_control_flow.typ"

#include "chapters/part1_introduction/03_bdds.typ"

#include "chapters/part1_introduction/04_bdd_programming.typ"

#include "chapters/part1_introduction/05_combining.typ"

#include "chapters/part1_introduction/06_symbolic_executor.typ"

// ============================================================================
// Part II: Deep Dive
// ============================================================================

#part[Deep Dive] <part-ii>

#reading-path(path: "advanced")

@part-ii provides rigorous mathematical foundations for abstract interpretation.
We develop complete lattice theory, fixpoint theorems, Galois connections, and advanced analysis techniques with formal proofs and implementation guidance.

#include "chapters/part2_deep_dive/07_lattice_theory.typ"

#include "chapters/part2_deep_dive/08_fixpoint_algorithms.typ"

#include "chapters/part2_deep_dive/09_advanced_galois.typ"

#include "chapters/part2_deep_dive/10_approximation_theory.typ"

#include "chapters/part2_deep_dive/11_domain_combinations.typ"

#include "chapters/part2_deep_dive/12_bdd_path_sensitivity.typ"

#include "chapters/part2_deep_dive/13_string_and_automata_domains.typ"

#include "chapters/part2_deep_dive/14_points_to_and_types.typ"

#include "chapters/part2_deep_dive/15_precision_techniques.typ"

// ============================================================================
// Part III: Applications & Future Directions
// ============================================================================

#part[Applications & Future Directions] <part-iii>

#reading-path(path: "essential") #h(0.7em) #reading-path(path: "implementation")

@part-iii bridges the gap between theory and the real world.
We explore how to apply BDD-guided analysis to security problems, handle complex interprocedural control flow, and look ahead to the integration of Artificial Intelligence with Formal Methods.

#include "chapters/part3_applications/16_security_analysis.typ"

#include "chapters/part3_applications/17_interprocedural_analysis.typ"

#include "chapters/part3_applications/18_performance.typ"

#include "chapters/part3_applications/19_ai_guided.typ"

#include "chapters/part3_applications/20_case_studies.typ"

// ============================================================================
// Part IV: Appendices
// ============================================================================

// #include "chapters/part4_appendices/a_math_preliminaries.typ"
// ... etc

// ============================================================================
// Bibliography
// ============================================================================

// #bibliography("refs.yaml")
