#import "../../theme.typ": *

= Quantification and Abstraction <ch-quantification>

// PLAN: Existential/universal quantification and related operations.
// Target length: 10-12 pages

== Existential Quantification

// Content to cover:
// - Definition: ∃x.f = f|_{x=0} ∨ f|_{x=1}
// - Eliminates variable from function
// - Creates "projection" onto remaining variables
// - Implementation via Apply

#definition(title: "Existential Quantification")[
  The existential quantification of $f$ with respect to variable $x$ is:
  $ exists x. f = f|_(x=0) or f|_(x=1) $
  Intuitively, $exists x. f$ is true if $f$ can be made true by some choice of $x$.
]

== Universal Quantification

// Content to cover:
// - Definition: ∀x.f = f|_{x=0} ∧ f|_{x=1}
// - Dual of existential
// - f is true for all values of x

== Multiple Variable Quantification

// Content to cover:
// - Quantifying over a set of variables
// - Order matters for efficiency
// - Quantify in order from bottom of BDD
// - Cube representation for variable sets

== Relational Product

// Content to cover:
// - Combined operation: (∃X. f ∧ g)
// - Critical for symbolic model checking
// - More efficient than separate ops
// - Image computation application

#algorithm(title: "Relational Product")[
  ```
  RelProduct(f, g, quantify_vars):
    // Compute conjunction and quantify simultaneously
    // More efficient than Apply(AND) followed by Exists

    if f == 0 or g == 0:
      return 0
    if f == 1 and g == 1:
      return 1

    // ... recursive case with simultaneous quantification
  ```
]

== Abstraction Operations

// Content to cover:
// - Smoothing (existential abstraction)
// - Consensus (universal abstraction)
// - Applications in verification
// - Variable hiding in composition

== Complexity Considerations

// Content to cover:
// - Quantification can cause blowup
// - Ordering affects quantification cost
// - Interleaving quantification with conjunction
// - Early quantification heuristics
