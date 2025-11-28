#import "../../theme.typ": *

= Model Checking with BDDs <ch-model-checking>

// PLAN: Symbolic model checking — BDDs' killer application.
// Target length: 12-15 pages

== The State Explosion Problem

// Content to cover:
// - Explicit state enumeration: 2^n states
// - Finite-state systems with many bits
// - Hardware and protocol verification needs
// - Symbolic representation as solution

== Encoding States and Transitions

// Content to cover:
// - State variables: Boolean encoding of state
// - Transition relation: R(s, s')
// - Initial states: I(s)
// - Property states: P(s)

#example-box(title: "Two-Bit Counter")[
  A counter with state bits $x_0, x_1$ has transition relation:
  $ R(x_0, x_1, x'_0, x'_1) = (x'_0 <-> not x_0) and (x'_1 <-> (x_0 xor x_1)) $
  This encodes: $x_0$ toggles every step, $x_1$ toggles when $x_0$ was 1.
]

== Reachability Analysis

// Content to cover:
// - Forward reachability: compute Image
// - Backward reachability: compute PreImage
// - Fixpoint computation
// - BDD represents entire reachable set

#algorithm(title: "Symbolic Reachability")[
  ```
  Reachable(Init, Trans):
    R = Init
    repeat:
      R_old = R
      R = R ∪ Image(R, Trans)
    until R == R_old
    return R
  ```
]

== CTL Model Checking

// Content to cover:
// - CTL operators: EX, EG, EU, etc.
// - Symbolic algorithms for each operator
// - Fixpoint characterizations
// - Full CTL model checking procedure

== Image and PreImage Computation

// Content to cover:
// - Image: ∃s. R(s, s') ∧ S(s)
// - PreImage: ∃s'. R(s, s') ∧ S(s')
// - Efficient implementation with relational product
// - Partitioned transition relations

== Example: Mutual Exclusion Protocol

// Content to cover:
// - Peterson's algorithm or similar
// - Encoding in BDDs
// - Verifying mutual exclusion
// - Finding counterexamples

== Limitations and Modern Approaches

// Content to cover:
// - BDD size limits for large systems
// - SAT-based bounded model checking
// - IC3/PDR algorithms
// - When to choose BDDs vs. SAT
