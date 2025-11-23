#import "../../theme.typ": *

= Advanced Galois Connections <ch-advanced-galois>

#reading-path(path: "advanced")

@ch-lattice-theory introduced Galois connections as the mathematical foundation relating concrete and abstract domains.
We now explore advanced topics: abstract transformers, best transformers, and completeness --- essential tools for designing precise and efficient analyses.
For domain combination techniques including products and reduction operators, see @ch-domain-combinations.

== From Concrete to Abstract Transformers

#definition(title: "Concrete Transformer")[
  Given a program statement $s$ and concrete domain $C$, the *concrete transformer* $llb s rrb_C: C -> C$ computes the effect of executing~$s$:

  $ llb s rrb_C (c) = {sigma' mid(|) exists sigma in c: sigma ->^s sigma'} $

  For a concrete state set $c$, this is the set of all states reachable by executing $s$ from any state in $c$.
]

#example-box[
  *Variable Modification:*

  For `x := x - 1`, the concrete transformer is:
  $ llb "x" := "x" - 1 rrb_C (c) = {sigma["x" |-> sigma("x") - 1] mid(|) sigma in c} $

  If $c = {("x"=64, "y"=100), ("x"=32, "y"=50)}$:
  $ llb "x" := "x" - 1 rrb_C (c) = {("x"=63, "y"=100), ("x"=31, "y"=50)} $
]

#definition(title: "Abstract Transformer")[
  Given Galois connection $(C, alpha, gamma, A)$ and statement $s$, an *abstract transformer* $llb s rrb^sharp: A -> A$ is *sound* if:

  $ alpha(llb s rrb_C (gamma(a))) lle llb s rrb^sharp (a) $

  for all $a in A$.
  Equivalently, by the adjunction property:

  $ llb s rrb_C (gamma(a)) subset.eq gamma(llb s rrb^sharp (a)) $
]

The soundness condition ensures the abstract transformer over-approximates the concrete behavior: any concrete state reachable by executing $s$ is represented in the abstract result.

#insight-box[
  Soundness is the cornerstone of abstract interpretation.
  We may lose precision (over-approximate), but we never claim a property holds when it doesn't (under-approximate).
  This makes the analysis safe for verification.
]

== Best Abstract Transformers

Not all sound abstract transformers are equally precise.
The *best* (most precise) transformer exists when the Galois connection has certain properties.

#definition(title: "Best Abstract Transformer")[
  The *best abstract transformer* for statement $s$ is:

  $ llb s rrb^sharp_"best" (a) = alpha(llb s rrb_C (gamma(a))) $

  This is the most precise sound transformer.
  It computes exactly the abstraction of the concrete result.
]

#theorem(title: "Best Transformer Characterization")[
  Let $(C, alpha, gamma, A)$ be a Galois connection.

  + $llb s rrb^sharp_"best"$ is sound (by definition).
  + $llb s rrb^sharp_"best"$ is the *most precise*: for any sound transformer $llb s rrb^sharp$,
    $ llb s rrb^sharp_"best" (a) lle llb s rrb^sharp (a) $
]

#proof[
  *Soundness*: Follows directly from the definition and Galois connection properties.

  *Most precise*: Let $llb s rrb^sharp$ be any sound transformer.
  By soundness:
  $ alpha(llb s rrb_C (gamma(a))) lle llb s rrb^sharp (a) $

  Since $llb s rrb^sharp_"best" (a) = alpha(llb s rrb_C (gamma(a)))$ by definition, we have:
  $ llb s rrb^sharp_"best" (a) lle llb s rrb^sharp (a) $
]

#example-box[
  *Variable Decrement in Sign Domain:*

  For `x := x - 1` with sign domain, consider $a = "Pos"$ (positive x).

  Concrete: $gamma("Pos") = ZZ^+ = {1, 2, ...}$.

  After `x := x - 1`: $llb "x" := "x" - 1 rrb_C (ZZ^+) = {0, 1, ...}$.

  Best transformer:
  - In basic sign domain ${bot, "Neg", "Zero", "Pos", top}$, we get $alpha({0, 1, ...}) = "Zero" ljoin "Pos"$ (since the set spans both).
    Without a "NonNeg" element, this join yields $top$.
  - In extended sign domain with "NonNeg", the best transformer would return $"NonNeg"$ (more precise).

  A sound but imprecise alternative: A conservative implementation might always return $top$ for any subtraction, sacrificing precision for simplicity.
]

== Completeness of Abstract Transformers

Best transformers are most precise, but computing them may be expensive or impossible.
*Completeness* characterizes when a practical transformer achieves the precision of the best transformer.

#definition(title: "Completeness")[
  An abstract transformer $llb s rrb^sharp$ is *complete* (or *exact*) if:

  $ llb s rrb^sharp (a) = alpha(llb s rrb_C (gamma(a))) $

  for all $a in A$.
  Equivalently, it coincides with the best transformer.
]

#theorem(title: "Completeness Condition")[
  Let $(C, alpha, gamma, A)$ be a Galois connection.
  Abstract transformer $llb s rrb^sharp$ is complete if and only if:

  $ llb s rrb^sharp compose alpha = alpha compose llb s rrb_C $

  That is, abstraction commutes with the concrete transformer.
]

#example-box[
  *Variable Adjustment:*

  Consider `x := x + 4` on intervals.

  - Input: $a = [60, 1500]$.
  - Concrete: $llb "x" := "x" + 4 rrb_C ({60, ..., 1500}) = {64, ..., 1504}$.
  - Best: $alpha({64, ..., 1504}) = [64, 1504]$.

  A practical interval addition: $[60, 1500] + 4 = [64, 1504]$ --- complete!

  However, for `x := x * x` (non-linear operation):
  - Input: $a = [-2, 2]$.
  - Concrete: $gamma([-2,2]) -> {0,1,4}$ after squaring.
  - Best: $alpha({0,1,4}) = [0,4]$.
  - Practical: $[-2,2] times [-2,2] = [-4, 4]$ --- incomplete (loses precision at $-4$).
]

#info-box(title: "Precision vs. Efficiency")[
  Complete transformers are ideal but not always feasible:

  - *Best transformer*: Expensive (requires $gamma$, concrete computation, then $alpha$).
  - *Complete practical transformer*: Efficient direct abstract computation, same precision.
  - *Incomplete transformer*: Fast but loses precision.

  Analysis design balances these tradeoffs.
]

== Combining Domains

Analyses often require tracking multiple properties simultaneously.
While individual domains like Signs or Intervals track specific properties, combining them enables richer analysis.

The theory of domain combinations appears in @ch-domain-combinations, which covers:
- *Direct products*: Independent parallel analysis
- *Reduced products*: Coordination through reduction operators
- *Trace partitioning*: Path-sensitive analysis foundations
- *Formal Galois connection treatment*: Soundness proofs and precision theorems

This separation allows us to focus here on how transformers interact with single domains, while @ch-domain-combinations provides the complete algebraic framework for combining them.

#chapter-summary[
  This chapter completed the theoretical foundation for designing precise abstract analyses by exploring the transformation pipeline from concrete to abstract semantics.

  *Abstract transformers* provide the mechanism for computing statement effects within abstract domains, replacing expensive concrete execution with tractable approximations.
  The notion of *best transformers* establishes an optimality criterion, defining the most precise sound approximation achievable through the abstraction function.

  *Completeness* characterizes the ideal scenario where practical transformers achieve best transformer precision without computing through the costly $alpha compose llb s rrb_C compose gamma$ composition.
  This theoretical benchmark guides the design of efficient transformers that preserve maximum precision.

  These principles form the foundation for designing abstract interpretations that balance soundness with efficiency.
  For techniques combining multiple domains including product constructions and reduction operators, see @ch-domain-combinations.
]
