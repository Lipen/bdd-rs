#import "../../theme.typ": *

= Advanced Galois Connections <ch-advanced-galois>

#reading-path(path: "advanced")

@ch-lattice-theory introduced Galois connections as the mathematical foundation relating concrete and abstract domains.
This chapter explores advanced topics: abstract transformers, best transformers, completeness, and the reduced product construction --- essential tools for designing precise and efficient analyses.

== From Concrete to Abstract Transformers

#definition(title: "Concrete Transformer")[
  Given a program statement $s$ and concrete domain $C$, the *concrete transformer* $llb s rrb_C: C -> C$ computes the effect of executing $s$:

  $ llb s rrb_C (c) = {sigma' mid(|) exists sigma in c: sigma arrow.r^s sigma'} $

  For a concrete state set $c$, this is the set of all states reachable by executing $s$ from any state in $c$.
]

#example-box[
  *Assignment transformer:*

  For `x := e`, the concrete transformer is:
  $ llb x := e rrb_C (c) = {sigma[x |-> llb e rrb sigma] mid(|) sigma in c} $

  If $c = {(x=2, y=3), (x=5, y=1)}$ and the statement is `x := x + y`:
  $ llb x := x + y rrb_C (c) = {(x=5, y=3), (x=6, y=1)} $
]

#definition(title: "Abstract Transformer")[
  Given Galois connection $(C, alpha, gamma, A)$ and statement $s$, an *abstract transformer* $llb s rrb^sharp: A -> A$ is *sound* if:

  $ alpha(llb s rrb_C (gamma(a))) lle llb s rrb^sharp (a) $

  for all $a in A$.
  Equivalently, by the adjunction property:

  $ llb s rrb_C (gamma(a)) subset.eq gamma(llb s rrb^sharp (a)) $
]

The soundness condition ensures that the abstract transformer over-approximates the concrete behavior.
Any concrete state reachable by executing $s$ is represented in the abstract result.

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

  This is the most precise sound transformer: it computes exactly the abstraction of the concrete result.
]

#theorem(title: "Best Transformer Characterization")[
  Let $(C, alpha, gamma, A)$ be a Galois connection.

  + $llb s rrb^sharp_"best"$ is sound (by definition)
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
  *Sign domain assignment:*

  For `x := x + 1` with sign domain, consider $a = "Neg"$ (negative values).

  Concrete: $gamma("Neg") = ZZ^- = {..., -2, -1}$

  After `x := x + 1`: $llb x := x+1 rrb_C (ZZ^-) = {..., -1, 0}$

  Best transformer:
  - In basic sign domain ${bot, "Neg", "Zero", "Pos", top}$, we get $alpha({..., -1, 0}) = "Neg" ljoin "Zero"$ (since the set spans both).
    Without a "NonPos" element, this join yields $top$.
  - In extended sign domain with "NonPos", the best transformer would return $"NonPos"$ (more precise).

  A sound but imprecise alternative: A conservative implementation might always return $top$ for any addition, sacrificing precision for simplicity.
]

== Completeness of Abstract Transformers

While best transformers are most precise, computing them may be expensive or impossible.
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
  *Interval domain for multiplication:*

  Consider `x := x * 2` on intervals.

  - Input: $a = [1, 3]$
  - Concrete: $llb x := x times 2 rrb_C ({1,2,3}) = {2,4,6}$
  - Best: $alpha({2,4,6}) = [2, 6]$

  A practical interval multiplication: $[1,3] times 2 = [2, 6]$ --- complete!

  However, for `x := x * x`:
  - Input: $a = [-2, 2]$
  - Concrete: $gamma([-2,2]) arrow.r {0,1,4}$ after squaring
  - Best: $alpha({0,1,4}) = [0,4]$
  - Practical: $[-2,2] times [-2,2] = [-4, 4]$ --- incomplete (loses precision at $-4$)
]

#info-box(title: "Precision vs. Efficiency")[
  Complete transformers are ideal but not always feasible:

  - *Best transformer*: Expensive (requires $gamma$, concrete computation, then $alpha$)
  - *Complete practical transformer*: Efficient direct abstract computation, same precision
  - *Incomplete transformer*: Fast but loses precision

  Analysis design balances these tradeoffs.
]

== Reduced Product Construction

Product domains (@ch-combining-domains) combine multiple abstractions.
The *reduced product* refines this by exploiting relationships between component domains.

#definition(title: "Direct Product")[
  Given domains $(C, alpha_1, gamma_1, A_1)$ and $(C, alpha_2, gamma_2, A_2)$ over the same concrete domain, the *direct product* is:

  $ A_1 times A_2 = {(a_1, a_2) mid(|) a_1 in A_1, a_2 in A_2} $

  with abstraction:
  $ alpha(c) = (alpha_1 (c), alpha_2 (c)) $

  and concretization:
  $ gamma((a_1, a_2)) = gamma_1 (a_1) inter gamma_2 (a_2) $

  Operations are component-wise: $(a_1, a_2) ljoin (b_1, b_2) = (a_1 ljoin b_1, a_2 ljoin b_2)$.
]

The direct product is sound but may contain *unrealizable* elements: pairs $(a_1, a_2)$ where $gamma_1(a_1) inter gamma_2(a_2) = emptyset$.

#example-box[
  *Sign × Parity product:*

  - Sign: ${bot, "Neg", "Zero", "Pos", top}$
  - Parity: ${bot, "Even", "Odd", top}$

  Product element: $("Neg", "Even")$ represents negative even numbers --- realizable.

  Product element: $("Zero", "Odd")$ --- *unrealizable*! Zero is always even, never odd.
  The concrete meaning is $gamma("Zero") inter gamma("Odd") = emptyset$.
]

#definition(title: "Reduced Product")[
  A *reduction operator* $rho: A_1 times A_2 -> A_1 times A_2$ eliminates contradictions:

  + *Soundness*: $gamma(rho(a_1, a_2)) = gamma(a_1, a_2)$
  + *Idempotence*: $rho(rho(a_1, a_2)) = rho(a_1, a_2)$
  + *Monotonicity*: $(a_1, a_2) lle (b_1, b_2) => rho(a_1, a_2) lle rho(b_1, b_2)$

  The *reduced product* applies $rho$ after each operation to maintain a canonical form.
]

#example-box[
  *Sign × Parity reduction:*

  ```rust
  fn reduce(sign: Sign, parity: Parity) -> (Sign, Parity) {
      match (sign, parity) {
          (Sign::Zero, Parity::Odd) => (Sign::Bottom, Parity::Bottom),
          (Sign::Zero, _) => (Sign::Zero, Parity::Even),
          // Negative/Positive can be even or odd
          _ => (sign, parity),
      }
  }
  ```

  After reduction, $("Zero", "Odd")$ becomes $(bot, bot)$, making the inconsistency explicit.
]

#theorem(title: "Reduced Product Precision")[
  Let $(C, alpha_i, gamma_i, A_i)$ for $i=1,2$ be Galois connections, and $rho$ be a reduction operator.

  + The reduced product forms a Galois connection with:
    $ alpha(c) = rho(alpha_1(c), alpha_2(c)) $
    $ gamma((a_1, a_2)) = gamma_1(a_1) inter gamma_2(a_2) $

  + Reduced product is *at least as precise* as the direct product:
    $ rho(a_1, a_2) lle (a_1, a_2) $
]

#proof[
  *Galois connection*: Soundness of $rho$ ensures $gamma(rho(a_1, a_2)) = gamma(a_1, a_2)$, preserving the concretization.
  The abstraction $alpha$ followed by reduction maintains the adjunction property.

  *Precision*: Reduction operator is *decreasing*: $rho(a_1, a_2) lle (a_1, a_2)$ by soundness (same concretization) and idempotence (stabilizes at a smaller element).
  Since $lle$ is the precision ordering (smaller = more precise), the reduced product is more precise.
]

== Designing Reduction Operators

Effective reduction operators exploit *domain-specific relationships*.

#definition(title: "Reduction Strategies")[
  Common reduction patterns:

  + *Contradiction elimination*: Detect $gamma(a_1) inter gamma(a_2) = emptyset$, set both to $bot$
  + *Constraint propagation*: Tighten one domain based on constraints from another
  + *Interval refinement*: Use sign/parity to narrow interval bounds
  + *Relational tightening*: Use relationships between variables
]

#example-box[
  *Sign × Interval reduction:*

  ```rust
  fn reduce(sign: Sign, interval: Interval) -> (Sign, Interval) {
      match sign {
          Sign::Pos => {
              // Positive: interval lower bound must be > 0
              let refined = interval.intersect(Interval::new(1, PosInf));
              (sign, refined)
          }
          Sign::Neg => {
              // Negative: interval upper bound must be < 0
              let refined = interval.intersect(Interval::new(NegInf, -1));
              (sign, refined)
          }
          Sign::Zero => {
              // Zero: interval must be [0, 0]
              let refined = Interval::new(0, 0);
              (sign, refined)
          }
          _ => (sign, interval), // Top or Bottom: no refinement
      }
  }
  ```

  Input: $("Pos", [-5, 10])$

  After reduction: $("Pos", [1, 10])$ --- negative part eliminated!
]

#warning-box[
  *Reduction cost*: Reduction adds computational overhead.
  Apply reduction:
  - After joins (most beneficial)
  - Periodically during fixpoint iteration
  - Only when precision gain justifies cost

  Measure impact experimentally!
]

== Composing Multiple Domains

For more than two domains, reduced products generalize.

#definition(title: "Multi-Domain Reduced Product")[
  Given domains $A_1, ..., A_n$ with abstractions $alpha_i$ and concretizations $gamma_i$, the reduced product is:

  $ A = {(a_1, ..., a_n) mid(|) a_i in A_i, gamma_1(a_1) inter ... inter gamma_n(a_n) != emptyset} $

  with reduction operator:
  $ rho(a_1, ..., a_n) = "fix"(lambda (b_1, ..., b_n) . (rho_1(b_1, ..., b_n), ..., rho_n(b_1, ..., b_n))) $

  where each $rho_i$ refines domain $A_i$ based on constraints from other domains.
]

#example-box[
  *Sign × Parity × Interval:*

  For variable `x`:
  - Sign: $"Pos"$
  - Parity: $"Even"$
  - Interval: $[0, 10]$

  Reduction:
  + Sign refines interval: $[0, 10] inter [1, infinity] = [1, 10]$
  + Parity refines interval: $[1, 10] inter {"even"} = {2, 4, 6, 8, 10}$
  + Result: $("Pos", "Even", [2, 10])$ with even parity constraint

  Possible values: ${2, 4, 6, 8, 10}$ (much more precise than any single domain!)
]

== Abstract Transformers for Products

Transformers on product domains must maintain reduction.

#algorithm(title: "Product Domain Transfer Function")[
  *Input:* Statement $s$, product state $(a_1, ..., a_n)$

  *Output:* Transformed product state

  + *for* $i = 1$ *to* $n$ *do*
    + $a'_i <- llb s rrb^sharp_i (a_i)$ $quad slash.double$ Apply transformer in each domain
  + *end for*
  + $(a'_1, ..., a'_n) <- rho(a'_1, ..., a'_n)$ $quad slash.double$ Reduce result
  + *return* $(a'_1, ..., a'_n)$
]

#theorem(title: "Soundness of Product Transformers")[
  If each component transformer $llb s rrb^sharp_i$ is sound and $rho$ is a sound reduction, then the product transformer is sound.
]

#proof[
  Let $c = gamma(a_1, ..., a_n)$ be the concrete set represented by the product element.

  After executing $s$ concretely: $c' = llb s rrb_C (c)$.

  By soundness of each component:
  $ c' subset.eq gamma_i (llb s rrb^sharp_i (a_i)) quad "for all" i $

  Thus:
  $ c' subset.eq inter.big_(i=1)^n gamma_i (llb s rrb^sharp_i (a_i)) = gamma(a'_1, ..., a'_n) $

  Reduction preserves concretization: $gamma(rho(a'_1, ..., a'_n)) = gamma(a'_1, ..., a'_n)$.

  Therefore: $c' subset.eq gamma(rho(a'_1, ..., a'_n))$, establishing soundness.
]

== Precision vs. Cost Tradeoffs

#definition(title: "Analysis Metrics")[
  For comparing domain choices:

  + *Precision*: How many false alarms? Can we prove the property?
  + *Cost*: Time and memory for analysis
  + *Scalability*: Performance on large programs
  + *Expressiveness*: What properties can we verify?
]

#example-box[
  *Domain comparison for `x := x * x`:*

  #table(
    columns: 3,
    table.header([Domain], [Result for $x in [-2, 2]$], [Cost]),
    [Sign], [$top$], [Low],
    [Interval], [$[-4, 4]$], [Medium],
    [Sign × Interval (unreduced)], [$(top, [-4, 4])$], [Medium],
    [Sign × Interval (reduced)], [$("NonNeg", [0, 4])$], [High],
    [Octagon], [$x^2 in [0, 4]$], [Very High],
  )

  Reduced product eliminates negative results, but at computational cost.
]

#info-box(title: "Choosing Domains")[
  Domain selection heuristics:

  - *Start simple*: Sign or intervals for initial analysis
  - *Add domains incrementally*: Identify precision bottlenecks
  - *Use reduction selectively*: Only where needed
  - *Profile performance*: Measure time/space costs
  - *Consider problem structure*: Some domains excel on certain patterns
]

== Chapter Summary

This chapter explored advanced Galois connection theory:

- *Abstract transformers* compute statement effects in abstract domains
- *Best transformers* achieve maximum precision but may be expensive
- *Completeness* characterizes when practical transformers match best transformers
- *Reduced products* combine domains while eliminating inconsistencies
- *Reduction operators* exploit domain relationships for precision
- *Multi-domain products* enable rich, expressive analyses
- *Precision/cost tradeoffs* guide domain selection

These techniques form the foundation for designing powerful, practical abstract interpretations.

#pagebreak()
