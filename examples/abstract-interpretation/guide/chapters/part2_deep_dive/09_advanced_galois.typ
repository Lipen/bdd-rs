#import "../../theme.typ": *

= Advanced Galois Connections <ch-advanced-galois>

#reading-path(path: "advanced")

@ch-lattice-theory introduced Galois connections as the mathematical foundation relating concrete and abstract domains.
We now explore advanced topics: abstract transformers, best transformers, completeness, and the reduced product construction --- essential tools for designing precise and efficient analyses.

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

== Reduced Product Construction

Product domains (@ch-combining-domains) combine multiple abstractions.
The *reduced product* refines this by exploiting relationships between component domains.
For a conceptual implementation-oriented overview see @ch-combining-domains; this chapter gives the formal lattice treatment and proofs.

#definition(title: "Direct Product")[
  Given domains $(C, alpha_1, gamma_1, A_1)$ and $(C, alpha_2, gamma_2, A_2)$ over the same concrete domain, the *direct product* is:

  $ A_1 times A_2 = {(a_1, a_2) mid(|) a_1 in A_1, a_2 in A_2} $

  with abstraction:
  $ alpha(c) = (alpha_1 (c), alpha_2 (c)) $

  and concretization:
  $ gamma((a_1, a_2)) = gamma_1 (a_1) inter gamma_2 (a_2) $

  Operations are component-wise: $(a_1, a_2) ljoin (b_1, b_2) = (a_1 ljoin b_1, a_2 ljoin b_2)$.
]

The direct product is sound but may contain *unrealizable* elements: pairs $(a_1, a_2)$ where $gamma_1 (a_1) inter gamma_2 (a_2) = emptyset$.

#example-box[
  *Real-World Example: Type × Value*

  Consider analyzing variables with two domains:
  - *Type*: ${bot, "Int", "Float", "Bool", top}$.
  - *Value*: Interval domain $[0, 100]$.

  Product element: $("Int", [5, 5])$ represents integer 5 --- realizable.

  Product element: $("Bool", [5, 5])$ --- *unrealizable*!
  Booleans are 0 or 1. The value 5 contradicts the type Bool.
  The concrete meaning is $gamma("Bool") inter gamma("Value"[5]) = emptyset$.
]

#definition(title: "Reduced Product")[
  A *reduction operator* $rho: A_1 times A_2 -> A_1 times A_2$ eliminates contradictions:

  + *Soundness*: $gamma(rho(a_1, a_2)) = gamma(a_1, a_2)$.
  + *Idempotence*: $rho(rho(a_1, a_2)) = rho(a_1, a_2)$.
  + *Monotonicity*: $(a_1, a_2) lle (b_1, b_2) => rho(a_1, a_2) lle rho(b_1, b_2)$.

  The *reduced product* applies $rho$ after each operation to maintain a canonical form.
]

#example-box[
  *Type × Value reduction:*

  ```rust
  fn reduce(ty: Type, val: Interval) -> (Type, Interval) {
      match ty {
          Type::Bool => {
              // Bool implies value is 0 or 1
              // If value range is outside [0, 1], it's a contradiction
              let bool_range = Interval::new(0, 1);
              let refined = val.intersect(bool_range);
              if refined.is_bottom() {
                  (Type::Bottom, Interval::bottom())
              } else {
                  (ty, refined)
              }
          },
          Type::Int | Type::Float => (ty, val),
          _ => (ty, val),
      }
  }
  ```

  After reduction, $("Bool", [5, 5])$ becomes $(bot, bot)$, making the inconsistency explicit.
]

#figure(
  caption: [Reduced product eliminates unrealizable states],

  cetz.canvas({
    import cetz: draw

    // Domain 1: Type
    let d1-x = 0
    draw.content((d1-x, 4), [Type])
    draw.circle((d1-x, 3), radius: 0.3, name: "int", fill: colors.bg-code, stroke: colors.primary + 1pt)
    draw.content("int", [Int])
    draw.circle((d1-x, 1), radius: 0.3, name: "bool", fill: colors.bg-code, stroke: colors.primary + 1pt)
    draw.content("bool", [Bool])

    // Domain 2: Value
    let d2-x = 3
    draw.content((d2-x, 4), [Value])
    draw.rect((d2-x - 0.4, 2.6), (d2-x + 0.4, 3.4), name: "v5", fill: colors.bg-code, stroke: colors.accent + 1pt)
    draw.content("v5", [5])
    draw.rect((d2-x - 0.4, 0.6), (d2-x + 0.4, 1.4), name: "vNone", fill: colors.bg-code, stroke: colors.accent + 1pt)
    draw.content("vNone", [$bot$])

    // Product
    let p-x = 7
    draw.content((p-x, 4), [Product State])

    // Realizable
    draw.rect((p-x - 0.8, 2.6), (p-x + 0.8, 3.4), name: "valid", fill: colors.success.lighten(70%), stroke: colors.success + 1pt)
    draw.content("valid", [(Int, 5)])

    // Unrealizable
    draw.rect((p-x - 0.8, 0.6), (p-x + 0.8, 1.4), name: "invalid", fill: colors.error.lighten(70%), stroke: colors.error + 1pt)
    draw.content("invalid", [(Bool, 5)])

    // Reduction arrow
    draw.line("invalid.east", (p-x + 2, 1), stroke: (paint: colors.text-light, thickness: 1pt, dash: "dashed"), mark: (end: ">"))
    draw.content((p-x + 2.5, 1), text(fill: colors.error)[$bot$])
    draw.content((p-x + 2.5, 1.5), text(size: 8pt)[Reduce])

    // Connections
    draw.line("int.east", "valid.west", stroke: colors.text-light + 0.5pt)
    draw.line("v5.east", "valid.west", stroke: colors.text-light + 0.5pt)

    draw.line("bool.east", "invalid.west", stroke: colors.text-light + 0.5pt)
    draw.line("v5.east", "invalid.west", stroke: colors.text-light + 0.5pt)
  }),
)

#info-box(title: "Implementing the Reduction Loop")[
  In a multi-domain product, reduction can be iterative.
  Domain A refines B, which refines C, which might refine A again!

  ```rust
  fn reduce_loop(mut state: ProductState) -> ProductState {
      loop {
          let old_state = state.clone();

          // 1. Apply all reduction rules
          state = apply_rules(state);

          // 2. Check for fixpoint
          if state == old_state { break; }

          // 3. Check for bottom (contradiction)
          if state.is_bottom() { return ProductState::bottom(); }
      }
      state
  }
  ```
  For finite height domains, this loop always terminates.
]

#theorem(title: "Reduced Product Precision")[
  Let $(C, alpha_i, gamma_i, A_i)$ for $i=1,2$ be Galois connections, and $rho$ be a reduction operator.

  + The reduced product forms a Galois connection with:
    $ alpha(c) = rho(alpha_1 (c), alpha_2 (c)) $
    $ gamma((a_1, a_2)) = gamma_1 (a_1) inter gamma_2 (a_2) $

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

  + *Contradiction elimination*: Detect $gamma(a_1) inter gamma(a_2) = emptyset$, set both to $bot$.
  + *Constraint propagation*: Tighten one domain based on constraints from another.
  + *Interval refinement*: Use sign/parity to narrow interval bounds.
  + *Relational tightening*: Use relationships between variables.
]

#example-box[
  *Mode × Value reduction:*

  ```rust
  fn reduce(mode: Mode, val: Interval) -> (Mode, Interval) {
      match mode {
          Mode::Fast => {
              // Fast mode: value must be > 100
              let refined = val.intersect(Interval::new(101, 1000));
              (mode, refined)
          }
          Mode::Safe => {
              // Safe mode: value must be <= 100
              let refined = val.intersect(Interval::new(0, 100));
              (mode, refined)
          }
          _ => (mode, val),
      }
  }
  ```

  Input: $("Fast", [0, 200])$.

  After reduction: $("Fast", [101, 200])$ --- safe values eliminated!
]

#warning-box(title: "Reduction Cost")[
  *Reduction cost*: Reduction adds computational overhead.
  Apply reduction:
  - After joins (most beneficial).
  - Periodically during fixpoint iteration.
  - Only when precision gain justifies cost.

  Measure impact experimentally!
]

== Composing Multiple Domains

For more than two domains:

#definition(title: "Multi-Domain Reduced Product")[
  Given domains $A_1, ..., A_n$ with abstractions $alpha_i$ and concretizations $gamma_i$, the reduced product is:

  $ A = {(a_1, ..., a_n) mid(|) a_i in A_i, gamma_1 (a_1) inter ... inter gamma_n (a_n) != emptyset} $

  with reduction operator:
  $ rho(a_1, ..., a_n) = "fix"(lambda (b_1, ..., b_n) . (rho_1 (b_1, ..., b_n), ..., rho_n (b_1, ..., b_n))) $

  where each $rho_i$ refines domain $A_i$ based on constraints from other domains.
]

#example-box[
  *Type × Mode × Value:*

  For variable `v`:
  - Type: $"Int"$
  - Mode: $"Const"$
  - Value: $[0, 100]$

  Reduction:
  + Type refines Value: Int implies integer values.
  + Mode refines Value: Const implies singleton value (if we knew it).
  + Result: $("Int", "Const", [0, 100])$.

  If Mode was "Positive", we could refine Value to $[1, 100]$.
]

== Abstract Transformers for Products

Transformers on product domains must maintain reduction.

#algorithm(title: "Product Domain Transfer Function")[
  *Input:* Statement $s$, product state $(a_1, ..., a_n)$.

  *Output:* Transformed product state.

  + *for* $i = 1$ *to* $n$ *do*
    + $a'_i <- llb s rrb^sharp_i (a_i)$ $quad slash.double$ Apply transformer in each domain.
  + *end for*
  + $(a'_1, ..., a'_n) <- rho(a'_1, ..., a'_n)$ $quad slash.double$ Reduce result.
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
  + *Cost*: Time and memory for analysis.
  + *Scalability*: Performance on large programs.
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

  - *Start simple*: Sign or intervals for initial analysis.
  - *Add domains incrementally*: Identify precision bottlenecks.
  - *Use reduction selectively*: Only where needed.
  - *Profile performance*: Measure time/space costs.
  - *Consider problem structure*: Some domains excel on certain patterns.
]

#chapter-summary[
  This chapter completed the theoretical foundation for designing precise abstract analyses by exploring the transformation pipeline from concrete to abstract semantics.

  *Abstract transformers* provide the mechanism for computing statement effects within abstract domains, replacing expensive concrete execution with tractable approximations.
  The notion of *best transformers* establishes an optimality criterion, defining the most precise sound approximation achievable through the abstraction function.

  *Completeness* characterizes the ideal scenario where practical transformers achieve best transformer precision without computing through the costly $alpha compose llb s rrb_C compose gamma$ composition.
  This theoretical benchmark guides the design of efficient transformers that preserve maximum precision.

  The *reduced product* construction enables combining multiple domains while eliminating inconsistencies through *reduction operators* that exploit relationships between domains.
  This coordination mechanism recovers precision lost to independent analysis, enabling *multi-domain products* that track diverse properties simultaneously.

  Throughout these techniques runs the fundamental *precision-cost tradeoff* that guides practical domain selection and reduction strategy design.
  These principles form the foundation for designing powerful, practical abstract interpretations that balance theoretical soundness with computational feasibility.
]
