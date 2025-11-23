#import "../../theme.typ": *

= Algebraic Domain Combinations <ch-domain-combinations>

#reading-path(path: "advanced")

Previous chapters explored individual abstract domains like Intervals and Signs.
Real-world analysis often requires tracking multiple properties simultaneously or capturing relationships between them.
We formalize the algebra of *combining* abstract domains.

This chapter develops the theory of domain combinations, progressing from simple parallel execution to sophisticated coordination mechanisms.
We begin with *direct products*, which run multiple analyses independently by pairing their results.
Next, we introduce *reduced products*, which enable domains to exchange information and refine each other's precision.
We then examine *trace partitioning*, the theoretical foundation that enables path-sensitive analysis by distinguishing abstract states based on control flow history.
Finally, we explore *relational domains*, which transcend per-variable analysis by tracking correlations between multiple variables simultaneously.

== The Direct Product

Combine two domains $A$ and $B$ via the *direct product*: run two independent analyses and pair their results.

#definition(title: "Direct Product Domain")[
  Given domains $(C, alpha_1, gamma_1, A_1)$ and $(C, alpha_2, gamma_2, A_2)$ over the same concrete domain, their *direct product* $A_1 times A_2$ is defined as:

  *Elements:* Pairs $(a_1, a_2)$ where $a_1 in A_1$ and $a_2 in A_2$.

  *Ordering:* $(a_1, b_1) lle (a_2, b_2) <==> a_1 lle_(A_1) a_2 and b_1 lle_(A_2) b_2$.

  *Lattice operations (component-wise):*
  - Join: $(a_1, b_1) ljoin (a_2, b_2) = (a_1 ljoin_(A_1) a_2, b_1 ljoin_(A_2) b_2)$
  - Meet: $(a_1, b_1) lmeet (a_2, b_2) = (a_1 lmeet_(A_1) a_2, b_1 lmeet_(A_2) b_2)$

  *Galois connection:*
  - Abstraction: $alpha(c) = (alpha_1 (c), alpha_2 (c))$
  - Concretization: $gamma((a_1, a_2)) = gamma_1 (a_1) inter gamma_2 (a_2)$
]

The direct product answers questions neither domain could answer alone, but domains cannot *help* each other.

The direct product is sound but may contain *unrealizable* elements: pairs $(a_1, a_2)$ where $gamma_1 (a_1) inter gamma_2 (a_2) = emptyset$.
These represent inconsistent abstract states that correspond to no concrete execution.

#example-box(title: "Direct Product: Precision Loss and Unrealizability")[
  *Precision loss from independence:*

  Consider the product of *Signs* and *Parity* domains.
  Let $x$ be $"Pos"$ in Signs and $"Even"$ in Parity.
  State: $("Pos", "Even")$.

  Now, assume we execute `x = x / 2`.
  - Signs: $"Pos"$ / 2 $->$ $"Pos"$.
  - Parity: $"Even"$ / 2 $->$ $top$ (could be `Even` or `Odd`).
  - Result: $("Pos", top)$.

  We lost the information that $x$ was `Even`!
  If we knew $x=6$, then $x/2=3$ (`Odd`).
  The domains operated independently and failed to refine the result.

  *Unrealizable states:*

  Consider *Type* × *Value* product:
  - *Type*: ${bot, "Int", "Float", "Bool", top}$
  - *Value*: Interval domain $[0, 100]$

  Product element $("Int", [5, 5])$ represents integer 5 --- realizable.

  Product element $("Bool", [5, 5])$ --- *unrealizable*!
  Booleans are 0 or 1. The value 5 contradicts the type `Bool`.
  The concrete meaning is $gamma("Bool") inter gamma("Value"[5]) = emptyset$.
]

== The Reduced Product

The *reduced product* improves upon the direct product by allowing information exchange (reduction) between domains.

#definition(title: "Reduction Operator")[
  A *reduction operator* $rho: A_1 times A_2 -> A_1 times A_2$ transforms a pair $(a_1, a_2)$ into a more precise pair $(a'_1, a'_2)$ satisfying:

  + *Soundness*: $gamma(rho(a_1, a_2)) = gamma(a_1, a_2)$ (no concrete states lost)
  + *Improvement*: $rho(a_1, a_2) lle (a_1, a_2)$ (result is more precise)
  + *Idempotence*: $rho(rho(a_1, a_2)) = rho(a_1, a_2)$ (repeated application stabilizes)
  + *Monotonicity*: $(a_1, a_2) lle (b_1, b_2) => rho(a_1, a_2) lle rho(b_1, b_2)$ (preserves ordering)

  The *reduced product* applies $rho$ after each operation to maintain a canonical form.
]

Reduction propagates constraints discovered by one domain to the other.

#example-box(title: "Reduction Examples")[
  *Intervals* $times$ *Congruence*:

  State: $x in [10, 12]$ AND $x equiv 0 mod 5$.

  - Intervals alone: $10, 11, 12$.
  - Congruence alone: $..., 5, 10, 15, ...$.
  - Intersection: ${10}$.

  *Reduction*: The congruence domain tells the interval domain: "The only valid value in $[10, 12]$ is $10$."
  Refined Interval: $[10, 10]$.

  The interval domain tells the congruence domain: "The value is exactly 10."
  Refined Congruence: $x equiv 0 mod 10$ (if supported).

  *Type* $times$ *Value*:

  ```rust
  fn reduce(ty: Type, val: Interval) -> (Type, Interval) {
      match ty {
          Type::Bool => {
              // Bool implies value is 0 or 1
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
    draw.content("int", [$"Int"$])
    draw.circle((d1-x, 1), radius: 0.3, name: "bool", fill: colors.bg-code, stroke: colors.primary + 1pt)
    draw.content("bool", [$"Bool"$])

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
    draw.rect(
      (p-x - 0.8, 2.6),
      (p-x + 0.8, 3.4),
      name: "valid",
      fill: colors.success.lighten(70%),
      stroke: colors.success + 1pt,
    )
    draw.content("valid", [(Int, 5)])

    // Unrealizable
    draw.rect(
      (p-x - 0.8, 0.6),
      (p-x + 0.8, 1.4),
      name: "invalid",
      fill: colors.error.lighten(70%),
      stroke: colors.error + 1pt,
    )
    draw.content("invalid", [(Bool, 5)])

    // Reduction arrow
    draw.line(
      "invalid.east",
      (p-x + 2, 1),
      stroke: (paint: colors.text-light, thickness: 1pt, dash: "dashed"),
      mark: (end: ">"),
    )
    draw.content((p-x + 2.5, 1), text(fill: colors.error)[$bot$])
    draw.content((p-x + 2.5, 1.5), text(size: 8pt)[Reduce])

    // Connections
    draw.line("int.east", "valid.west", stroke: colors.text-light + 0.5pt)
    draw.line("v5.east", "valid.west", stroke: colors.text-light + 0.5pt)

    draw.line("bool.east", "invalid.west", stroke: colors.text-light + 0.5pt)
    draw.line("v5.east", "invalid.west", stroke: colors.text-light + 0.5pt)
  }),
)

#figure(
  caption: [Direct vs. Reduced Product: Intervals $times$ Congruence],
  cetz.canvas({
    import cetz.draw: *

    // --- Styles & Helpers ---
    let style-box = (fill: colors.bg-code, stroke: colors.primary + 1pt, radius: 0.2)
    let style-arrow = (mark: (end: ">"), stroke: colors.text-light + 0.8pt)

    let draw-state(pos, name, body, fill: colors.bg-code, width: 4, height: 1.2) = {
      let (x, y) = pos
      let w = width / 2
      let h = height / 2
      rect((x - w, y - h), (x + w, y + h), name: name, fill: fill, stroke: colors.primary + 1pt, radius: 0.2)
      content(pos, body)
    }

    let draw-arrow(from, to, label: none) = {
      line(from, to, ..style-arrow, name: "arrow")
      if label != none {
        content("arrow.mid", anchor: "west", padding: 0.1, label)
      }
    }

    // --- Layout Constants ---
    let x-left = -4
    let x-right = 4
    let y-top = 3
    let y-bot = 0

    // --- Direct Product ---
    content((x-left, y-top + 1.5), text(weight: "bold")[Direct Product])

    // Initial State
    draw-state((x-left, y-top), "d_init", [${[10, 12], 0 thick (mod 5)}$])

    // Result (Independent)
    draw-state(
      (x-left, y-bot),
      "d_res",
      text(0.8em)[Interval: $10, 11, 12$ \ Congruence: $..., 5, 10, 15, ...$],
      fill: colors.warning.lighten(80%),
      height: 1.5,
    )

    // Operation
    draw-arrow("d_init.south", "d_res.north", label: text(size: 0.8em)[Interpret])

    content((x-left, y-bot - 1.2), text(size: 0.8em, fill: colors.error)[No refinement!])

    // --- Reduced Product ---
    content((x-right, y-top + 1.5), text(weight: "bold")[Reduced Product])

    // Initial State
    draw-state((x-right, y-top), "r_init", [${[10, 12], 0 thick (mod 5)}$])

    // Result (Refined)
    draw-state(
      (x-right, y-bot),
      "r_res",
      [${[10, 10], 0 thick (mod 10)}$],
      fill: colors.success.lighten(80%),
      height: 1.5,
    )

    // Reduction Step
    draw-arrow("r_init.south", "r_res.north", label: text(size: 0.8em, fill: colors.accent)[Reduce $rho$])

    content((x-right, y-bot - 1.2), text(size: 0.8em, fill: colors.success)[Precision gained!])

    // Explanation arrow
    line(
      "r_res.west",
      "d_res.east",
      stroke: (paint: colors.text-light, dash: "dashed"),
      mark: (start: ">", end: ">", stroke: (dash: "solid")),
    )
    content((0, y-bot + 0.5), text(size: 0.8em)[$10 in [10, 12]$ is $0 thick (mod 5)$])
  }),
)

In practice, computing the *optimal* reduction (the Granger-Cousot reduction) can be expensive.
Most analyzers use *local iterations* or specific reduction heuristics (e.g., "`Signs` refines `Intervals`").

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

=== Designing Reduction Operators

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

  After reduction: $("Fast", [101, 200])$ --- `Safe` values eliminated!
]

#warning-box(title: "Reduction Cost")[
  Reduction adds computational overhead.
  Apply reduction:
  - After joins (most beneficial).
  - Periodically during fixpoint iteration.
  - Only when precision gain justifies cost.

  Measure impact experimentally!
]

=== Multi-Domain Products

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
  + Type refines Value: `Int` implies integer values.
  + Mode refines Value: `Const` implies singleton value (if we knew it).
  + Result: $("Int", "Const", [0, 100])$.

  If Mode was `Pos`, we could refine Value to $[1, 100]$.
]

== Trace Partitioning

*Trace partitioning* is a powerful technique to gain precision by distinguishing execution paths.
Instead of merging control flows immediately, we maintain separate abstract states for different history traces.

#definition(title: "Trace Partitioning Domain")[
  Given a set of trace tokens $T$ (representing control paths) and a domain $A$, the trace partitioning domain is the function space:
  $ A_T = T -> A $

  An element $f in A_T$ maps each trace $t in T$ to an abstract state $f(t)$.
  The concrete meaning is the union of states over all traces:
  $ gamma(f) = union.big_(t in T) gamma_A (f(t)) $
]

This is the theoretical foundation for *path-sensitive analysis*.
If $T$ represents the "current basic block" or "last branch taken", we get standard path sensitivity.
If $T$ represents "call stack", we get context sensitivity (interprocedural analysis).

#figure(
  caption: [Trace partitioning splits abstract states by path],

  cetz.canvas({
    import cetz.draw: *

    // --- Styles & Helpers ---
    let style-box = (fill: colors.bg-code, stroke: colors.primary + 1pt, radius: 0.2)
    let style-arrow = (mark: (end: ">", stroke: (dash: "solid")), stroke: colors.text-light + 0.8pt)

    let draw-state(pos, name, body, fill: colors.bg-code, stroke: colors.primary + 1pt, width: 2.5, height: 1) = {
      let (x, y) = pos
      let w = width / 2
      let h = height / 2
      rect((x - w, y - h), (x + w, y + h), name: name, fill: fill, stroke: stroke, radius: 0.2)
      content(pos, body)
    }

    // --- Layout Constants ---
    let y-split = 4
    let y-branch = 2
    let y-merge = 0
    let x-sep = 2

    // Control flow split
    circle((0, y-split), radius: 0.3, name: "split", fill: colors.bg-code, stroke: colors.primary + 1pt)
    content("split", [?])

    // Branches
    draw-state((-x-sep, y-branch), "s1", [$x in [0, 5]$], fill: colors.success.lighten(70%))
    draw-state((x-sep, y-branch), "s2", [$x in [6, 10]$], fill: colors.warning.lighten(70%))

    // Edges to branches
    line("split", "s1", ..style-arrow, name: "split-s1")
    content("split-s1", text(size: 8pt, fill: colors.success)[True], anchor: "south-east", padding: 0.2)

    line("split", "s2", ..style-arrow, name: "split-s2")
    content("split-s2", text(size: 8pt, fill: colors.warning)[False], anchor: "south-west", padding: 0.2)

    // Merge point (Partitioned)
    draw-state((0, y-merge), "merge", [${("T", [0, 5]), ("F", [6, 10])}$], width: 5)
    content((0, y-merge - 1), text(size: 9pt, fill: colors.text-light)[Kept separate!])

    // Edges to merge
    line("s1", "merge", ..style-arrow)
    line("s2", "merge", ..style-arrow)

    // Comparison with Merge
    let x-std = 6
    content((x-std, y-branch), text(weight: "bold")[Standard Merge:])
    draw-state((x-std, y-merge), "std", [$[0, 10]$], fill: colors.error.lighten(70%), stroke: colors.error + 1pt)
    content((x-std, y-merge - 1), text(size: 9pt, fill: colors.error)[Precision lost])

    // Arrow for standard merge comparison (conceptual)
    line((x-std, y-branch - 0.5), "std.north", ..style-arrow, stroke: (dash: "dashed"))
  }),
)

#info-box(title: "Partitioning vs. Disjunctive Completion")[
  Trace partitioning is a practical approximation of *disjunctive completion* (the power set domain $P(A)$).

  - $P(A)$ allows *arbitrary* disjunctions: $(x=1) or (x=5)$.
  - Trace partitioning allows disjunctions *aligned with control flow*: $("path"_1 and x=1) or ("path"_2 and x=5)$.

  This structure makes trace partitioning much more efficient than full disjunctive completion.
]

== Abstract Transformers for Products

Transformers on product domains must maintain reduction.

#algorithm(title: "Product Domain Transfer Function")[
  *Input:* Statement $s$, product state $(a_1, ..., a_n)$.

  *Output:* Transformed product state.

  + *for* $i = 1$ *to* $n$ *do*
    + $a'_i <- llb s rrb^sharp_i (a_i)$ $quad slash.double$ Apply transformer in each domain.
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

== Relational Domains

So far, we have discussed *non-relational* domains (like Intervals), which track properties of variables independently ($x in [a, b]$).
*Relational domains* track relationships *between* variables.

=== Common Relational Abstractions

Relational domains differ in the types of constraints they can express, creating fundamental tradeoffs between precision and performance.

*Octagon domains* track constraints of the form $plus.minus x plus.minus y lle c$, capturing simple relationships like "$x$ is at most 5 greater than $y$".
They achieve efficient $O(n^3)$ complexity, making them practical for array bounds checking where relationships like $i < n$ are common.

*Polyhedral domains* use general linear inequalities $sum a_i x_i lle c$, expressing arbitrary linear constraints between variables.
They offer maximum precision for linear relationships but suffer exponential complexity in the worst case.

*Equality domains* specialize in constraints of the form $x = y + c$, precisely tracking affine relationships.
They are particularly effective for alias analysis and variable substitution.

#example-box(title: "Real-World Example: Consistency Check")[
  Consider a security check for user roles:

  ```rust
  // User is admin?
  if user_id == admin_id {
      // Must have admin role
      if role != "Admin" {
          error();
      }
  }
  ```

  - *Intervals*: Tracks range of `user_id` and `role` independently.
    Cannot capture the correlation "if user is admin, role must be Admin".
  - *Relational*: Tracks `user_id == admin_id => role == "Admin"`.
    Can prove that the `error()` is unreachable for consistent states.
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

  Reduced product eliminates `Neg` results, but at computational cost.
]

#info-box(title: "Choosing Domains")[
  Domain selection heuristics:

  - *Start simple*: Sign or intervals for initial analysis.
  - *Add domains incrementally*: Identify precision bottlenecks.
  - *Use reduction selectively*: Only where needed.
  - *Profile performance*: Measure time/space costs.
  - *Consider problem structure*: Some domains excel on certain patterns.
]

== Widening in Product Domains

When combining domains, the widening operator must also be combined.
For a product $A times B$, the standard widening is component-wise:
$ (a_1, b_1) widen (a_2, b_2) = (a_1 widen_A a_2, b_1 widen_B b_2) $

However, this can be too aggressive.
*Delayed widening* or *widening with thresholds* is often necessary to prevent precision loss in one domain from destabilizing the other.

#chapter-summary[
  This chapter developed a hierarchy of domain combination techniques, each adding sophistication to multi-property analysis.

  The *direct product* provides the foundation by running multiple analyses independently, combining their results through simple pairing.
  While answering questions neither domain could handle alone, it cannot exploit synergies between domains.

  The *reduced product* overcomes this limitation by introducing reduction operators that enable bidirectional information exchange.
  Domains can now refine each other's abstract states, recovering precision lost to independent analysis.

  The *trace partitioning* construction provides the theoretical basis for path sensitivity.
  By distinguishing abstract states based on execution history captured through control flow predicates, it enables precise reasoning about conditional program behavior.

  Finally, *relational domains* transcend per-variable analysis by tracking correlations between multiple variables.
  They enable expressing constraints like $x < y$ or $x = 2y + 1$, which are essential for reasoning about array bounds, pointer arithmetic, and data structure consistency.

  In the next chapter, we will implement a powerful instance of these concepts: a *Reduced Product of BDDs (Trace Partitioning) and Abstract Domains*.
  This "Killer Feature" uses BDDs to efficiently manage the trace partition $T$, enabling scalable path-sensitive analysis.
]
