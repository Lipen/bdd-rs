#import "../../theme.typ": *

= Advanced Galois Connections <ch-advanced-galois>

#reading-path(path: "advanced")

@ch-lattice-theory introduced Galois connections as the mathematical foundation relating concrete and abstract domains.
This chapter explores advanced topics: abstract transformers, best transformers, completeness, and the reduced product construction.
These are essential tools for designing precise and efficient analyses.

== From Concrete to Abstract Transformers

#definition(title: "Concrete Transformer")[
  Given a program statement $s$ and concrete domain $C$, the *concrete transformer* $llb s rrb_C: C -> C$ computes the effect of executing~$s$:

  $ llb s rrb_C (c) = {sigma' mid(|) exists sigma in c: sigma ->^s sigma'} $

  For a concrete state set $c$, this is the set of all states reachable by executing $s$ from any state in $c$.
]

#example-box[
  *Packet Header Modification:*

  For `ttl := ttl - 1`, the concrete transformer is:
  $ llb "ttl" := "ttl" - 1 rrb_C (c) = {sigma["ttl" |-> sigma("ttl") - 1] mid(|) sigma in c} $

  If $c = {("ttl"=64, "len"=100), ("ttl"=32, "len"=50)}$:
  $ llb "ttl" := "ttl" - 1 rrb_C (c) = {("ttl"=63, "len"=100), ("ttl"=31, "len"=50)} $
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
  *TTL Decrement in Sign Domain:*

  For `ttl := ttl - 1` with sign domain, consider $a = "Pos"$ (positive TTL).

  Concrete: $gamma("Pos") = ZZ^+ = {1, 2, ...}$.

  After `ttl := ttl - 1`: $llb "ttl" := "ttl" - 1 rrb_C (ZZ^+) = {0, 1, ...}$.

  Best transformer:
  - In basic sign domain ${bot, "Neg", "Zero", "Pos", top}$, we get $alpha({0, 1, ...}) = "Zero" ljoin "Pos"$ (since the set spans both).
    Without a "NonNeg" element, this join yields $top$.
  - In extended sign domain with "NonNeg", the best transformer would return $"NonNeg"$ (more precise).

  A sound but imprecise alternative: A conservative implementation might always return $top$ for any subtraction, sacrificing precision for simplicity.
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
  *Packet Length Adjustment:*

  Consider `len := len + 4` (adding 4-byte CRC) on intervals.

  - Input: $a = [60, 1500]$.
  - Concrete: $llb "len" := "len" + 4 rrb_C ({60, ..., 1500}) = {64, ..., 1504}$.
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

#definition(title: "Direct Product")[
  Given domains $(C, alpha_1, gamma_1, A_1)$ and $(C, alpha_2, gamma_2, A_2)$ over the same concrete domain, the *direct product* is:

  $ A_1 times A_2 = {(a_1, a_2) mid(|) a_1 in A_1, a_2 in A_2} $

  with abstraction:
  $ alpha(c) = (alpha_1 (c), alpha_2 (c)) $

  and concretization:
  $ gamma((a_1, a_2)) = gamma_1 (a_1) inter gamma_2 (a_2) $

  Operations are component-wise: $(a_1, a_2) ljoin (b_1, b_2) = (a_1 ljoin b_1, a_2 ljoin b_2)$.
]

The direct product is sound but may contain *unrealizable* elements.
These are pairs $(a_1, a_2)$ where $gamma_1(a_1) inter gamma_2(a_2) = emptyset$.

#example-box[
  *Real-World Example: Protocol × Port*

  Consider analyzing network traffic with two domains:
  - *Protocol*: ${bot, "TCP", "UDP", "ICMP", top}$.
  - *Port*: Interval domain $[0, 65535]$.

  Product element: $("TCP", [80, 80])$ represents TCP traffic on port 80 --- realizable.

  Product element: $("ICMP", [80, 80])$ --- *unrealizable*!
  ICMP packets do not have source/destination ports in the same way TCP/UDP do.
  The concrete meaning is $gamma("ICMP") inter gamma("Port"[80]) = emptyset$.
]

#definition(title: "Reduced Product")[
  A *reduction operator* $rho: A_1 times A_2 -> A_1 times A_2$ eliminates contradictions:

  + *Soundness*: $gamma(rho(a_1, a_2)) = gamma(a_1, a_2)$.
  + *Idempotence*: $rho(rho(a_1, a_2)) = rho(a_1, a_2)$.
  + *Monotonicity*: $(a_1, a_2) lle (b_1, b_2) => rho(a_1, a_2) lle rho(b_1, b_2)$.

  The *reduced product* applies $rho$ after each operation to maintain a canonical form.
]

#example-box[
  *Protocol × Port reduction:*

  ```rust
  fn reduce(proto: Protocol, port: Interval) -> (Protocol, Interval) {
      match proto {
          Protocol::ICMP => {
              // ICMP implies no ports (or specific types/codes)
              // If port range implies existence of ports, it's a contradiction
              if !port.is_bottom() {
                  (Protocol::Bottom, Interval::bottom())
              } else {
                  (proto, port)
              }
          },
          Protocol::TCP | Protocol::UDP => (proto, port),
          _ => (proto, port),
      }
  }
  ```

  After reduction, $("ICMP", [80, 80])$ becomes $(bot, bot)$, making the inconsistency explicit.
]

#figure(
  caption: [Reduced product eliminates unrealizable states],

  cetz.canvas({
    import cetz: draw

    // Domain 1: Protocol
    let d1-x = 0
    draw.content((d1-x, 4), [Protocol])
    draw.circle((d1-x, 3), radius: 0.3, name: "tcp", fill: colors.bg-code, stroke: colors.primary + 1pt)
    draw.content("tcp", [TCP])
    draw.circle((d1-x, 1), radius: 0.3, name: "icmp", fill: colors.bg-code, stroke: colors.primary + 1pt)
    draw.content("icmp", [ICMP])

    // Domain 2: Port
    let d2-x = 3
    draw.content((d2-x, 4), [Port])
    draw.rect((d2-x - 0.4, 2.6), (d2-x + 0.4, 3.4), name: "p80", fill: colors.bg-code, stroke: colors.accent + 1pt)
    draw.content("p80", [80])
    draw.rect((d2-x - 0.4, 0.6), (d2-x + 0.4, 1.4), name: "pNone", fill: colors.bg-code, stroke: colors.accent + 1pt)
    draw.content("pNone", [$bot$])

    // Product
    let p-x = 7
    draw.content((p-x, 4), [Product State])

    // Realizable
    draw.rect((p-x - 0.8, 2.6), (p-x + 0.8, 3.4), name: "valid", fill: colors.success.lighten(70%), stroke: colors.success + 1pt)
    draw.content("valid", [(TCP, 80)])

    // Unrealizable
    draw.rect((p-x - 0.8, 0.6), (p-x + 0.8, 1.4), name: "invalid", fill: colors.error.lighten(70%), stroke: colors.error + 1pt)
    draw.content("invalid", [(ICMP, 80)])

    // Reduction arrow
    draw.line("invalid.east", (p-x + 2, 1), stroke: (paint: colors.text-light, thickness: 1pt, dash: "dashed"), mark: (end: ">"))
    draw.content((p-x + 2.5, 1), text(fill: colors.error)[$bot$])
    draw.content((p-x + 2.5, 1.5), text(size: 8pt)[Reduce])

    // Connections
    draw.line("tcp.east", "valid.west", stroke: colors.text-light + 0.5pt)
    draw.line("p80.east", "valid.west", stroke: colors.text-light + 0.5pt)

    draw.line("icmp.east", "invalid.west", stroke: colors.text-light + 0.5pt)
    draw.line("p80.east", "invalid.west", stroke: colors.text-light + 0.5pt)
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
    $ alpha(c) = rho(alpha_1(c), alpha_2(c)) $
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
  *Jumbo Flag × Length reduction:*

  ```rust
  fn reduce(flag: Flag, len: Interval) -> (Flag, Interval) {
      match flag {
          Flag::Jumbo => {
              // Jumbo frame: length must be > 1500
              let refined = len.intersect(Interval::new(1501, 9000));
              (flag, refined)
          }
          Flag::Standard => {
              // Standard frame: length must be <= 1500
              let refined = len.intersect(Interval::new(0, 1500));
              (flag, refined)
          }
          _ => (flag, len),
      }
  }
  ```

  Input: $("Jumbo", [0, 2000])$.

  After reduction: $("Jumbo", [1501, 2000])$ --- standard frames eliminated!
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

For more than two domains, reduced products generalize.

#definition(title: "Multi-Domain Reduced Product")[
  Given domains $A_1, ..., A_n$ with abstractions $alpha_i$ and concretizations $gamma_i$, the reduced product is:

  $ A = {(a_1, ..., a_n) mid(|) a_i in A_i, gamma_1 (a_1) inter ... inter gamma_n (a_n) != emptyset} $

  with reduction operator:
  $ rho(a_1, ..., a_n) = "fix"(lambda (b_1, ..., b_n) . (rho_1(b_1, ..., b_n), ..., rho_n(b_1, ..., b_n))) $

  where each $rho_i$ refines domain $A_i$ based on constraints from other domains.
]

#example-box[
  *Protocol × Flag × Length:*

  For packet `p`:
  - Protocol: $"TCP"$
  - Flag: $"SYN"$
  - Length: $[0, 100]$

  Reduction:
  + Protocol refines Length: TCP header is min 20 bytes. $[0, 100] inter [20, infinity] = [20, 100]$.
  + Flag refines Length: SYN packet usually has no payload (len = header len).
  + Result: $("TCP", "SYN", [20, 60])$ (assuming max header size).

  Much more precise!
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

== Chapter Summary

This chapter explored advanced Galois connection theory:

- *Abstract transformers* compute statement effects in abstract domains.
- *Best transformers* achieve maximum precision but may be expensive.
- *Completeness* characterizes when practical transformers match best transformers.
- *Reduced products* combine domains while eliminating inconsistencies.
- *Reduction operators* exploit domain relationships for precision.
- *Multi-domain products* enable rich, expressive analyses.
- *Precision/cost tradeoffs* guide domain selection.

These techniques form the foundation for designing powerful, practical abstract interpretations.
