#import "../../theme.typ": *

= Precision Techniques and Design Patterns <ch-precision-techniques>

#reading-path(path: "advanced")

Improving precision without sacrificing termination is the central craft of abstract interpretation.
This chapter catalogs practical techniques and patterns for building precise, scalable analyzers, using our packet filter case study to illustrate key concepts.

== Reduced Product Patterns

#definition(title: "Reduced Product")[
  Given domains $A$ and $B$, the reduced product is $(A times B, rho)$ where $rho$ reduces $(a, b)$ to $(a', b')$ such that $gamma(a', b') = gamma(a, b)$ and $a' lle a$, $b' lle b$.
]

*Firewall Optimization Patterns*:

- *Mutual Refinement*: IP ranges (Intervals) refine BDD paths.
  If `ip` is in `[10.0.0.0, 10.255.255.255]`, the BDD branch for `is_private_ip` becomes true.
- *On-Demand Reduction*: Only reduce expensive domains (like Polyhedra) at loop heads or function summaries.
- *Domain-Aware Reductions*: String length limits trim the Automaton domain (e.g., `len(payload) < 1500`).

== Partitioning and Trace Sensitivity

- *Path Partitioning*: Splitting the abstract state based on control flow predicates (e.g., `if tcp.flags.syn`).
- *Trace Partitioning*: Differentiating states by bounded histories.
- *Disjunctive Completion*: Maintaining a set of abstract states $\{a_1, a_2, ...\}$ instead of merging them into $a_1 ljoin a_2$.

#example-box(title: "Partitioning by Protocol")[
  A firewall analysis might merge states too aggressively if it joins TCP and UDP flows.
  By partitioning on `eth.type` or `ip.proto`, we maintain separate invariants for TCP sequence numbers and UDP lengths.
  This avoids spurious warnings about "missing sequence numbers" in UDP packets.
]

== Widening/Narrowing Design

- *Thresholded Widening*: Delay widening for $k$ iterations to capture stable loops.
- *Extrapolation with History*: Widen by stable strides (e.g., if `i` goes $0, 4, 8$, widen to $4k$).
- *Narrowing Schedules*: Apply bounded descending iterations to recover precision after widening.

#figure(
  caption: [Widening with Thresholds for Packet Sizes],

  cetz.canvas({
    import cetz: draw

    // Axis
    draw.line((0, 0), (6, 0), mark: (end: ">"), name: "x")
    draw.content("x.end", [Value], anchor: "west")

    // Thresholds
    draw.line((2, -0.2), (2, 0.2), stroke: colors.text-light)
    draw.content((2, -0.4), [64])
    draw.line((4, -0.2), (4, 0.2), stroke: colors.text-light)
    draw.content((4, -0.4), [1500])

    // Iterations
    draw.rect((0, 0.5), (0.5, 1), fill: colors.primary, stroke: none)
    draw.content((0.25, 1.3), [It 1])

    draw.rect((0, 1.5), (1.0, 2), fill: colors.primary, stroke: none)
    draw.content((0.5, 2.3), [It 2])

    // Widen to Threshold
    draw.rect((0, 2.5), (4, 3), fill: colors.accent, stroke: none)
    draw.content((2, 3.3), [Widen to 1500])

    // Widen to Top
    draw.rect((0, 3.5), (5.5, 4), fill: colors.secondary, stroke: (dash: "dashed"))
    draw.content((2.75, 4.3), [Widen to $top$])
  }),
)

== Heuristics that Matter

- *Iteration Order*: Process inner loops first (recursive component analysis).
- *Variable Ordering*: Place protocol discriminators (e.g., `eth.type`) high in the BDD order.
- *Context Keys*: Use call-site sensitivity for `check_packet` functions, but not for generic helpers like `memcpy`.
- *Resource Budgets*: Cap the number of disjuncts in trace partitioning to prevent exponential blowup.

#insight-box[
  The best analyzers are architected around explicit precision/performance knobs with telemetry: track iteration counts, lattice heights, BDD sizes, and reduction effectiveness.
]

== Explainers and UX

- *Minimal Counterexamples*: Find the shortest path in the BDD or the smallest packet that triggers a rule violation.
- *Trace Slicing*: Report only the predicates relevant to a warning (e.g., "Packet dropped because `syn` flag set and port is 80").
- *Suggest Repairs*: "Did you mean to allow established connections?"

#chapter-summary[
  Precision arises from principled products, partitioning, refinement, and carefully designed widenings.
  Engineering choices (orders, budgets, telemetry) determine practical success.
  In our packet filter, partitioning by protocol and using thresholded widening for packet sizes ensures both precision and performance.
]
