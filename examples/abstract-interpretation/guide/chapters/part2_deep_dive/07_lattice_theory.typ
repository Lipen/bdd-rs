#import "../../theme.typ": *

= Lattice Theory Foundations <ch-lattice-theory>

#reading-path(path: "advanced")

This chapter provides the mathematical foundations for abstract interpretation.
We develop the theory of complete lattices, fixpoint theorems, and Galois connections.
These are the essential tools for understanding program analysis rigorously.

== Partial Orders and Lattices

#intuition-box[
  *Ordering as Information*

  In daily life, "order" usually means size (bigger vs. smaller).
  In abstract interpretation, order means *precision* or *information*.
  - $x <= y$ means "$x$ is more precise than $y$".
  - $x$ contains *more specific information* than $y$.
  - $y$ represents a *larger set of possibilities* (more uncertainty) than $x$.

  Think of it as:
  - $bot$ (Bottom): "Impossible" (Perfect information, but contradictory).
  - $x$: "`x` is 5" (Very precise).
  - $y$: "`x` is positive" (Less precise).
  - $top$ (Top): "`x` is any integer" (No information).
]

#definition(title: "Partial Order")[
  A *partial order* is a relation $<=$ on a set $L$ that is:

  - *Reflexive*: $forall x in L: x <= x$
  - *Transitive*: $forall x, y, z in L: x <= y and y <= z => x <= z$
  - *Antisymmetric*: $forall x, y in L: x <= y and y <= x => x = y$

  We write $(L, <=)$ for a set $L$ equipped with a partial order $<=$.
  This is called a *partially ordered set* or *poset*.
]

The partial order represents the *precision ordering* in abstract interpretation.
$x <= y$ means "$x$ is more precise than $y$".
Alternatively, "$x$ approximates fewer concrete behaviors than $y$".

#example-box[
  *Real-World Example: Integer Intervals*

  Consider the set of integer intervals.
  The ordering is subset inclusion (reversed for precision):
  $A <= B$ if the set of integers in $A$ is a subset of $B$.

  - $[5, 5]$ (Single value) is very precise.
  - $[0, 10]$ (Small range) is less precise.
  - $[-infinity, +infinity]$ (All integers) is the least precise ($top$).
  - $emptyset$ (No value) is the most precise ($bot$).

  $ emptyset <= [5, 5] <= [0, 10] <= [-infinity, +infinity] $
]

#figure(
  caption: [Lattice of Integer Intervals],

  cetz.canvas({
    import cetz: draw

    // Helper function for lattice nodes
    let draw-node(name, pos, label, style: "internal") = {
      if style == "bottom" {
        draw.rect(pos, (rel: (2, .8)), name: name, stroke: colors.primary + 1pt)
      } else if style == "top" {
        draw.rect(pos, (rel: (3, .8)), name: name, stroke: colors.primary + 1pt)
      } else {
        draw.rect(pos, (rel: (2.5, .8)), name: name, stroke: colors.primary + 1pt, fill: colors.bg-code)
      }
      draw.content(name, label)
    }

    let draw-edge(from, to) = {
      draw.line(from, to, stroke: colors.text-light + 0.8pt, mark: (end: ">"))
    }

    // Layout
    draw-node("top", (3, 6), [$[-infinity, +infinity]$ ($top$)], style: "top")

    draw-node("pos", (0, 4), [$[0, +infinity]$])
    draw-node("neg", (6, 4), [$[-infinity, 0]$])

    draw-node("sub1", (-1, 2), [$[0, 10]$])
    draw-node("sub2", (2, 2), [$[100, 200]$])
    draw-node("sub3", (6, 2), [$[-10, -1]$])

    draw-node("bot", (3, 0), [$emptyset$ ($bot$)], style: "bottom")

    // Edges
    draw-edge("bot", "sub1")
    draw-edge("bot", "sub2")
    draw-edge("bot", "sub3")

    draw-edge("sub1", "pos")
    draw-edge("sub2", "pos")
    draw-edge("sub3", "neg")

    draw-edge("pos", "top")
    draw-edge("neg", "top")

    // Annotations
    draw.content((9, 6), text(size: 9pt, fill: colors.text-light)[Least precise], anchor: "west", padding: 0.2)
    draw.content((9, 0), text(size: 9pt, fill: colors.text-light)[Most precise], anchor: "west", padding: 0.2)
    draw.line((9, 6), (9, 0), stroke: colors.text-light + 0.5pt, mark: (end: ">", fill: colors.text-light))
    draw.content((9.2, 3), rotate(270deg, text(size: 9pt, fill: colors.text-light)[Precision]))
  }),
)

#definition(title: "Upper and Lower Bounds")[
  Let $(L, <=)$ be a poset and $S subset.eq L$ be a subset.

  - An element $u in L$ is an *upper bound* of $S$ if $forall x in S: x <= u$.
  - An element $l in L$ is a *lower bound* of $S$ if $forall x in S: l <= x$.
  - The *least upper bound* (lub) or *supremum* of $S$, denoted $sup S$ or $ljoin.big S$, is the smallest element that is an upper bound of $S$ (if it exists).
  - The *greatest lower bound* (glb) or *infimum* of $S$, denoted $inf S$ or $lmeet.big S$, is the largest element that is a lower bound of $S$ (if it exists).
]

These operations correspond to *join* ($ljoin$) and *meet* ($lmeet$) in abstract interpretation.
The join computes the least precise abstraction containing both inputs (over-approximation).
The meet finds the most precise common refinement.

#definition(title: "Lattice")[
  A poset $(L, <=)$ is a *lattice* if every pair of elements $x, y in L$ has both:

  - A least upper bound: $x ljoin y$
  - A greatest lower bound: $x lmeet y$

  We write $(L, <=, ljoin, lmeet)$ or simply $L$ when the operations are clear.

  In Rust, we capture this structure with the `AbstractDomain` trait:

  ```rust
  pub trait AbstractDomain: Clone + PartialEq + Debug {
      // The lattice operations
      fn bottom() -> Self;
      fn top() -> Self;
      fn join(&self, other: &Self) -> Self;
      fn meet(&self, other: &Self) -> Self;

      // The partial order
      fn is_less_or_equal(&self, other: &Self) -> bool {
          // x <= y iff x join y == y
          self.join(other) == *other
      }
  }
  ```
]

#example-box[
  *Sign Lattice:*

  Consider the Sign lattice:

  #align(center, grid(
    columns: 5,
    stroke: colors.text-light + 0.5pt,
    inset: 5pt,
    fill: (x, y) => if x == 0 or y == 0 { colors.box-info },
    [*$ljoin$*], [*$bot$*], [*Pos*], [*Neg*], [*$top$*],
    [*$bot$*], [$bot$], [Pos], [Neg], [$top$],
    [*Pos*], [Pos], [Pos], [$top$], [$top$],
    [*Neg*], [Neg], [$top$], [Neg], [$top$],
    [*$top$*], [$top$], [$top$], [$top$], [$top$],
  ))

  Note that $"Pos" ljoin "Neg" = top$ because there's no single sign that is both Positive and Negative (except $top$ which covers both).
]

#definition(title: "Complete Lattice")[
  A lattice $(L, <=, ljoin, lmeet)$ is *complete* if every subset $S subset.eq L$ (including infinite subsets) has both:

  - A least upper bound: $ljoin.big_(x in S) x$
  - A greatest lower bound: $lmeet.big_(x in S) x$

  In particular, a complete lattice has:
  - A *least element* $bot = lmeet.big_(x in L) x$ (bottom).
  - A *greatest element* $top = ljoin.big_(x in L) x$ (top).
]

Complete lattices are the fundamental structure for abstract interpretation.
Program analysis must handle unbounded sets of states and infinite chains during iteration.

#theorem(title: "Properties of Complete Lattices")[
  Let $(L, <=, ljoin, lmeet, bot, top)$ be a complete lattice.

  + *Idempotence*: $x ljoin x = x$ and $x lmeet x = x$.
  + *Commutativity*: $x ljoin y = y ljoin x$ and $x lmeet y = y lmeet x$.
  + *Associativity*: $(x ljoin y) ljoin z = x ljoin (y ljoin z)$.
  + *Absorption*: $x ljoin (x lmeet y) = x$ and $x lmeet (x ljoin y) = x$.
  + *Identity*: $x ljoin bot = x$ and $x lmeet top = x$.
  + *Annihilation*: $x ljoin top = top$ and $x lmeet bot = bot$.
]

#proof[
  We prove a representative subset.

  *Idempotence of $ljoin$:*
  Since $x <= x$, we have $x$ is an upper bound of ${x, x}$.
  For any other upper bound $u$ with $x <= u$, we have $x <= u$.
  Thus $x$ is the least upper bound, so $x ljoin x = x$.

  *Absorption of $ljoin$:*
  Since $x lmeet y <= x$, we have $x$ is an upper bound of ${x, x lmeet y}$.
  For any upper bound $u$ with $x <= u$ and $x lmeet y <= u$, we have $x <= u$.
  Thus $x ljoin (x lmeet y) = x$.

  Other properties follow similarly from the definitions.
]

== Height and Chains

#definition(title: "Chain")[
  A subset $C subset.eq L$ is a *chain* if every two elements are comparable:
  $ forall x, y in C: x <= y or y <= x $

  The *length* of a finite chain $x_0 < x_1 < dots < x_n$ is $n$ (number of strict comparisons).
]

Chains are important because program analysis iterates along chains in the lattice.
We refine approximations until reaching a fixpoint.

#definition(title: "Height")[
  The *height* of a poset $(L, <=)$, denoted $"height"(L)$, is the length of the longest chain in $L$.
  If arbitrarily long chains exist, the height is infinite.
]

#example-box[
  *Heights of common lattices:*

  - Sign lattice: $"height" = 2$ (chain: $bot < "Pos" < top$).
  - Boolean lattice: $"height"({bot, top}) = 1$.
  - Powerset lattice: $"height"(cal(P)(S)) = |S|$ for finite set $S$.
  - Interval lattice over $ZZ$: $"height"("Interval") = infinity$ (unbounded chains).
]

#theorem(title: "Ascending Chain Condition")[
  A poset $(L, <=)$ satisfies the *ascending chain condition* (ACC) if every increasing chain
  $ x_0 <= x_1 <= x_2 <= dots $
  eventually stabilizes.
  There exists $N$ such that $x_N = x_(N+1) = x_(N+2) = dots$.
]

#info-box(title: "Why ACC Matters")[
  The ascending chain condition ensures that fixpoint iteration terminates.
  Without ACC, analysis might iterate forever, refining approximations without converging.

  When ACC doesn't hold (infinite-height lattices), we need *widening* operators to enforce convergence.
]

== Monotone Functions

#definition(title: "Monotone Function")[
  A function $f: L -> M$ between posets is *monotone* (or *order-preserving*) if:
  $ forall x, y in L: x <= y => f(x) <= f(y) $

  Intuitively, increasing precision in the input increases precision in the output.
]

All abstract operations in program analysis must be monotone to ensure sound approximation.
If an analysis loses precision when given more precise inputs, something is wrong.

#example-box[
  *Monotone functions on Intervals:*

  Abstract "absolute value" is monotone:
  - If $x_1 <= x_2$ (e.g., $[0, 5] <= [0, 10]$), then $"abs"(x_1) <= "abs"(x_2)$.
  - Example: $"abs"([0, 5]) = [0, 5] <= "abs"([0, 10]) = [0, 10]$.

  But consider a *non-monotone* function that returns $0$ for $bot$ and $[0, 5]$, but $100$ for $[0, 10]$.
  Then $[0, 5] <= [0, 10]$ but $f([0, 5]) = 0 gt.eq.not 100 = f([0, 10])$, violating monotonicity.
]

#theorem(title: "Composition Preserves Monotonicity")[
  If $f: L -> M$ and $g: M -> N$ are monotone, then $g compose f: L -> N$ is monotone.
]

#proof[
  Let $x <= y$ in $L$.
  Since $f$ is monotone, $f(x) <= f(y)$ in $M$.
  Since $g$ is monotone, $g(f(x)) <= g(f(y))$ in $N$.
  Thus $(g compose f)(x) <= (g compose f)(y)$.
]

== Fixpoints and Tarski's Theorem

#definition(title: "Fixpoint")[
  Let $f: L -> L$ be a function on a poset.
  An element $x in L$ is a *fixpoint* of $f$ if $f(x) = x$.

  The set of all fixpoints is denoted $"Fix"(f) = {x in L mid(|) f(x) = x}$.

  - A *least fixpoint* is $"lfp"(f) = lmeet.big_(x in "Fix"(f)) x$ (if it exists).
  - A *greatest fixpoint* is $"gfp"(f) = ljoin.big_(x in "Fix"(f)) x$ (if it exists).
]

Fixpoints represent stable abstract states in program analysis.
Applying the transfer function doesn't change the approximation.

#theorem(title: "Tarski's Fixpoint Theorem")[
  Let $(L, <=, ljoin, lmeet, bot, top)$ be a complete lattice and $f: L -> L$ be monotone.
  Then:

  + $f$ has a least fixpoint: $"lfp"(f) = lmeet.big_(f(x) <= x) x$.
  + $f$ has a greatest fixpoint: $"gfp"(f) = ljoin.big_(x <= f(x)) x$.
  + The set of all fixpoints $"Fix"(f)$ forms a complete lattice.
]

This is the foundation of fixpoint iteration in abstract interpretation!

#proof[
  We prove existence of the least fixpoint (greatest is dual).

  Let $P = {x in L mid(|) f(x) <= x}$ be the set of *post-fixpoints*.

  *Claim 1:* $P$ is non-empty.
  Since $L$ is a complete lattice, it has a top element $top$.
  We have $f(top) <= top$ (anything is below $top$), so $top in P$.

  *Claim 2:* Let $mu = lmeet.big_(x in P) x$ be the greatest lower bound of $P$.
  We show $f(mu) = mu$.

  First, show $f(mu) <= mu$:
  For all $x in P$, we have $mu <= x$.
  By monotonicity of $f$: $f(mu) <= f(x)$.
  Since $x in P$, we have $f(x) <= x$.
  Thus $f(mu) <= x$ for all $x in P$.
  Therefore $f(mu)$ is a lower bound of $P$, so $f(mu) <= lmeet.big_(x in P) x = mu$.

  Next, show $mu <= f(mu)$:
  From $f(mu) <= mu$, we have $mu in P$ (it's a post-fixpoint).
  Applying $f$: $f(mu) <= f(mu)$ (trivially).
  By monotonicity: $f(f(mu)) <= f(mu)$, so $f(mu) in P$.
  Since $mu = lmeet.big_(x in P) x$ is the greatest lower bound, $mu <= f(mu)$.

  By antisymmetry, $f(mu) = mu$, so $mu$ is a fixpoint.

  *Claim 3:* $mu$ is the least fixpoint.
  Any fixpoint $x$ satisfies $f(x) = x$, hence $f(x) <= x$, so $x in P$.
  Thus $mu = lmeet.big_(x in P) x <= x$ for all fixpoints $x$.
]

#info-box(title: "Constructive Fixpoint")[
  Tarski's theorem tells us the fixpoint exists, but doesn't give an algorithm to compute it.
  The *Kleene fixpoint theorem* (next section) provides a constructive iteration method.
]

== Kleene Fixpoint Theorem and Iteration

#theorem(title: "Kleene Fixpoint Theorem")[
  Let $(L, <=)$ be a complete lattice with finite height, and $f: L -> L$ be monotone.
  Then the least fixpoint can be computed by iteration:

  $ "lfp"(f) = ljoin.big_(i >= 0) f^i (bot) $

  where $f^0(bot) = bot$ and $f^(i+1)(bot) = f(f^i(bot))$.

  Moreover, the sequence stabilizes after finitely many steps.
  There exists $N$ such that $f^N(bot) = f^(N+1)(bot) = "lfp"(f)$.
]

This gives us the standard fixpoint iteration algorithm used in dataflow analysis!

#proof[
  Define the *Kleene sequence*: $x_0 = bot, x_(i+1) = f(x_i)$.

  *Step 1:* The sequence is increasing.
  By induction on $i$:
  - Base: $x_0 = bot <= f(bot) = x_1$ (bottom is below everything).
  - Step: Assume $x_i <= x_(i+1)$. By monotonicity: $f(x_i) <= f(x_(i+1))$, i.e., $x_(i+1) <= x_(i+2)$.

  *Step 2:* The sequence stabilizes.
  Since $L$ has finite height and the sequence is increasing, it must eventually stabilize at some $x_N = x_(N+1)$.

  *Step 3:* $x_N$ is a fixpoint.
  $f(x_N) = f(x_(N)) = x_(N+1) = x_N$.

  *Step 4:* $x_N$ is the least fixpoint.
  Let $mu$ be any fixpoint.
  By induction, $x_i <= mu$ for all $i$:
  - Base: $x_0 = bot <= mu$.
  - Step: Assume $x_i <= mu$. Then $x_(i+1) = f(x_i) <= f(mu) = mu$ (by monotonicity).

  Thus $x_N <= mu$, so $x_N$ is the least fixpoint.
]

#figure(
  caption: [Kleene iteration ascending from bottom to least fixpoint],

  cetz.canvas({
    import cetz: draw

    // Helper for iteration nodes
    let draw-iteration(name, pos, label) = {
      draw.circle(pos, radius: 0.25, name: name, fill: colors.bg-code, stroke: colors.primary + 0.8pt)
      draw.content(name, text(size: 8pt, label))
    }

    // Lattice elements vertically
    let y-bot = 0
    let y-x1 = 1.5
    let y-x2 = 3
    let y-lfp = 4.5
    let y-top = 6

    // Draw lattice structure (left side)
    draw.line((0, y-bot), (0, y-top), stroke: colors.text-light + 0.5pt)
    draw.content((-0.8, y-bot), $bot$)
    draw.content((-0.8, y-x1), $x_1$)
    draw.content((-0.8, y-x2), $x_2$)
    draw.content((-0.8, y-lfp), $"lfp"(f)$)
    draw.content((-0.8, y-top), $top$)

    // Iteration sequence (right side)
    let x-iter = 2

    draw-iteration("i0", (x-iter, y-bot), $f^0$)
    draw-iteration("i1", (x-iter, y-x1), $f^1$)
    draw-iteration("i2", (x-iter, y-x2), $f^2$)
    draw-iteration("i3", (x-iter, y-lfp), $f^3$)

    // Show convergence
    draw.line("i0", "i1", stroke: colors.primary + 0.8pt, mark: (end: ">"))
    draw.line("i1", "i2", stroke: colors.primary + 0.8pt, mark: (end: ">"))
    draw.line("i2", "i3", stroke: colors.primary + 0.8pt, mark: (end: ">"))

    // Fixpoint reached
    draw.content((x-iter + 1.5, y-lfp), text(size: 9pt, fill: colors.success)[$f^3 = f^4$])
    draw.content((x-iter + 1.5, y-lfp - 0.3), text(size: 9pt, fill: colors.success)[Fixpoint!])

    // Annotations
    draw.content((x-iter, y-bot - 0.6), text(size: 8pt, fill: colors.text-light)[Start: $x_0 = bot$])
    draw.content((x-iter, y-top + 0.6), text(size: 8pt, fill: colors.text-light)[Ascending chain])
  }),
)

#example-box[
  *Computing reachable program states:*

  Consider a program with states ${"Init", "Loop", "Exit"}$.
  Let $f(S)$ = $S union "next_state"(S)$.

  Starting from $S_0 = {"Init"}$:
  - $f^0({"Init"}) = {"Init"}$.
  - $f^1({"Init"}) = {"Init", "Loop"}$.
  - $f^2({"Init"}) = {"Init", "Loop", "Exit"}$.
  - $f^3({"Init"}) = {"Init", "Loop", "Exit"}$ (no new states).

  Fixpoint reached after 3 iterations!
]

== Galois Connections

Galois connections formalize the relationship between concrete and abstract domains.
They ensure that abstraction and concretization are consistent.

#definition(title: "Galois Connection")[
  Let $(C, <=_C)$ and $(A, <=_A)$ be posets.
  A pair of monotone functions
  $ alpha: C -> A quad "and" quad gamma: A -> C $
  forms a *Galois connection*, written $(C, alpha, gamma, A)$ or $C limits(-->)^alpha_gamma A$, if:

  $ forall c in C, forall a in A: alpha(c) <=_A a <==> c <=_C gamma(a) $

  - $alpha$ is the *abstraction function* (concrete $->$ abstract).
  - $gamma$ is the *concretization function* (abstract $->$ concrete).
]

#figure(
  caption: [Concrete vs. Abstract Execution: The Commuting Diagram],

  cetz.canvas({
    import cetz: draw

    // Nodes
    let c1 = (0, 4)
    let c2 = (4, 4)
    let a1 = (0, 0)
    let a2 = (4, 0)

    // Draw nodes
    draw.circle(c1, radius: 0.4, fill: colors.bg-code, stroke: colors.primary + 1pt, name: "c1")
    draw.content(c1, $C_1$)
    draw.circle(c2, radius: 0.4, fill: colors.bg-code, stroke: colors.primary + 1pt, name: "c2")
    draw.content(c2, $C_2$)

    draw.circle(a1, radius: 0.4, fill: colors.accent.lighten(80%), stroke: colors.accent + 1pt, name: "a1")
    draw.content(a1, $A_1$)
    draw.circle(a2, radius: 0.4, fill: colors.accent.lighten(80%), stroke: colors.accent + 1pt, name: "a2")
    draw.content(a2, $A_2$)

    // Edges
    // Concrete execution
    draw.line("c1", "c2", stroke: colors.primary + 1pt, mark: (end: ">"))
    draw.content((2, 4.3), text(fill: colors.primary)[$f$ (Concrete)])

    // Abstract execution
    draw.line("a1", "a2", stroke: colors.accent + 1pt, mark: (end: ">"))
    draw.content((2, -0.3), text(fill: colors.accent)[$f^sharp$ (Abstract)])

    // Abstraction (alpha)
    draw.line("c1", "a1", stroke: (paint: colors.text-light, dash: "dashed"), mark: (end: ">"))
    draw.content((-0.5, 2), $alpha$)

    draw.line("c2", "a2", stroke: (paint: colors.text-light, dash: "dashed"), mark: (end: ">"))
    draw.content((4.5, 2), $alpha$)

    // Soundness condition
    draw.content((2, 2), text(size: 9pt)[$alpha compose f <= f^sharp compose alpha$])
  }),
) <fig:commuting-diagram>

#figure(
  caption: [Galois connection between concrete and abstract domains],

  cetz.canvas({
    import cetz: draw

    // Concrete domain (left)
    draw.rect((0, 0), (2.5, 5), stroke: colors.primary + 1pt, name: "concrete")
    draw.content((1.25, 5.5), text(fill: colors.primary, weight: "bold")[Concrete $C$])

    // Abstract domain (right)
    draw.rect((4, 0.5), (6.5, 4.5), stroke: colors.accent + 1pt, name: "abstract")
    draw.content((5.25, 5.5), text(fill: colors.accent, weight: "bold")[Abstract $A$])

    // Elements
    draw.circle((1.25, 1), radius: 0.15, fill: colors.primary, name: "c")
    draw.content((1.25, 0.6), $c$)

    draw.circle((5.25, 3.5), radius: 0.15, fill: colors.accent, name: "a")
    draw.content((5.25, 3.9), $a$)

    // Arrows
    draw.line("c", "a", stroke: colors.primary + 1pt, mark: (end: ">", fill: colors.primary))
    draw.content((3.25, 2.5), text(fill: colors.primary)[$alpha$])

    draw.line("a", "c", stroke: colors.accent + 1pt, mark: (end: ">", fill: colors.accent))
    draw.content((3.25, 1.8), text(fill: colors.accent)[$gamma$])

    // Adjunction property
    draw.content((3.25, 0.3), text(size: 9pt, fill: colors.text-light)[$alpha(c) <=_A a <==> c <=_C gamma(a)$])
  }),
)

#theorem(title: "Properties of Galois Connections")[
  Let $(C, alpha, gamma, A)$ be a Galois connection.

  + $alpha$ and $gamma$ are monotone.
  + $alpha compose gamma$ is *reductive*: $alpha(gamma(a)) <=_A a$ for all $a in A$.
  + $gamma compose alpha$ is *extensive*: $c <=_C gamma(alpha(c))$ for all $c in C$.
  + $alpha(gamma(alpha(c))) = alpha(c)$ (abstraction idempotent).
  + $gamma(alpha(gamma(a))) = gamma(a)$ (concretization idempotent).
]

#proof[
  We prove properties 2 and 3 (others are exercises).

  *Property 2* ($alpha compose gamma$ reductive):
  By definition of Galois connection with $c = gamma(a)$ and $a = a$:
  $ alpha(gamma(a)) <=_A a <==> gamma(a) <=_C gamma(a) $
  The right side is trivially true, so $alpha(gamma(a)) <=_A a$.

  *Property 3* ($gamma compose alpha$ extensive):
  By definition with $c = c$ and $a = alpha(c)$:
  $ alpha(c) <=_A alpha(c) <==> c <=_C gamma(alpha(c)) $
  The left side is trivially true, so $c <=_C gamma(alpha(c))$.
]

#example-box[
  *Sign abstraction as Galois connection:*

  Concrete domain: $C = cal(P)(ZZ)$ (powersets of integers).
  Abstract domain: $A = {"Bot", "Neg", "Zero", "Pos", "Top"}$.

  Abstraction $alpha: cal(P)(ZZ) -> A$:
  $
    alpha(S) = cases(
      "Bot" & "if" S = emptyset,
      "Neg" & "if" S subset.eq ZZ^-,
      "Zero" & "if" S = {0},
      "Pos" & "if" S subset.eq ZZ^+,
      "Top" & "otherwise"
    )
  $

  Concretization $gamma: A -> cal(P)(ZZ)$:
  $
    gamma(a) = cases(
      emptyset & "if" a = "Bot",
      ZZ^- & "if" a = "Neg",
      {0} & "if" a = "Zero",
      ZZ^+ & "if" a = "Pos",
      ZZ & "if" a = "Top"
    )
  $

  Verify adjunction: $alpha(S) <=_A a <==> S subset.eq gamma(a)$.
]

== The Lattice of Boolean Functions

Since we use BDDs to represent sets of paths, it is crucial to understand that Boolean functions form a lattice.

Let $B_n$ be the set of all Boolean functions $f: {0,1}^n -> {0,1}$.
We define the ordering $f <= g$ as logical implication:
$ f <= g <==> forall x: f(x) => g(x) $

This forms a complete lattice $(B_n, <=, or, and, "false", "true")$.
- Join ($ljoin$) is logical OR ($or$).
- Meet ($lmeet$) is logical AND ($and$).
- Bottom ($bot$) is the constant function `false` (empty set of paths).
- Top ($top$) is the constant function `true` (all paths).

#insight-box[
  *BDDs implement this lattice.*
  The BDD operations `apply_or` and `apply_and` correspond exactly to the lattice join and meet operations.
  This is why we can use BDDs directly in our abstract interpretation framework.
]

== Chapter Summary

This chapter established the mathematical foundations:

- *Complete lattices* provide the structure for abstract domains.
- *Monotone functions* ensure sound approximation.
- *Tarski's theorem* guarantees fixpoint existence.
- *Kleene iteration* computes fixpoints constructively.
- *Galois connections* relate concrete and abstract semantics.

These tools enable rigorous program analysis with guaranteed termination and soundness.
