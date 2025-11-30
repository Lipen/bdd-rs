#import "../../theme.typ": *

= Boolean Functions <ch-boolean-functions>

Before diving into BDDs, we need to establish the mathematical ground we're standing on.
This chapter reviews Boolean algebra and introduces the key concepts --- cofactors, Shannon expansion, and the representation problem --- that BDDs are designed to solve.

If you're comfortable with Boolean algebra, skim to @sec-shannon-expansion; that's where the BDD story really begins.

== Boolean Algebra Foundations

=== The Boolean Domain

The Boolean domain $BB = {0, 1}$ contains exactly two values: *false* (0) and *true* (1).
Everything in Boolean computation reduces to these two primitives.

#definition(title: "Boolean Function")[
  A *Boolean function* of $n$ variables is a mapping $f: BB^n -> BB$.
  Given $n$ Boolean variables $x_1, x_2, ..., x_n$, the function $f$ assigns a truth value to each of the $2^n$ possible input combinations.
]

How many Boolean functions of $n$ variables exist?
Each function is determined by its output on $2^n$ inputs, and each output can be 0 or 1.
Thus, there are exactly $2^(2^n)$ distinct Boolean functions of $n$ variables.

#table(
  columns: (auto, auto, auto),
  align: (center, center, center),
  table.header([*Variables*], [*Inputs*], [*Functions*]),
  [1], [$2$], [$4$],
  [2], [$4$], [$16$],
  [3], [$8$], [$256$],
  [4], [$16$], [$65,536$],
  [5], [$32$], [$4.3 times 10^9$],
  [10], [$1,024$], [$approx 10^308$],
)

The explosive growth explains why naive enumeration is impractical.
Even with 10 variables, there are more Boolean functions than atoms in the observable universe.

=== Basic Operations

The fundamental Boolean operations are:

*Negation (NOT)*: $not x$ flips the value.
$ not 0 = 1, quad not 1 = 0 $

*Conjunction (AND)*: $x and y$ is true when both operands are true.
$ x and y = 1 "iff" x = 1 "and" y = 1 $

*Disjunction (OR)*: $x or y$ is true when at least one operand is true.
$ x or y = 1 "iff" x = 1 "or" y = 1 $

*Exclusive OR (XOR)*: $x xor y$ is true when exactly one operand is true.
$ x xor y = 1 "iff" x != y $

*Implication*: $x -> y$ is false only when $x$ is true and $y$ is false.
$ x -> y = not x or y $

*Equivalence (XNOR)*: $x <-> y$ is true when both operands have the same value.
$ x <-> y = not(x xor y) $

=== Algebraic Laws

Boolean algebra satisfies many useful identities:

*Commutativity:*
$ x and y = y and x, quad x or y = y or x $

*Associativity:*
$ (x and y) and z = x and (y and z), quad (x or y) or z = x or (y or z) $

*Distributivity:*
$ x and (y or z) = (x and y) or (x and z) $
$ x or (y and z) = (x or y) and (x or z) $

*De Morgan's Laws:*
$ not(x and y) = not x or not y $
$ not(x or y) = not x and not y $

*Absorption:*
$ x and (x or y) = x, quad x or (x and y) = x $

*Complement:*
$ x and not x = 0, quad x or not x = 1 $

These laws enable algebraic manipulation of Boolean expressions, but they do not directly solve the representation problem.

== Representations of Boolean Functions

A Boolean function can be represented in many ways.
Each representation has trade-offs in space, canonicity, and operation efficiency.

=== Truth Tables

The most explicit representation lists the function's output for every input:

#example-box(title: "Truth Table for XOR")[
  #align(center)[
    #table(
      columns: (auto, auto, auto),
      align: (center, center, center),
      table.header([$x$], [$y$], [$x xor y$]),
      [0], [0], [0],
      [0], [1], [1],
      [1], [0], [1],
      [1], [1], [0],
    )
  ]
]

Truth tables are *canonical* --- each function has exactly one truth table.
Equivalence checking is straightforward: compare tables entry by entry.

However, truth tables require $2^n$ entries for $n$ variables.
This exponential size makes them impractical for functions with more than about 20 variables.

=== Boolean Formulas

A Boolean formula is a syntactic expression using variables and operations:
$ f = (x_1 and x_2) or (not x_1 and x_3) $

Formulas can be compact, but they are *non-canonical* --- many different formulas represent the same function.
For example, these all represent the same function:
$ x and y = y and x = not(not x or not y) = (x or 0) and (y or 0) $

Checking formula equivalence requires reasoning about all possible simplifications, which is co-NP-complete in general.

=== Normal Forms

Normal forms impose structure on Boolean formulas.

*Disjunctive Normal Form (DNF)*: An OR of ANDs (sum of products).
$ f = (x_1 and x_2) or (not x_1 and x_3) or (x_2 and x_3) $

*Conjunctive Normal Form (CNF)*: An AND of ORs (product of sums).
$ f = (x_1 or x_2) and (not x_1 or x_3) and (x_2 or not x_3) $

Normal forms are useful for specific algorithms (SAT solvers work on CNF), but they are still non-canonical.
The same function can have multiple DNF or CNF representations.

#insight-box[
  The representation dilemma:
  - *Truth tables* are canonical but exponentially large.
  - *Formulas* are compact but non-canonical.
  - *BDDs* achieve canonicity with size often polynomial in practice.
]

== Shannon Expansion <sec-shannon-expansion>

The key to BDDs is the *Shannon expansion*, which decomposes a function by "case splitting" on a variable.

=== Cofactors

#definition(title: "Cofactor")[
  The *cofactor* of $f$ with respect to variable $x_i$ set to value $b in {0, 1}$ is the function:
  $ f|_(x_i = b) = f(x_1, ..., x_(i-1), b, x_(i+1), ..., x_n) $

  We write $f|_(x_i = 0)$ as the *negative cofactor* (or *low cofactor*) and $f|_(x_i = 1)$ as the *positive cofactor* (or *high cofactor*).
]

The cofactor $f|_(x_i = b)$ is the function $f$ restricted to the case where $x_i$ has value $b$.
It is a function of $n - 1$ variables (since $x_i$ is fixed).

#example-box(title: "Computing Cofactors")[
  Let $f = (x and y) or z$.
  Then:
  - $f|_(x = 0) = (0 and y) or z = z$
  - $f|_(x = 1) = (1 and y) or z = y or z$
  - $f|_(y = 0) = (x and 0) or z = z$
  - $f|_(y = 1) = (x and 1) or z = x or z$
]

=== The Shannon Expansion Theorem

#theorem(title: "Shannon Expansion")[
  Every Boolean function $f(x_1, ..., x_n)$ can be decomposed with respect to any variable $x_i$:
  $ f = (not x_i and f|_(x_i = 0)) or (x_i and f|_(x_i = 1)) $

  Equivalently, using the if-then-else notation:
  $ f = "ite"(x_i, f|_(x_i = 1), f|_(x_i = 0)) $
]

#figure(
  cetz.canvas(length: 1cm, {
    import cetz.draw: *

    // Shannon expansion visualization
    content((6, 6.5), text(weight: "bold", size: 1em)[Shannon Expansion: $f = "ite"(x, f_1, f_0)$])

    // Root node f
    bdd-decision-node((6, 5), "f", name: "root")

    // Left branch: x=0
    rect(
      (2, 2.5),
      (4.5, 3.5),
      fill: colors.box-example.lighten(40%),
      stroke: 1pt + colors.success.lighten(20%),
      radius: 4pt,
    )
    content((3.25, 3), text(size: 0.9em)[$f|_(x=0)$])

    // Right branch: x=1
    rect(
      (7.5, 2.5),
      (10, 3.5),
      fill: colors.box-definition.lighten(40%),
      stroke: 1pt + colors.primary.lighten(20%),
      radius: 4pt,
    )
    content((8.75, 3), text(size: 0.9em)[$f|_(x=1)$])

    // Low edge (dashed)
    line((5.6, 4.6), (3.6, 3.5), stroke: (dash: "dashed", paint: colors.line, thickness: 1.5pt))
    content((3.8, 4.3), text(size: 0.7em, fill: colors.text-muted)[$x = 0$])

    // High edge (solid)
    line((6.4, 4.6), (8.4, 3.5), stroke: 1.5pt + colors.line)
    content((8.2, 4.3), text(size: 0.7em, fill: colors.text-muted)[$x = 1$])

    // Explanation below
    content((6, 1.5), align(center)[
      #set text(size: 0.8em)
      "If $x$ is true, evaluate $f|_(x=1)$; otherwise evaluate $f|_(x=0)$"
    ])
  }),
  caption: [Shannon expansion decomposes $f$ into two subfunctions based on a variable's value.],
)

#proof[
  Consider any assignment to the variables.
  If $x_i = 0$, then $not x_i = 1$ and the formula evaluates to $f|_(x_i = 0)$, which equals $f$ when $x_i = 0$.
  If $x_i = 1$, then $x_i = 1$ and the formula evaluates to $f|_(x_i = 1)$, which equals $f$ when $x_i = 1$.
  In both cases, the formula equals $f$.
]

The Shannon expansion has a natural interpretation: "if $x_i$ is true, then $f|_(x_i = 1)$, else $f|_(x_i = 0)$."

=== Recursive Structure

Applying Shannon expansion recursively yields a *decision tree*:

+ Start with $f$.
+ Pick a variable $x_1$ and decompose: two subfunctions $f|_(x_1 = 0)$ and $f|_(x_1 = 1)$.
+ For each subfunction, pick the next variable $x_2$ and decompose again.
+ Continue until reaching constant functions (0 or 1).

#figure(
  cetz.canvas(length: 1cm, {
    import cetz.draw: *

    // Decision tree for f = x AND y
    content((5, 7), text(weight: "bold", size: 1em)[Decision Tree for $f = x and y$])

    // Level 0: x
    bdd-decision-node((5, 5.5), "x", name: "x-root")

    // Level 1: y nodes
    bdd-decision-node((2.5, 3.5), "y", name: "y-left")
    bdd-decision-node((7.5, 3.5), "y", name: "y-right")

    // Level 2: terminals (as squares for decision tree leaves)
    bdd-terminal-node((1, 1.5), "0", name: "t00")
    bdd-terminal-node((4, 1.5), "0", name: "t01")
    bdd-terminal-node((6, 1.5), "0", name: "t10")
    bdd-terminal-node((9, 1.5), "1", name: "t11")

    // Edges from x
    bdd-low-edge("x-root", "y-left")
    bdd-high-edge("x-root", "y-right")

    // Edges from left y
    bdd-low-edge("y-left", "t00")
    bdd-high-edge("y-left", "t01")

    // Edges from right y
    bdd-low-edge("y-right", "t10")
    bdd-high-edge("y-right", "t11")

    // Path labels
    content((1, 0.7), text(size: 0.7em, fill: colors.text-muted)[00])
    content((4, 0.7), text(size: 0.7em, fill: colors.text-muted)[01])
    content((6, 0.7), text(size: 0.7em, fill: colors.text-muted)[10])
    content((9, 0.7), text(size: 0.7em, fill: colors.text-muted)[11])
  }),
  caption: [A decision tree for $x and y$ has $2^n = 4$ leaves --- one for each input combination.],
)

This produces a binary tree with $2^n$ leaves, one for each input combination.

The key insight leading to BDDs: *many subtrees are identical*.
If $f|_(x_1 = 0, x_2 = 1)$ equals $f|_(x_1 = 1, x_2 = 0)$, we can share a single subtree for both.
This sharing is what transforms exponential decision trees into potentially compact BDDs.

== Function Equivalence

Two Boolean functions $f$ and $g$ are *equivalent* (written $f equiv g$) if they produce the same output on every input:
$ f equiv g "iff" forall x in BB^n: f(x) = g(x) $

=== The Equivalence Checking Problem

Given two representations of Boolean functions, determine if they represent the same function.

*With truth tables*: Compare entry by entry.
Complexity: $O(2^n)$ time and space.

*With formulas*: In general, this is co-NP-complete.
Even syntactically different formulas can represent the same function.

*With BDDs (canonical)*: Compare pointers.
If two BDDs are constructed in the same manager with the same variable ordering, they represent the same function if and only if they are the same node.
Complexity: $O(1)$.

#insight-box[
  Canonicity transforms equivalence checking from a hard problem (co-NP-complete) into a trivial one ($O(1)$).
  This is the fundamental reason BDDs are powerful for verification.
]

=== Why Equivalence Matters

Equivalence checking appears throughout computer science:

- *Circuit verification*: Does an optimized circuit compute the same function as the specification?
- *Compiler optimization*: Is the optimized code equivalent to the original?
- *Theorem proving*: Are two logical formulas equivalent?
- *Test generation*: Does the implementation match the specification?

Any technique that makes equivalence checking efficient has broad applicability.

== The Representation Problem

We have seen three representations:

#table(
  columns: (auto, auto, auto, auto),
  align: (left, center, center, center),
  table.header([*Representation*], [*Canonical?*], [*Space*], [*Equivalence*]),
  [Truth table], [Yes], [$O(2^n)$], [$O(2^n)$],
  [Boolean formula], [No], [Variable], [co-NP-complete],
  [BDD (ROBDD)], [Yes], [Variable#super[†]], [$O(1)$],
)

#text(
  size: 0.9em,
)[#super[†] BDD size ranges from constant (for simple functions) to exponential (for multiplication), but is often polynomial for structured functions.]

No representation is universally best.
Truth tables guarantee polynomial-time operations but have exponential space.
Formulas can be compact but have hard equivalence checking.
BDDs occupy a middle ground: canonical representation with size that depends on the function's structure.

The BDD "gamble" is that many practical functions have compact BDDs.
Decades of experience in verification, synthesis, and optimization have shown this gamble often pays off --- but not always.

=== Preview: The BDD Solution

In the next chapter, we define BDDs formally.
The key ideas are:

+ Apply Shannon expansion with a *fixed variable ordering*.
+ *Share* identical subfunctions (hash consing).
+ *Eliminate* redundant tests (where both branches lead to the same place).

These constraints yield the *Reduced Ordered Binary Decision Diagram* (ROBDD), which is canonical for any fixed ordering.
The challenge then becomes managing the variable ordering to keep BDDs small --- a topic we address in @ch-variable-ordering.
