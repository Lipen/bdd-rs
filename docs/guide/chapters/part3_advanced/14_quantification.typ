#import "../../theme.typ": *

= Quantification and Abstraction <ch-quantification>

Quantification eliminates variables from Boolean functions.
It answers questions like "does *some* assignment to $x$ make $f$ true?" (existential) or "is $f$ true for *every* value of $x$?" (universal).

These operations are the bridge between BDDs and symbolic reasoning.
Model checking, constraint solving, and image computation all rely heavily on quantification to project away variables and reduce problem dimensionality.

== Existential Quantification

#definition(title: "Existential Quantification")[
  The existential quantification of $f$ with respect to variable $x$ is:
  $ exists x. f = f|_(x=0) or f|_(x=1) $
  Intuitively, $exists x. f$ is true if $f$ can be made true by *some* choice of $x$.
]

The result is a function that no longer depends on $x$.
We've "projected away" that variable.

#figure(
  cetz.canvas(length: 1cm, {
    import cetz.draw: *

    // Original BDD for f = x AND y
    content((3, 7), text(weight: "bold")[Original: $f = x and y$])

    bdd-decision-node((3, 5.5), "x", name: "x-orig")
    bdd-terminal-node((1.5, 4), "0", name: "zero-orig")
    bdd-decision-node((4.5, 4), "y", name: "y-orig")
    bdd-terminal-node((3.5, 2.5), "0", name: "zero-y")
    bdd-terminal-node((5.5, 2.5), "1", name: "one-y")

    bdd-low-edge("x-orig", "zero-orig")
    bdd-high-edge("x-orig", "y-orig")
    bdd-low-edge("y-orig", "zero-y")
    bdd-high-edge("y-orig", "one-y")

    // Arrow
    line((6, 4.5), (7.5, 4.5), stroke: 2pt + colors.primary, mark: (end: ">", fill: colors.primary))
    content((6.75, 5.1), text(size: 0.8em)[$exists x$])

    // Result: exists x. (x AND y) = y
    content((10, 7), text(weight: "bold")[Result: $exists x. f = y$])

    bdd-decision-node((10, 5.5), "y", name: "y-result")
    bdd-terminal-node((8.5, 4), "0", name: "zero-result")
    bdd-terminal-node((11.5, 4), "1", name: "one-result")

    bdd-low-edge("y-result", "zero-result")
    bdd-high-edge("y-result", "one-result")

    // Explanation
    content((6.75, 1.5), align(center)[
      #set text(size: 0.8em)
      $exists x. (x and y) = (0 and y) or (1 and y) = 0 or y = y$
    ])
  }),
  caption: [Existential quantification eliminates $x$ by OR-ing the two cofactors.],
)

=== Computing Existential Quantification

```rust
pub fn exists(&self, f: Ref, x: Var) -> Ref {
    let low = self.cofactor(f, x, false);   // f|_{x=0}
    let high = self.cofactor(f, x, true);   // f|_{x=1}
    self.or(low, high)                       // low ∨ high
}
```

== Universal Quantification

#definition(title: "Universal Quantification")[
  The universal quantification of $f$ with respect to variable $x$ is:
  $ forall x. f = f|_(x=0) and f|_(x=1) $
  $forall x. f$ is true only if $f$ is true for *all* choices of $x$.
]

Universal quantification is the dual of existential quantification.
It's more restrictive --- requiring $f$ to hold regardless of $x$.

#figure(
  cetz.canvas(length: 1cm, {
    import cetz.draw: *

    // Original BDD for f = x OR y
    content((3, 7), text(weight: "bold")[Original: $f = x or y$])

    bdd-decision-node((3, 5.5), "x", name: "x-univ")
    bdd-decision-node((1.5, 4), "y", name: "y-left")
    bdd-terminal-node((4.5, 4), "1", name: "one-high")
    bdd-terminal-node((0.5, 2.5), "0", name: "zero-ll")
    bdd-terminal-node((2.5, 2.5), "1", name: "one-lh")

    bdd-low-edge("x-univ", "y-left")
    bdd-high-edge("x-univ", "one-high")
    bdd-low-edge("y-left", "zero-ll")
    bdd-high-edge("y-left", "one-lh")

    // Arrow
    line((6, 4.5), (7.5, 4.5), stroke: 2pt + colors.primary, mark: (end: ">", fill: colors.primary))
    content((6.75, 5.1), text(size: 0.8em)[$forall x$])

    // Result: forall x. (x OR y) = y
    content((10, 7), text(weight: "bold")[Result: $forall x. f = y$])

    bdd-decision-node((10, 5.5), "y", name: "y-univ-result")
    bdd-terminal-node((8.5, 4), "0", name: "zero-univ-result")
    bdd-terminal-node((11.5, 4), "1", name: "one-univ-result")

    bdd-low-edge("y-univ-result", "zero-univ-result")
    bdd-high-edge("y-univ-result", "one-univ-result")

    // Explanation
    content((6.75, 1.5), align(center)[
      #set text(size: 0.8em)
      $forall x. (x or y) = (0 or y) and (1 or y) = y and 1 = y$
    ])
  }),
  caption: [Universal quantification eliminates $x$ by AND-ing the two cofactors.],
)

=== Computing Universal Quantification

```rust
pub fn forall(&self, f: Ref, x: Var) -> Ref {
    let low = self.cofactor(f, x, false);   // f|_{x=0}
    let high = self.cofactor(f, x, true);   // f|_{x=1}
    self.and(low, high)                      // low ∧ high
}
```

== Multiple Variable Quantification

Often we need to quantify over multiple variables at once.
The order of quantification matters for performance (though not correctness).

#insight-box[
  *Rule of thumb*: Quantify variables from the bottom of the BDD upward.
  This keeps intermediate results smaller because bottom variables affect fewer nodes.
]

=== Cube-Based Quantification

Variables to quantify are often represented as a *cube* --- a conjunction of variables:

```rust
// Quantify over {x, y, z} represented as cube = x ∧ y ∧ z
pub fn exists_cube(&self, f: Ref, cube: Ref) -> Ref {
    if self.is_one(cube) {
        return f;  // No more variables to quantify
    }
    let var = self.top_var(cube);
    let remaining = self.high(cube);  // Rest of cube
    let quantified = self.exists(f, var);
    self.exists_cube(quantified, remaining)
}
```

== Relational Product

The *relational product* (also called *and-exists*) combines conjunction with existential quantification:

$ "RelProd"(f, g, X) = exists X. (f and g) $

This operation is critical for symbolic model checking, where it computes reachable states.

#figure(
  cetz.canvas(length: 1cm, {
    import cetz.draw: *

    // Visualization of relational product
    content((6, 6.5), text(weight: "bold", size: 1em)[Relational Product: $exists X. (f and g)$])

    // Left: f
    rect((1, 3.5), (3.5, 5.5), fill: colors.box-definition.lighten(40%), stroke: 1pt + colors.primary, radius: 4pt)
    content((2.25, 5), text(size: 0.9em, weight: "semibold")[$f$])
    content((2.25, 4.3), text(size: 0.7em, fill: colors.text-muted)[current states])

    // Right: g
    rect(
      (4.5, 3.5),
      (7, 5.5),
      fill: colors.box-example.lighten(40%),
      stroke: 1pt + colors.success.lighten(20%),
      radius: 4pt,
    )
    content((5.75, 5), text(size: 0.9em, weight: "semibold")[$g$])
    content((5.75, 4.3), text(size: 0.7em, fill: colors.text-muted)[transition relation])

    // AND then EXISTS
    content((4, 2.7), text(size: 0.9em)[$and$])

    rect(
      (2.5, 1.2),
      (5.5, 2.2),
      fill: colors.box-warning.lighten(40%),
      stroke: 1pt + colors.warning.lighten(20%),
      radius: 4pt,
    )
    content((4, 1.7), text(size: 0.8em)[$f and g$])

    line((4, 2.2), (4, 2.5), stroke: 1pt + colors.line, mark: (start: ">"))

    content((6.5, 1.7), text(size: 0.9em)[$exists X$])
    line((5.5, 1.7), (7, 1.7), stroke: 1.5pt + colors.primary, mark: (end: ">", fill: colors.primary))

    // Result
    rect(
      (7.5, 1.2),
      (10.5, 2.2),
      fill: colors.box-insight.lighten(40%),
      stroke: 1pt + colors.info.lighten(20%),
      radius: 4pt,
    )
    content((9, 1.7), text(size: 0.8em)[next states])
  }),
  caption: [Relational product computes the image (next states) in one combined operation.],
)

=== Why Combine Operations?

Computing $exists X. (f and g)$ as two separate steps can create huge intermediate results.
The combined algorithm quantifies variables *during* the conjunction, keeping BDDs smaller.

#algorithm(title: "Relational Product (And-Exists)")[
  ```
  RelProduct(f, g, cube):
    if f == 0 or g == 0:
      return 0
    if is_one(cube):
      return And(f, g)
    if f == 1 and g == 1:
      return 1

    v = top_var_of(f, g, cube)

    if v in cube:
      // Quantify this variable
      f_low, f_high = cofactors(f, v)
      g_low, g_high = cofactors(g, v)
      cube' = remove(v, cube)

      r_low  = RelProduct(f_low, g_low, cube')
      r_high = RelProduct(f_high, g_high, cube')
      return Or(r_low, r_high)
    else:
      // Regular conjunction recursion
      // ... standard Apply-style recursion
  ```
]

== Complexity Considerations

Quantification can cause significant BDD growth.

#warning-box(title: "Quantification Blowup")[
  While cofactors can only shrink, their OR (or AND) can create BDDs much larger than the original.
  A single existential quantification can square the BDD size in the worst case.
]

=== Early Quantification

When computing $exists x. (f_1 and f_2 and ... and f_n)$:

- *Naive*: Compute all conjunctions, then quantify
- *Better*: Quantify $x$ as soon as it appears in only one remaining term

#insight-box[
  *Early quantification* keeps intermediate BDDs smaller by eliminating variables as soon as they're no longer needed.
  This is a key optimization in symbolic model checking.
]

== Applications

Quantification is used throughout symbolic reasoning:

#comparison-table(
  [*Application*],
  [*Operation*],
  [*Purpose*],
  [Reachability],
  [$exists X. (R and T)$],
  [Compute next states],
  [Verification],
  [$forall X. (P -> Q)$],
  [Check implication],
  [Projection],
  [$exists Y. f$],
  [Hide internal variables],
  [Consensus],
  [$forall x. f$],
  [Variables that don't matter],
)
