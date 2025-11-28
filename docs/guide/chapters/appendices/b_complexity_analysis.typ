#import "../../theme.typ": *

= Complexity Analysis <appendix-complexity>

// PLAN: Time and space complexity of BDD operations.
// Target length: 4-6 pages

== Operation Complexity Summary

#table(
  columns: 3,
  align: (left, center, center),
  table.header(
    [*Operation*], [*Time*], [*Space*]
  ),
  [Negation (complement edges)], [$O(1)$], [$O(1)$],
  [Negation (no complement)], [$O(n)$], [$O(n)$],
  [Apply (AND, OR, XOR, ...)], [$O(n dot m)$], [$O(n dot m)$],
  [ITE], [$O(n dot m dot k)$], [$O(n dot m dot k)$],
  [Restriction], [$O(n)$], [$O(n)$],
  [Composition], [$O(n^2 dot m)$], [$O(n^2 dot m)$],
  [Existential Quantification], [$O(n^2)$], [$O(n^2)$],
  [Equivalence Check], [$O(1)$], [$O(1)$],
  [Satisfiability Check], [$O(1)$], [$O(1)$],
  [Model Counting], [$O(n)$], [$O(n)$],
  [Level Swap (reordering)], [$O(w^2)$], [$O(1)$],
)

Where $n$, $m$, $k$ are BDD sizes and $w$ is the width at swapped levels.

== Space Complexity of Functions

Some Boolean functions have inherently exponential BDDs regardless of variable ordering:

#table(
  columns: 2,
  align: (left, center),
  table.header([*Function*], [*BDD Size*]),
  [Constant (0 or 1)], [$O(1)$],
  [Single variable], [$O(1)$],
  [Symmetric functions], [$O(n^2)$],
  [Threshold functions], [$O(n^2)$],
  [Integer multiplication], [$O(2^(n\/3))$ lower bound],
  [Hidden weighted bit], [$O(2^(n\/2))$],
)

== Notes on Complexity

- Complexities assume cached operations (computed table)
- Without caching, Apply becomes exponential
- Variable ordering can change polynomial to exponential
- Quantification complexity depends on eliminated variable's position
