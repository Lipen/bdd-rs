#import "../../theme.typ": *

= Complexity Analysis <appendix-complexity>

Time and space complexity of BDD operations.
These are worst-case bounds; actual performance is often much better due to sharing and caching.

== Operation Complexity

#figure(
  table(
    columns: 4,
    align: (left, center, center, left),
    table.header(
      [*Operation*], [*Time*], [*Space*], [*Notes*]
    ),
    [Negation], [$O(1)$], [$O(1)$], [Complement edge flip],
    [AND, OR, XOR], [$O(|f| dot |g|)$], [$O(|f| dot |g|)$], [Apply algorithm],
    [ITE], [$O(|f| dot |g| dot |h|)$], [$O(|f| dot |g| dot |h|)$], [Three operands],
    [Restrict], [$O(|f|)$], [$O(|f|)$], [Single variable],
    [Compose], [$O(|f|^2 dot |g|)$], [$O(|f|^2 dot |g|)$], [$f[x := g]$],
    [$exists x. f$], [$O(|f|^2)$], [$O(|f|^2)$], [Single variable],
    [$forall x. f$], [$O(|f|^2)$], [$O(|f|^2)$], [Same as $exists$],
    [Relational Product], [$O(|f| dot |g| dot 2^k)$], [$O(|f| dot |g| dot 2^k)$], [$k$ = vars quantified],
    [Equivalence Check], [$O(1)$], [$O(1)$], [Pointer comparison],
    [SAT Check], [$O(1)$], [$O(1)$], [Is BDD ≠ 0?],
    [SAT Count], [$O(|f|)$], [$O(|f|)$], [Dynamic programming],
    [SAT Witness], [$O(n)$], [$O(n)$], [$n$ = variables],
    [Level Swap], [$O(w^2)$], [$O(1)$], [$w$ = level width],
  ),
  caption: [Complexity of BDD operations. $|f|$ denotes the number of nodes in BDD $f$.],
)

== Function Size Bounds

Some functions have inherently small or large BDDs:

#figure(
  table(
    columns: 3,
    align: (left, center, left),
    table.header([*Function Class*], [*BDD Size*], [*Example*]),
    [Constants], [$O(1)$], [$0$, $1$],
    [Single variable], [$O(1)$], [$x_i$],
    [AND/OR of $n$ vars], [$O(n)$], [$x_1 and x_2 and ... and x_n$],
    [XOR of $n$ vars], [$O(n)$], [$x_1 xor x_2 xor ... xor x_n$],
    [Symmetric], [$O(n^2)$], [Majority, threshold],
    [Comparator], [$O(n)$], [$x < y$ (interleaved)],
    [Addition], [$O(n)$], [$x + y$ (interleaved)],
    [Multiplication], [$Omega(2^(n\/3))$], [$x times y$],
    [Hidden weighted bit], [$Omega(2^(n\/2))$], [Specific construction],
  ),
  caption: [BDD sizes for various function classes (with optimal variable ordering).],
)

#warning-box(title: "Ordering Dependence")[
  These bounds assume *optimal* variable ordering.
  With a bad ordering, even simple functions like addition can become exponential.
  For example, $x < y$ with all $x$-bits before all $y$-bits is exponential.
]

== Caching Effects

Without caching, Apply is exponential.
With caching:

#definition(title: "Memoization Guarantee")[
  Each unique subproblem $(f, g, "op")$ is computed *at most once*.
  Total work is bounded by the number of distinct subproblems, which is $O(|f| dot |g|)$.
]

#insight-box[
  The cache is what makes BDDs practical.
  A "small" cache (e.g., 10% of unique table size) is usually sufficient --- most operations have high temporal locality.
]

== Memory Analysis

Per-node memory in `bdd-rs`:

#figure(
  table(
    columns: 2,
    align: (left, right),
    [Component], [Size],
    [Variable index], [16 bits],
    [Low child (index + complement)], [32 bits],
    [High child (index only)], [31 bits],
    [Hash chain pointer], [32 bits],
    [*Total per node*], [~14 bytes (aligned to 16)],
  ),
  caption: [Memory layout of a BDD node in `bdd-rs`.],
)

For a BDD with $N$ nodes:
- *Unique table*: $N times 16$ bytes (nodes) $+ O(N)$ (hash buckets)
- *Operation cache*: Typically $0.1 N$ to $0.5 N$ entries $times$ 16 bytes/entry
- *Total*: Roughly $20 N$ to $30 N$ bytes
