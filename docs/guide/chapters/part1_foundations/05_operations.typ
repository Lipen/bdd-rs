#import "../../theme.typ": *

= BDD Operations <ch-operations>

The power of BDDs comes from efficient algorithms for Boolean operations.
This chapter covers the core operations: combining BDDs (Apply), testing conditions (restriction), and abstracting variables (quantification).
The recurring theme is that BDD operations have polynomial complexity in the BDD size, not the exponential function size.

== Overview of Operations

BDD operations fall into several complexity classes:

#comparison-table(
  [*Operation*], [*Complexity*], [*Example*],
  [Equivalence], [$O(1)$], [$f equiv g$?],
  [SAT check], [$O(1)$], [$f equiv 0$?],
  [Negation], [$O(1)^*$], [$not f$],
  [Size query], [$O(1)$], [$|f|$?],
  [Counting], [$O(|f|)$], [$|{bold(x) : f(bold(x)) = 1}|$],
  [Cofactor], [$O(|f|)$], [$f|_(x=1)$],
  [Apply (AND, OR, ...)], [$O(|f| dot |g|)$], [$f and g$],
  [Quantification], [$O(|f|^2)$], [$exists x. f$],
  [Composition], [$O(|f|^2 dot |g|^2)$], [$f[x := g]$],
)

$*$ With complement edges; $O(|f|)$ without.

The key insight: operations are polynomial in BDD size, which is often much smaller than $2^n$.

== The Apply Algorithm

The `Apply` algorithm is the workhorse of BDD manipulation.
It combines two BDDs using any binary Boolean operation (AND, OR, XOR, etc.).

=== Intuition

To compute $f op g$ where $op$ is a binary operation:
+ Apply Shannon expansion to both functions on the same variable
+ Recursively compute the operation on cofactors
+ Combine results using `mk`

The trick is *memoization*: remember results to avoid redundant computation.

=== The Algorithm

#algorithm(title: "Apply")[
  ```
  function Apply(op, f, g):
      // Terminal cases
      if is_terminal(f) and is_terminal(g):
          return terminal(op(value(f), value(g)))

      // Short-circuit optimizations (for AND)
      if op = AND:
          if f = 0 or g = 0: return 0
          if f = 1: return g
          if g = 1: return f
          if f = g: return f

      // Cache lookup
      if (op, f, g) in ApplyCache:
          return ApplyCache[(op, f, g)]

      // Determine top variable (smallest in ordering)
      v = topvar(f, g)

      // Get cofactors (Shannon expansion)
      f_low  = cofactor(f, v, 0)
      f_high = cofactor(f, v, 1)
      g_low  = cofactor(g, v, 0)
      g_high = cofactor(g, v, 1)

      // Recursive calls
      low  = Apply(op, f_low, g_low)
      high = Apply(op, f_high, g_high)

      // Build result (mk handles reduction)
      result = mk(v, low, high)

      // Cache result
      ApplyCache[(op, f, g)] = result
      return result
  ```
]

The `topvar` function returns the smallest variable (according to ordering) that appears in either $f$ or $g$.
If a BDD does not depend on that variable, its cofactors are both equal to itself.

#info-box(title: "Cofactor Computation")[
  For a node $v$ with variable $x$:
  - If we're computing the cofactor for $x$: return low or high child
  - If we're computing the cofactor for a variable $y < x$ (above in ordering): the function doesn't depend on $y$, return the node itself
]

=== Terminal Rules

Different operations have different terminal rules:

#comparison-table(
  [*Operation*], [*Terminal Rule*], [*Short-circuits*],
  [AND ($and$)], [$0 and x = 0$, $1 and x = x$], [Either arg is $0$],
  [OR ($or$)], [$1 or x = 1$, $0 or x = x$], [Either arg is $1$],
  [XOR ($xor$)], [$0 xor x = x$, $1 xor x = not x$], [Both terminals],
  [IMPLIES ($->$)], [$0 -> x = 1$, $1 -> x = x$], [$f = 0$],
  [IFF ($<->$)], [$x <-> x = 1$, $0 <-> x = not x$], [$f = g$],
)

=== Example: Computing $f and g$

Let $f = x_1$ and $g = x_1 or x_2$ with ordering $x_1 < x_2$.

+ `Apply(AND, f, g)`:
  - Neither is terminal, so expand on $x_1$
  - $f_"low" = 0$, $f_"high" = 1$
  - $g_"low" = x_2$, $g_"high" = 1$

+ Recursive calls:
  - `Apply(AND, 0, x_2)` $= 0$ (short-circuit)
  - `Apply(AND, 1, 1)` $= 1$ (terminals)

+ Build result:
  - `mk(x_1, 0, 1)` $= x_1$

Result: $x_1 and (x_1 or x_2) = x_1$ ✓

== Complexity Analysis

#theorem(title: "Apply Complexity")[
  For BDDs $f$ and $g$, `Apply(op, f, g)` runs in $O(|f| times |g|)$ time.
]

#proof[
  The cache ensures each pair of nodes $(n_f, n_g)$ is processed at most once.
  There are at most $|f| times |g|$ such pairs.
  Each non-cached call does $O(1)$ work (excluding recursive calls).
  Therefore, total time is $O(|f| times |g|)$.
]

#theorem(title: "Result Size")[
  The result of `Apply(op, f, g)` has at most $O(|f| times |g|)$ nodes.
]

This bound is tight in the worst case but rarely achieved in practice.
Many operations produce results much smaller than the theoretical maximum.

=== Cache Management

The *apply cache* (or *computed table*) is crucial for performance.
Without caching, Apply would have exponential complexity.

Implementation considerations:
- *Cache key*: $(op, f, g)$ triple, often hashed
- *Cache size*: Bounded; old entries may be evicted
- *Symmetry*: For commutative operations, normalize $(f, g)$ to avoid duplicate entries
- *Clearing*: Cache must be invalidated when garbage collecting nodes

== If-Then-Else (ITE)

The If-Then-Else operation is a ternary operation that subsumes all binary operations.

#definition(title: "ITE Operation")[
  $"ite"(f, g, h) = (f and g) or (not f and h)$

  Semantically: "if $f$ then $g$ else $h$"
]

=== ITE is Universal

Every binary Boolean operation can be expressed as ITE:

#comparison-table(
  [*Operation*], [*ITE Expression*],
  [$f and g$], [$"ite"(f, g, 0)$],
  [$f or g$], [$"ite"(f, 1, g)$],
  [$not f$], [$"ite"(f, 0, 1)$],
  [$f xor g$], [$"ite"(f, not g, g)$],
  [$f -> g$], [$"ite"(f, g, 1)$],
  [$f <-> g$], [$"ite"(f, g, not g)$],
)

Some BDD libraries implement only ITE and derive other operations from it.
Others implement Apply directly for common operations (more efficient).

=== ITE Algorithm

#algorithm(title: "ITE")[
  ```
  function ITE(f, g, h):
      // Terminal cases
      if f = 1: return g
      if f = 0: return h
      if g = 1 and h = 0: return f
      if g = 0 and h = 1: return NOT(f)
      if g = h: return g

      // Cache lookup
      if (f, g, h) in ITECache:
          return ITECache[(f, g, h)]

      // Determine top variable
      v = topvar(f, g, h)

      // Recursive calls
      low  = ITE(cofactor(f,v,0), cofactor(g,v,0), cofactor(h,v,0))
      high = ITE(cofactor(f,v,1), cofactor(g,v,1), cofactor(h,v,1))

      // Build result
      result = mk(v, low, high)
      ITECache[(f, g, h)] = result
      return result
  ```
]

ITE complexity is $O(|f| times |g| times |h|)$ in the worst case.

== Negation

Negation (complement) is conceptually simple: flip every $0$ to $1$ and vice versa.

=== Without Complement Edges

#algorithm(title: "Negation (Recursive)")[
  ```
  function NOT(f):
      if f = 0: return 1
      if f = 1: return 0
      if f in NotCache: return NotCache[f]

      result = mk(var(f), NOT(low(f)), NOT(high(f)))
      NotCache[f] = result
      return result
  ```
]

This takes $O(|f|)$ time --- we visit each node once and create a mirror node.

=== With Complement Edges

With complement edges (@ch-complement-edges), negation is $O(1)$: just flip a bit in the reference.

#insight-box[
  Complement edges are an optimization where the "negated" bit is stored in the pointer, not the node.
  This makes negation free but complicates other operations slightly.
  Most modern BDD packages use complement edges.
]

== Restriction (Cofactor)

*Restriction* substitutes a constant for a variable: $f|_(x=b)$.

#algorithm(title: "Restrict")[
  ```
  function Restrict(f, x, b):
      if is_terminal(f): return f
      if var(f) > x: return f          // x not in f's cone
      if var(f) = x:
          return (b = 0) ? low(f) : high(f)

      // var(f) < x: recurse
      if f in RestrictCache: return RestrictCache[f]

      result = mk(var(f),
                  Restrict(low(f), x, b),
                  Restrict(high(f), x, b))
      RestrictCache[f] = result
      return result
  ```
]

Restriction runs in $O(|f|)$ time.

=== Cube Restriction

Often we want to restrict multiple variables at once.
A *cube* is a conjunction of literals: $x_1 and not x_3 and x_5$.

Restricting by a cube means setting all those variables to their specified values.
This can be done in a single pass through the BDD.

=== Applications

- *Evaluation*: $f(1,0,1) = f|_(x_1=1, x_2=0, x_3=1)$
- *Simplification*: Given constraint $c$, simplify $f$ under $c$
- *Composition building block*: Used in existential quantification

== Composition (Substitution)

*Composition* replaces a variable with a function: $f[x := g]$.

This is more expensive than restriction because $g$ can be an arbitrary BDD, not just a constant.

#algorithm(title: "Compose")[
  ```
  function Compose(f, x, g):
      if is_terminal(f): return f
      if var(f) > x: return f          // x not in f's cone

      if (f, x, g) in ComposeCache:
          return ComposeCache[(f, x, g)]

      if var(f) = x:
          // f = x ? high(f) : low(f)
          // f[x := g] = g ? high(f)[x := g] : low(f)[x := g]
          result = ITE(g,
                       Compose(high(f), x, g),
                       Compose(low(f), x, g))
      else:
          // var(f) < x
          result = mk(var(f),
                      Compose(low(f), x, g),
                      Compose(high(f), x, g))

      ComposeCache[(f, x, g)] = result
      return result
  ```
]

Composition complexity is $O(|f|^2 times |g|^2)$ in the worst case, but often much better in practice.

#warning-box(title: "Composition Pitfall")[
  Repeated composition can be expensive.
  If you need $f[x_1 := g_1, x_2 := g_2, ..., x_k := g_k]$, the order matters and naive sequential composition can blow up.
  Consider vector composition or careful ordering.
]

== Existential and Universal Quantification

*Quantification* abstracts away a variable.

#definition(title: "Existential Quantification")[
  $exists x. f = f|_(x=0) or f|_(x=1)$

  The function is true if $f$ is true for *some* value of $x$.
]

#definition(title: "Universal Quantification")[
  $forall x. f = f|_(x=0) and f|_(x=1)$

  The function is true if $f$ is true for *all* values of $x$.
]

=== Algorithm

#algorithm(title: "Existential Quantification")[
  ```
  function Exists(f, x):
      f0 = Restrict(f, x, 0)
      f1 = Restrict(f, x, 1)
      return Apply(OR, f0, f1)
  ```
]

This takes two restriction passes plus one Apply, so complexity is $O(|f|^2)$.

=== Multiple Variables

Quantifying multiple variables: $exists x_1, x_2, x_3. f$

Naive approach: quantify one at a time.
This can be inefficient because intermediate results may explode.

Better approaches:
- *Order by proximity*: Quantify variables that are close in the ordering together
- *Early quantification*: Interleave quantification with conjunction
- *Conjunctive decomposition*: Split $f$ and quantify pieces

#info-box(title: "Quantification in Model Checking")[
  In symbolic model checking, image computation involves:
  $"Image"(S) = exists bold(x). T(bold(x), bold(x)') and S(bold(x))$

  Efficient quantification is critical for scalability.
  Techniques like "partition TR" and "early quantification" address this.
]

== Optimization Techniques

Several techniques improve operation performance:

=== Cache Sharing

Different operations can share cache entries:
- $f and g$ and $g and f$ are the same (commutativity)
- Some ITE patterns reduce to Apply calls

=== Terminal Case Optimization

Recognizing terminal cases early avoids recursion:
- $f and 0 = 0$, $f or 1 = 1$
- $f and f = f$, $f or f = f$
- $f xor f = 0$, $f -> f = 1$

=== Cofactor Computation

For efficiency, cofactor computation should be $O(1)$:
- If the node's variable matches: return child
- Otherwise: return the node itself (function doesn't depend on that variable)

== Summary

#info-box(title: "Core Operations")[
  - *Apply*: Combine BDDs with any binary operation --- $O(|f| times |g|)$
  - *ITE*: Universal ternary operation --- $O(|f| times |g| times |h|)$
  - *Negation*: $O(1)$ with complement edges, $O(|f|)$ without
  - *Restrict*: Substitute constant for variable --- $O(|f|)$
  - *Compose*: Substitute function for variable --- $O(|f|^2 times |g|^2)$
  - *Quantify*: Abstract away variables --- $O(|f|^2)$

  All operations preserve canonicity: results are automatically reduced.
]

The Apply algorithm is the foundation.
Understanding it deeply is essential for effective BDD use.
In Part II, we dive into implementation details that make these operations fast in practice.
// - Applications in verification (preview)
