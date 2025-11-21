#import "../../theme.typ": *

= Interprocedural Analysis <ch-interprocedural>

#reading-path(path: "advanced")

Interprocedural analysis reasons across function boundaries.
We survey context-insensitive summaries, call-strings (k-CFA), summary reuse, recursion handling, and modular analysis trade-offs.

== Call Graph and Summaries

We assume a call graph $G_c$ and per-function transfer summaries.

#definition(title: "Function Summary")[
  A summary $S_f: A -> A$ maps an abstract input to an abstract output at the function boundary.
  For multi-argument functions, use product domains or named parameters.
]

- Context-insensitive: one summary per function (fast, imprecise).
- Context-sensitive: summarize per context key (e.g., call-string up to length $k$).

== The Challenge of Summaries with BDDs

When using BDDs, a unique challenge arises: *Variable Remapping*.
A function `foo(a, b)` might be called as `foo(x, y)` in one place and `foo(z, w)` in another.
The BDD for `foo` is built using formal parameters `a` and `b`.
To apply the summary, we must:
+ *Rename:* Substitute formal parameters (`a`, `b`) with actual arguments (`x`, `y`) in the BDD.
+ *Project:* Existentially quantify out local variables of `foo` to keep the summary clean.

#example-box(title: "Applying a Summary")[
  Summary for `max(a, b)`:
  $ R = (a > b and "ret" = a) or (a <= b and "ret" = b) $

  Call site: `y = max(x, 10)`

  + *Rename:* Replace `a -> x`, `b -> 10`, `"ret" -> y`.
  + *Instantiate:*
    $ R' = (x > 10 and y = x) or (x <= 10 and y = 10) $
  + *Join:* Combine $R'$ with the current state at the call site.
]

== Call-Strings (k-limited)

#definition(title: "k-Call-String Sensitivity")[
  A context is the sequence of the last $k$ call sites.
  Summaries are memoized by `(f, context_k)`; joins occur when contexts collide.
]

Pros: captures common patterns like factory methods; Cons: combinatorial growth bounded by $k$.

== Recursion and Fixpoints

Recursive SCCs in $G_c$ require mutual fixpoint computation.
Use worklists over SCCs and apply widenings at call heads.

#algorithm(title: "SCC Worklist with Widening")[
  + Compute SCCs of $G_c$; process in topological order
  + For SCC $C$, iterate summaries for functions in $C$ until convergence (with widening at headers)
  + Export stabilized summaries to callers
]

== Heap-Parameter Passing

Summaries over heap require heap abstractions as parameters (e.g., points-to maps and abstract stores).
Widening on heap parameters maintains termination; reduction with caller facts improves precision.

== Modular vs Whole-Program

- Modular: compile summaries with contracts; re-check clients quickly
- Whole-program: more precise global fixpoint but higher cost

#chapter-summary[
  Interprocedural analysis hinges on summaries, context selection (e.g., k-call-strings), SCC fixpoints with widening, and heap-aware parameterization.
  It balances modularity, precision, and scalability.
]

#pagebreak()
