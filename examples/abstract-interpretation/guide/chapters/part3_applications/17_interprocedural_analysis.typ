#import "../../theme.typ": *

= Inter-Procedural Analysis <ch-interprocedural>

#reading-path(path: "advanced")

Real-world programs are rarely a single flat list of instructions; they are organized into *functions* or *modules* that call one another.
Inter-procedural analysis reasons across these boundaries, treating functions as modular units.

== Call Graph and Summaries

We assume a "Call Graph" $G_c$ where nodes are functions and edges are calls.

#definition(title: "Function Summary")[
  A summary $S_F: A -> A$ maps an abstract input state to an abstract output state (or return value) for function $F$.
  This allows us to analyze a function once and reuse the result whenever it is "called".
]

- *Context-insensitive*: One summary per function. Fast, but may lose precision if the function behaves differently based on who called it.
- *Context-sensitive*: Summarize per calling context (e.g., "Called from Main" vs "Called from Test").

== The Challenge of Summaries with BDDs

When using BDDs, a unique challenge arises: *Variable Remapping*.
A reusable function `check_range(val)` might be called with `x` in one place and `y` in another.
The BDD for `check_range` is built using a formal parameter `val`.
To apply the summary, we must:
+ *Rename:* Substitute the formal parameter (`val`) with the actual argument (`x`) in the BDD.
+ *Project:* Existentially quantify out local variables of the function to keep the summary clean.

#example-box(title: "Applying a Function Summary")[
  Summary for `check_valid(val)`:
  $ R = ("val" in "ValidSet" and "return" = "True") or ("val" in.not "ValidSet" and "return" = "False") $

  Call site: `call check_valid(x)`

  + *Rename:* Replace `"val" -> "x"`.
  + *Instantiate:*
    $ R' = ("x" in "ValidSet" and "return" = "True") or ("x" in.not "ValidSet" and "return" = "False") $
  + *Join:* Combine $R'$ with the current state at the call site.
]

== Call-Strings (k-limited)

In program analysis, "recursion" is rare in some domains (like embedded systems), but "shared functions" are common.
A `log_error` function might be called from 50 different places.

#definition(title: "k-Call-String Sensitivity")[
  A context is the sequence of the last $k$ functions called.
  Summaries are memoized by `(function, context_k)`.
]

#figure(
  caption: [Context sensitivity distinguishes call paths],

  cetz.canvas({
    import cetz: draw

    // Nodes
    draw.circle((0, 4), radius: 0.5, name: "main", stroke: colors.primary + 1pt)
    draw.content("main", [Main])

    draw.circle((-2, 2), radius: 0.4, name: "A", stroke: colors.primary + 1pt)
    draw.content("A", [A])

    draw.circle((2, 2), radius: 0.4, name: "B", stroke: colors.primary + 1pt)
    draw.content("B", [B])

    draw.circle((0, 0), radius: 0.4, name: "C", stroke: colors.accent + 1pt)
    draw.content("C", [C])

    // Edges
    draw.line("main", "A", stroke: colors.text-light + 0.8pt, mark: (end: ">"))
    draw.line("main", "B", stroke: colors.text-light + 0.8pt, mark: (end: ">"))

    draw.line(
      "A",
      "C",
      stroke: (paint: colors.success, dash: "dashed"),
      mark: (end: ">", stroke: (dash: "solid")),
      name: "A-C",
    )
    draw.content("A-C", text(size: 9pt, fill: colors.success)[Context 1], anchor: "north-east", padding: 0.1)

    draw.line(
      "B",
      "C",
      stroke: (paint: colors.warning, dash: "dashed"),
      mark: (end: ">", stroke: (dash: "solid")),
      name: "B-C",
    )
    draw.content("B-C", text(size: 9pt, fill: colors.warning)[Context 2], anchor: "north-west", padding: 0.1)

    // Contexts
    draw.content((0, -1), text(size: 9pt)[C is analyzed twice])
  }),
)

This is useful if `log_error` needs to know *which* function called it to provide a precise error analysis (e.g., "Error in SQL Module" vs "Error in Rate Limiter").

== Handling Loops and Recursion

Most simple programs form a Directed Acyclic Graph (DAG).
However, recursive algorithms introduce loops.
In these cases, we compute the *Least Fixpoint* of the function summaries.

#algorithm(title: "SCC Worklist")[
  + Compute Strongly Connected Components (SCCs) of the Call Graph.
  + Process SCCs in topological order (leaves to root).
  + For a cyclic SCC, iterate summaries until convergence (using widening if domains are infinite).
  + Export stabilized summaries to callers.
]

== Modular vs Whole-Program Analysis

- *Modular*: Analyze each function in isolation with assumed contracts. Useful for incremental updates (e.g., changing one function doesn't require re-analyzing the whole program).
- *Whole-Program*: Analyze the entire codebase as one giant control flow graph. More precise but slower.

#chapter-summary[
  This chapter extended analysis beyond single procedures to handle function calls and modular programs.

  *Inter-procedural analysis* treats functions as compositional units with computed summaries.
  Rather than re-analyzing every function at each call site, we compute a *function summary* once that captures its input-output behavior abstractly.
  This summary can then be instantiated at each call site through *variable remapping*, dramatically reducing analysis cost.

  *BDDs facilitate variable remapping* through their symbolic representation.
  By building correspondence mappings between caller and callee variables, we can apply Boolean operations to transfer path conditions across procedure boundaries while preserving correlation structure.

  *Context sensitivity* distinguishes different calling contexts, enabling more precise summaries at the cost of additional computation.
  The trade-off between context-insensitive (fast, imprecise), $k$-limited call-string (balanced), and fully context-sensitive (slow, precise) analysis depends on verification goals and program structure.

  This modular approach enables analyzing large programs by dividing them into tractable pieces, with summaries providing the glue that preserves soundness across composition.
]
