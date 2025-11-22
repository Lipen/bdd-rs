#import "../../theme.typ": *

= String and Automata Domains <ch-strings-automata>

#reading-path(path: "advanced") #h(0.7em) #reading-path(path: "implementation")

String-heavy programs require reasoning about concatenation, length, prefixes/suffixes, and membership in regular sets (e.g., input validation, sanitization).
This chapter develops abstract domains for strings, from lightweight numeric properties to regular-language abstractions via finite automata, and discusses widenings and reduced products.

== Motivation and Threat Model

Typical security and correctness questions:
- Does input validation enforce membership in a safe regular language (e.g., email, path, identifier)?
- Can a dangerous character reach a sink after normalization (e.g., doubled slashes collapsed)?
- Do string lengths stay within bounds?

We aim for conservative answers: no false negatives.

== Scalar String Properties: Length and Charset

#definition(title: "Length Domain")[
  Elements are $[m, n]$ with $0 <= m <= n <= +infinity$.
  Join/meet are interval operations; widening moves unstable bounds to $0$ or $+infinity$.

  Transformers:
  - $"len"(x dot y) in [m_x + m_y, n_x + n_y]$
  - $"len"(x."trim")$ narrows upper bound by at most a constant.
]

#definition(title: "Charset Domain")[
  Track a set of allowed characters $C subset.eq Sigma$ (alphabet).
  Join is union; meet is intersection; widening limits the number of tracked classes.
]

#example-box(title: "Reduced Product: Length × Charset")[
  Combining length and charset refines feasibility:
  - If charset excludes `'/'`, then `normalize(path)` cannot introduce `'//'` via contraction.
  - If length lower bound is 1 and charset excludes NUL, `is_empty` is provably false.
]

== Regular-Language Abstraction via Automata

Represent sets of strings with a deterministic finite automaton (DFA) $A = (Q, q_0, F, delta)$.

#definition(title: "Automata Domain")[
  The abstract element is a DFA; concretization is its language $L(A)$.
  - Join: language union via automaton union (product construction + accepting set union)
  - Meet: language intersection via product automaton + accepting set intersection
  - Widening: language over-approximation by merging states (quotienting) using a refinement-stable partition
]

#theorem(title: "Soundness of Quotient Widening")[
  Let $tilde$ be a right-invariant equivalence on $Q$ (Myhill–Nerode style refinement-stable).
  Quotient $A / tilde$ recognizes a language $L'$ with $L(A) subset.eq L'$.
  Thus replacing $A$ by $A / tilde$ during iteration preserves soundness and ensures convergence under bounded refinements.
]

== Transformers for Common Operations

- Concatenation: $L(A_x dot A_y) = \{ x y mid(|) x in L(A_x), y in L(A_y) \}$ via epsilon-bridge construction with determinization.
- Prefix/Suffix: $"prefix"_k(L)$ and $"suffix"_k(L)$ realized by state annotation up to bound $k$; widen by increasing $k$ lazily.
- Replace: Over-approximate $"replace"(s, "re", r)$ by composing with a transducer; when unavailable, approximate by charset and length effects plus inclusion checks.
- Substring: Restrict by positions using length bounds; refine with automata if indices are narrow.

#warning-box(title: "Determinization Blow-up")[
  Determinization may be exponential.
  Use bounds (e.g., depth, number of states) and switch to scalar domains when limits exceed thresholds.
]

== Reduced Products and Cooperation

Combine automata with scalar domains to improve precision:
- Length refines automata by trimming unreachable states (length-infeasible).
- Charset prunes transitions that produce forbidden characters.
- BDD control refines string facts path-sensitively (e.g., `if is_alpha(x) { ... }`).

#definition(title: "Granger-Style Reduced Product")[
  Let $(A_1, A_2)$ be two abstract elements.
  A *reduction* operator $rho(A_1, A_2)$ computes a pair $(A_1', A_2')$ such that $gamma(A_1', A_2') = gamma(A_1, A_2)$ and $A_i' <= A_i$.
  Implement by mutual refinement until a local fixpoint or budgets are exhausted.
]

== Validation and Normalization Pipelines

We model pipelines `validate; normalize; use`:
- Validation: assert $x in L_"safe"$ (meet with DFA for $L_"safe"$)
- Normalization: apply length/charset-preserving rewrites; ensure closure under rewrites remains in $L_"safe"$
- Use: sinks (e.g., regex match, path join) proved safe by inclusion: $L("current") subset.eq L_"safe"$

#example-box(title: "Path Sanitization")[
  `normalize` collapses repeated slashes `//` and forbids `..`.
  Prove: after normalization, every path is in $L_"nosneak"$ disallowing traversal.
  Use length lower bounds and automata intersection; explain counterexamples via shortest witness in DFA.
]

== Widening/Narrowing Patterns

- Automata quotienting by state partition; refine back (narrowing) with counterexample-guided splitting.
- Length widening by bounds to $[0, +infinity]$; narrow with concrete constraints (e.g., bounded loops).
- Charset widening by class coarsening (e.g., collapse to classes: alpha, digit, other).

#chapter-summary[
  String analysis benefits from layered abstractions: scalar (length/charset) and language-level (automata).
  Reduced products and prudent widenings yield practical, sound analyses for validation and normalization pipelines.
]
