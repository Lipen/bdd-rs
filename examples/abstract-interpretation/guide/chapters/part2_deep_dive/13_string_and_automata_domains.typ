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

#example-box(title: "Real-World Example: Malicious Payload Detection")[
  Consider a Deep Packet Inspection (DPI) rule:
  `if payload.contains("attack") { drop() }`

  - *String Domain*: Tracks the set of possible strings in `payload`.
  - *Analysis*:
    - If `payload` comes from a trusted source (e.g., internal config), the domain might prove it never contains "attack".
    - If `payload` is user input, the domain tracks that after the `if`, the payload *must* contain "attack" (on the true branch) or *must not* (on the false branch).
    - This allows proving that subsequent code is only reachable for safe payloads.
]

== Widening/Narrowing Patterns

- Automata quotienting by state partition; refine back (narrowing) with counterexample-guided splitting.
- Length widening by bounds to $[0, +infinity]$; narrow with concrete constraints (e.g., bounded loops).
- Charset widening by class coarsening (e.g., collapse to classes: alpha, digit, other).

#figure(
  caption: [Automata widening by merging states],

  cetz.canvas({
    import cetz: draw

    // Before widening: Chain
    draw.content((0, 4), text(weight: "bold")[Exact Sequence])
    draw.circle((0, 3), radius: 0.3, name: "q0", stroke: colors.primary + 1pt)
    draw.content("q0", [0])
    draw.circle((1.5, 3), radius: 0.3, name: "q1", stroke: colors.primary + 1pt)
    draw.content("q1", [1])
    draw.circle((3, 3), radius: 0.3, name: "q2", stroke: colors.primary + 1pt)
    draw.content("q2", [2])
    draw.circle((4.5, 3), radius: 0.3, name: "q3", stroke: colors.primary + 1pt)
    draw.content("q3", [3])

    draw.line("q0.east", "q1.west", stroke: colors.text-light + 0.8pt, mark: (end: ">"))
    draw.content((0.75, 3.3), [a])
    draw.line("q1.east", "q2.west", stroke: colors.text-light + 0.8pt, mark: (end: ">"))
    draw.content((2.25, 3.3), [a])
    draw.line("q2.east", "q3.west", stroke: colors.text-light + 0.8pt, mark: (end: ">"))
    draw.content((3.75, 3.3), [a])

    // After widening: Loop
    draw.content((0, 1), text(weight: "bold")[Widened (Merged)])
    draw.circle((0, 0), radius: 0.3, name: "w0", stroke: colors.accent + 1pt)
    draw.content("w0", [0])
    draw.circle((2, 0), radius: 0.3, name: "w1", stroke: colors.accent + 1pt)
    draw.content("w1", [1+])

    draw.line("w0.east", "w1.west", stroke: colors.text-light + 0.8pt, mark: (end: ">"))
    draw.content((1, 0.3), [a])

    // Self-loop
    draw.bezier("w1.north-east", "w1.north-west", (2.8, 0.8), (1.2, 0.8), stroke: colors.text-light + 0.8pt, mark: (end: ">"))
    draw.content((2, 1), [a])

    // Arrow
    draw.line((2, 2.5), (2, 1.5), stroke: (paint: colors.warning, thickness: 2pt), mark: (end: ">"))
    draw.content((2.8, 2), text(size: 9pt, fill: colors.warning)[Merge states > 0])
  }),
)

#chapter-summary[
  String analysis benefits from layered abstractions: scalar (length/charset) and language-level (automata).
  Reduced products and prudent widenings yield practical, sound analyses for validation and normalization pipelines.
]
