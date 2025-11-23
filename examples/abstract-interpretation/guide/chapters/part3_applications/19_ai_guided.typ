#import "../../theme.typ": *

= AI-Guided Analysis <ch-ai-guided>

#reading-path(path: "advanced")

#warning-box(title: "Experimental Frontier")[
  This chapter discusses emerging techniques at the intersection of AI and Formal Methods.
  Unlike the previous chapters, these methods are active research topics and not yet standard practice.
]

The intersection of Artificial Intelligence --- specifically Large Language Models (LLMs) --- and Formal Methods represents a rapidly evolving frontier.
While Abstract Interpretation provides rigorous mathematical guarantees, it often grapples with computational complexity and the precision loss inherent in the "widening" operators required for termination.
Conversely, AI models excel at pattern recognition and heuristic guessing but lack formal guarantees.

== The Wizard and the Clerk

We can conceptualize a hybrid system using the analogy of a Wizard and a Clerk.

- *The Wizard (AI/LLM):* Brilliant but unreliable.
  Can guess complex loop invariants, suggest widening thresholds, or identify likely specifications.
- *The Clerk (Abstract Interpreter):* Pedantic and rigorous.
  Checks every detail.
  If the Wizard's guess is correct, the Clerk verifies it efficiently.
  If the guess is wrong, the Clerk rejects it.

#figure(
  caption: [AI-Guided Verification Loop],

  cetz.canvas({
    import cetz: draw

    // AI Node
    draw.circle((0, 4), radius: 0.5, name: "ai", stroke: colors.accent + 1pt)
    draw.content("ai", [AI])
    draw.content("ai.north", text(size: 9pt)[Guess Invariant], anchor: "south", padding: 0.2)

    // Verifier Node
    draw.rect((-1, 1), (1, 2), name: "verifier", stroke: colors.primary + 1pt)
    draw.content("verifier", [Verifier])

    // Result Nodes
    draw.circle((-2, -1), radius: 0.5, name: "ok", stroke: colors.success + 1pt)
    draw.content("ok", [OK])

    draw.circle((2, -1), radius: 0.5, name: "fail", stroke: colors.error + 1pt)
    draw.content("fail", [Retry])

    // Edges
    draw.line("ai.south", "verifier.north", stroke: colors.text-light + 0.8pt, mark: (end: ">"), name: "ai-verifier")
    draw.content("ai-verifier", [Proposed \ Invariant], anchor: "east", padding: 0.2)

    draw.line("verifier", "ok", stroke: colors.success + 1pt, mark: (end: ">"), name: "verifier-ok")
    draw.content("verifier-ok", text(fill: colors.success)[Valid], anchor: "south-east", padding: 0.1)

    draw.line("verifier", "fail", stroke: colors.error + 1pt, mark: (end: ">"), name: "verifier-fail")
    draw.content("verifier-fail", text(fill: colors.error)[Invalid], anchor: "south-west", padding: 0.1)

    draw.bezier(
      "fail.east",
      "ai.east",
      (3, 0),
      (2, 4),
      stroke: (paint: colors.text-light, dash: "dashed"),
      mark: (end: ">", stroke: (dash: "solid")),
      name: "feedback-loop",
    )
    draw.content("feedback-loop.mid", [Feedback], anchor: "south-west", padding: 0.1)
  }),
)

== Invariant Synthesis

Instead of iteratively computing a fixpoint (which can be slow), we can ask an LLM to predict the loop invariant.

#example-box(title: "Neuro-Symbolic Loop Analysis")[
  + *Prompt:* "Given this loop `while i > 0 { i -= 1; process() }`, what is the invariant?"
  + *AI Response:* "Invariant: `i <= 100` (assuming initial max)"
  + *Verifier:* The BDD analyzer checks if this formula is inductive.
    - Base case: `init => inv`? Yes.
    - Inductive step: `inv && cond => inv'`? Yes.
  + *Result:* Verified instantly without iteration.
]

This approach leverages the *Checkable Proof* property: it is often harder to find a proof (invariant) than to check it.
The AI acts as an oracle for the fixpoint operator `lfp(f)`.

== Widening Oracles

Widening operators ($widen$) are necessary for termination but often lose too much information.
A "Widening Oracle" (trained ML model) can look at the iteration history and the code structure to suggest:
- *When* to widen (maybe wait 3 more iterations).
- *How* to widen (e.g., "widen to the buffer size 4096" instead of infinity).

The soundness is preserved because the Abstract Interpreter still performs the widening and subsequent verification; the AI only guides the *strategy*.

== Future Directions

As LLMs become more capable of understanding code semantics, we expect "Conversational Verification" to become a reality: a dialogue where the human, the AI, and the formal verifier work together to prove software correctness.
