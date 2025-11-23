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

== Invariant Synthesis

Instead of iteratively computing a fixpoint (which can be slow), we can ask an LLM to predict the loop invariant.

#example-box(title: "Neuro-Symbolic Loop Analysis")[
  + *Prompt:* "Given this packet loop `while ttl > 0 { ttl -= 1; forward() }`, what is the invariant?"
  + *AI Response:* "Invariant: `ttl <= 64` (assuming initial max TTL)"
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
- *How* to widen (e.g., "widen to the MTU size 1500" instead of infinity).

The soundness is preserved because the Abstract Interpreter still performs the widening and subsequent verification; the AI only guides the *strategy*.

== Future Directions

As LLMs become more capable of understanding code semantics, we expect "Conversational Verification" to become a reality: a dialogue where the human, the AI, and the formal verifier work together to prove software correctness.
