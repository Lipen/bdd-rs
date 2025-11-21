#import "../../theme.typ": *

= AI-Guided Analysis <ch-ai-guided>

#reading-path(path: "advanced")

The intersection of Artificial Intelligence (specifically Large Language Models) and Formal Methods is a rapidly evolving frontier.
While Abstract Interpretation provides mathematical guarantees, it often struggles with computational complexity and the "widening" problem (losing precision to ensure termination).
AI models, on the other hand, are excellent at pattern recognition and guessing, but lack guarantees.

== The Wizard and the Clerk

We can conceptualize a hybrid system using the analogy of a Wizard and a Clerk.

- *The Wizard (AI/LLM):* Brilliant but unreliable. Can guess complex loop invariants, suggest widening thresholds, or identify likely specifications.
- *The Clerk (Abstract Interpreter):* Pedantic and rigorous. Checks every detail. If the Wizard's guess is correct, the Clerk verifies it efficiently. If the guess is wrong, the Clerk rejects it.

== Invariant Synthesis

Instead of iteratively computing a fixpoint (which can be slow), we can ask an LLM to predict the loop invariant.

#example-box(title: "Neuro-Symbolic Loop Analysis")[
  + *Prompt:* "Given this loop `while x < 100 { x += 2 }`, what is the invariant?"
  + *AI Response:* "Invariant: `x % 2 == 0 && x <= 100`"
  + *Verifier:* The BDD analyzer checks if this formula is inductive.
     - Base case: `init => inv`? Yes.
     - Inductive step: `inv && cond => inv'`? Yes.
  + *Result:* Verified instantly without iteration.
]

== Widening Oracles

Widening operators ($nabla$) are necessary for termination but often lose too much information.
A "Widening Oracle" (trained ML model) can look at the iteration history and the code structure to suggest:
- *When* to widen (maybe wait 3 more iterations).
- *How* to widen (e.g., "widen to the next constant appearing in the code").

== Future Directions

As LLMs become more capable of understanding code semantics, we expect "Conversational Verification" to become a reality: a dialogue where the human, the AI, and the formal verifier work together to prove software correctness.
