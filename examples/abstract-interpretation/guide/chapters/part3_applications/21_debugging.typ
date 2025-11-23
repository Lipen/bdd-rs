#import "../../theme.typ": *

= Conclusion & Further Reading <ch-conclusion>

#reading-path(path: "essential")

We have journeyed from the low-level bit-twiddling of Binary Decision Diagrams to the high-level mathematical framework of Abstract Interpretation, culminating in the analysis of complex software systems.

== The Big Picture

The power of this approach lies in the synergy between two distinct fields:

1.  *Abstract Interpretation* provides the *soundness*. It ensures that when we say "Input X cannot cause Error Y", we are mathematically correct. There are no missed corner cases.
2.  *Binary Decision Diagrams* provide the *efficiency*. They allow us to represent and manipulate sets of $2^100$ states as easily as a single integer.

By combining them, we build tools that are both rigorous and scalable --- a rare combination in software verification.

== What We Built

Throughout this guide, we constructed a "Program Analyzer" that can:
- *Parse* program logic into boolean formulas.
- *Encode* program variables into BDD variables.
- *Analyze* reachability across control flow.
- *Verify* safety properties like assertions and invariants.
- *Optimize* code by removing dead branches.

== Further Reading

To deepen your understanding, we recommend the following resources:

- *Abstract Interpretation:*
  - "Abstract Interpretation: A Unified Lattice Model for Static Analysis" (Cousot & Cousot, 1977). The seminal paper.
  - "Principles of Program Analysis" (Nielson, Nielson, & Hankin). The standard textbook.

- *Binary Decision Diagrams:*
  - "Graph-Based Algorithms for Boolean Function Manipulation" (Randal E. Bryant, 1986). The paper that introduced OBDDs.
  - Knuth's "The Art of Computer Programming, Vol 4A". Extensive coverage of BDDs.

- *Software Verification:*
  - "Symbolic Execution and Program Testing" (King, 1976).
  - "Model Checking" (Clarke, Grumberg, Peled).

== Final Words

Formal verification is often seen as an ivory-tower academic pursuit.
We hope this guide has shown that with the right tools (`bdd-rs`) and the right abstractions, it is a practical engineering discipline that can solve real-world problems today.

Happy verifying!
