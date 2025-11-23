#import "../../theme.typ": *

= Precision Techniques and Design Patterns <ch-precision-techniques>

#reading-path(path: "advanced")

In the previous chapters, we built a functional analyzer.
It is sound, meaning it will never miss a bug.
However, a sound analyzer is not necessarily a *useful* one.
If it reports a potential violation for every single packet, it provides no value.
This is the "False Positive" problem.

The central craft of Abstract Interpretation is balancing three competing goals:
+ *Precision*: Minimizing false alarms by tracking more detail.
+ *Performance*: Analyzing large policies quickly (seconds, not hours).
+ *Termination*: Ensuring the analysis always finishes, even with loops.

This chapter catalogs the advanced techniques required to turn a toy analyzer into a production-grade tool.
We will move beyond simple domains and explore how to combine them, split them, and accelerate them.

== The Power of Combination: Reduced Products

Real-world policies are complex.
They involve boolean logic ("allow if TCP and port 80"), arithmetic ("packet length > 64"), and set membership ("src ip in 10.0.0.0/8").
No single abstract domain is good at all of these.

- *BDDs* are excellent for boolean logic and sets of discrete values, but they explode when tracking arithmetic ranges.
- *Intervals* are great for arithmetic bounds ($min <= x <= max$) but lose relationships between variables (e.g., $x = y$).

To get the best of both worlds, we run multiple domains in parallel.
This is called a *Product Domain*.
However, simply running them side-by-side is not enough; they must communicate.
This communication is called *Reduction*.

#intuition-box[
  *The Two Detectives*

  Imagine two detectives investigating a suspect.
  - Detective A (Intervals) knows: "The suspect is between 20 and 30 years old."
  - Detective B (BDDs) knows: "The suspect is either a teenager (13-19) or a senior citizen (65+)."

  Individually, neither can identify the suspect.
  - Detective A thinks 25 is possible.
  - Detective B thinks 15 is possible.

  But if they talk to each other ("Reduce"), they realize their information is contradictory.
  The intersection of $[20, 30]$ and $\{13..19, 65..\}$ is empty.
  The set of suspects is empty ($bot$).
  They have proven the scenario is impossible.
]

#definition(title: "Reduced Product")[
  Given two abstract domains $A$ and $B$, the *Reduced Product* $A times B$ is a domain that represents the intersection of their concretizations: $gamma(a, b) = gamma(a) inter gamma(b)$.
  The reduction operator $rho$ exchanges information between $A$ and $B$ to refine both, such that $rho(a, b) lle (a, b)$.
]

=== Example: Mutual Refinement in Firewalls

Consider a rule that drops private IP addresses, but only for short packets:

```rust
if src_ip >= 10.0.0.0 && src_ip <= 10.255.255.255 {
    if len < 64 {
        drop;
    }
}
```

+ The *Interval Domain* analyzes the condition and restricts `src_ip` to `[10.0.0.0, 10.255.255.255]` and `len` to `[0, 63]`.
+ The *BDD Domain* tracks the boolean flags `is_private` and `is_short`.
+ *Reduction Cycle*:
  - Interval $->$ BDD: "The `src_ip` range implies `is_private` is TRUE."
  - Interval $->$ BDD: "The `len` range implies `is_short` is TRUE."
  - BDD $->$ Interval: "Since `is_private` is TRUE, prune any paths where `src_ip` is outside 10/8." (Redundant here, but useful if the BDD learned it from elsewhere).

Without reduction, the BDD might think `!is_private` is still possible if the control flow was complex.

== Divide and Conquer: State Partitioning

One of the biggest sources of imprecision is the *Merge* operation ($ljoin$).
When control flow paths join (e.g., after an `if/else`), we merge their abstract states to keep the analysis tractable.
However, merging destroys relationships (relational information).

If one path has `{proto: TCP, port: 80}` and another has `{proto: UDP, port: 53}`, merging them in a non-relational domain gives:
`{proto: {TCP, UDP}, port: {80, 53}}`.
This now includes the spurious state `{proto: UDP, port: 80}`, which might trigger a false alarm (e.g., "UDP traffic on port 80 is blocked").

=== Trace Partitioning

The solution is *Partitioning*: keeping distinct states separate based on some criteria.
Instead of one monolithic abstract state, we maintain a map:
`Map<PartitionKey, AbstractState>`.

#example-box(title: "Partitioning by Protocol")[
  In our FirewallChecker, the most effective partition key is often the *Protocol* (TCP vs. UDP vs. ICMP).

  We maintain separate invariants for TCP flows and UDP flows.
  - The TCP partition tracks sequence numbers and flags.
  - The UDP partition tracks lengths and checksums.

  This prevents "pollution" where UDP packets are flagged for missing TCP flags.
]

This technique is also known as *Disjunctive Completion*.
We effectively delay the merge until the end of the analysis, or until the number of partitions grows too large.

=== Context Sensitivity (Inter-procedural)

When analyzing functions (e.g., named ACLs or sub-routines), merging the state from all call sites leads to imprecision.
If `check_access()` is called from a trusted interface and an untrusted interface, merging the states blurs the distinction.

*Context Sensitivity* partitions the state by the *Call String* (the stack of function calls).
- `check_access` called from `main -> trusted_zone`
- `check_access` called from `main -> internet_zone`

This allows the analyzer to verify that `check_access` behaves correctly for *each* context independently.

== Accelerating Convergence: Widening and Narrowing

In @ch-fixpoint-algorithms, we discussed finding the fixpoint of loops.
For domains with infinite height (like Intervals or Polyhedra), standard iteration might never terminate.
We need a way to guess the limit.

=== Widening ($widen$)

Widening is an operator that extrapolates the growth of an abstract value.
It observes the trend between two iterations and jumps to a safe upper bound.
If we see a value growing from `[0, 1]` to `[0, 2]`, widening might guess `[0, infinity]`.

#warning-box(title: "The Risk of Widening")[
  Widening guarantees termination, but it is *imprecise*.
  It often over-approximates too much, including states that are not actually reachable (like infinite packet sizes).
  This can lead to false positives.
]

=== Thresholded Widening

To tame the widening, we use *Thresholds* (also called *Landmarks*).
Instead of jumping to infinity, we jump to known "interesting" values.

In networking, interesting values for packet sizes include:
- 64 bytes (Minimum Ethernet)
- 1500 bytes (Standard MTU)
- 9000 bytes (Jumbo Frames)
- 65535 bytes (Max IP)

If the packet size grows past 1500, we widen to 9000, not infinity.
This keeps the analysis precise enough to prove properties like "packets never exceed Jumbo Frame size".

=== Narrowing ($narrow$)

After widening overshoots the target, we use *Narrowing* to shrink the result back down.
We run a few more iterations of the loop using the standard semantic function.
Since the widening established a safe upper bound, these subsequent iterations can only refine the result, recovering precision.

*Sequence*:
+ Iterate with $widen$ (Widen) until convergence (Post-fixpoint).
+ Iterate with $narrow$ (Narrow) for $k$ steps to improve precision.

== Engineering Heuristics

Beyond the mathematics, the success of an analyzer often depends on engineering choices.

=== BDD Variable Ordering

For BDDs, the order of variables determines the size of the graph.
A bad order can lead to exponential blowup.

#insight-box[
  *Heuristic:* Place variables that are tested together close together in the order.
  For firewalls, we typically order variables by protocol layer:
  + Ethernet Header (Type)
  + IP Header (Src, Dst, Proto)
  + Transport Header (Ports, Flags)
]

=== Resource Budgets

To prevent the analyzer from hanging on complex inputs, we enforce budgets:
- *Partition Budget*: Max 50 partitions per control location. If exceeded, force a merge.
- *BDD Node Budget*: Abort if a BDD exceeds 1 million nodes.
- *Time Budget*: Soft timeout for the solver (e.g., 5 seconds per rule).

When a budget is hit, we force a merge (loss of precision) rather than crashing (loss of availability).
This is a "Fail-Open" or "Fail-Safe" strategy depending on the application.

== User Experience: Explaining the Result

A verification tool is only as good as its error messages.
Telling a user "Assertion Failed" is useless.

=== Minimal Counterexamples

Because we use BDDs, we have the set of *all* failing packets.
We should present the *simplest* one to the user.
- Prefer IPv4 over IPv6.
- Prefer zero flags over set flags.
- Prefer standard ports over random high ports.

=== Trace Slicing

If a packet is dropped, the user wants to know *why*.
A trace slice removes all rules that did not contribute to the decision.
If a packet was dropped because of its Port, the slice should hide the IP checks.
This requires tracking *provenance* or *dependencies* during the analysis.

#chapter-summary[
  - *Reduced Products* allow different domains to share information, proving properties neither could prove alone.
  - *Partitioning* prevents precision loss at merge points by keeping incompatible states separate (e.g., TCP vs UDP).
  - *Widening with Thresholds* ensures loops terminate quickly while respecting domain-specific boundaries (like MTU).
  - *Engineering Heuristics* like variable ordering and resource budgets are critical for scaling to real-world networks.
]
