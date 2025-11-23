#import "../../theme.typ": *

= Precision Techniques and Design Patterns <ch-precision-techniques>

#reading-path(path: "advanced")

Previous chapters built a functional analyzer that is sound (never misses a bug).
A sound analyzer is not necessarily *useful*: reporting a potential violation for every input provides no value.
This is the "False Positive" problem.

The central craft of Abstract Interpretation is balancing three competing goals:
+ *Precision*: Minimizing false alarms by tracking more detail.
+ *Performance*: Analyzing large programs quickly (seconds, not hours).
+ *Termination*: Ensuring the analysis always finishes, even with loops.

We catalog advanced techniques to turn a toy analyzer into a production-grade tool, exploring how to combine, split, and accelerate domains.

== The Power of Combination: Reduced Products

Real-world programs involve boolean logic ("allow if Admin and id > 100"), arithmetic ("buffer size > 64"), and set membership ("value in [0, 100]").
No single abstract domain handles all of these well.

- *BDDs* are excellent for boolean logic and sets of discrete values, but they explode when tracking arithmetic ranges.
- *Intervals* are great for arithmetic bounds ($min <= x <= max$) but lose relationships between variables (e.g., $x = y$).

We run multiple domains in parallel (*Product Domain*).
Simply running them side-by-side is not enough; they must communicate via *Reduction*.

#intuition-box[
  *The Two Detectives*

  Imagine two detectives investigating a suspect.
  - Detective A (Intervals) knows: "The suspect is between 20 and 30 years old."
  - Detective B (BDDs) knows: "The suspect is either a teenager (13-19) or a senior citizen (65+)."

  Individually, neither can identify the suspect.
  - Detective A thinks 25 is possible.
  - Detective B thinks 15 is possible.

  But if they talk to each other ("Reduce"), they realize their information is contradictory.
  The intersection of $[20, 30]$ and ${13..19, 65..}$ is empty.
  The set of suspects is empty ($bot$).
  They have proven the scenario is impossible.
]

#definition(title: "Reduced Product")[
  Given two abstract domains $A$ and $B$, the *Reduced Product* $A times B$ is a domain that represents the intersection of their concretizations: $gamma(a, b) = gamma(a) inter gamma(b)$.
  The reduction operator $rho$ exchanges information between $A$ and $B$ to refine both, such that $rho(a, b) lle (a, b)$.
]

=== Implementation Pattern

In Rust, we implement this by composing structs.
The `reduce` method is the key addition to the `AbstractDomain` trait.

```rust
struct ProductDomain<A, B> {
    dom_a: A,
    dom_b: B,
}

impl<A: AbstractDomain, B: AbstractDomain> AbstractDomain for ProductDomain<A, B> {
    fn meet(&self, other: &Self) -> Self {
        let mut res = ProductDomain {
            dom_a: self.dom_a.meet(&other.dom_a),
            dom_b: self.dom_b.meet(&other.dom_b),
        };
        res.reduce(); // Critical step!
        res
    }

    fn reduce(&mut self) {
        // Loop until fixpoint or budget exceeded
        loop {
            let old_state = self.clone();

            // 1. Transfer info A -> B
            if let Some(range) = self.dom_a.get_range("x") {
                self.dom_b.constrain_variable("x", range);
            }

            // 2. Transfer info B -> A
            if self.dom_b.is_constant("y", 0) {
                self.dom_a.set_constant("y", 0);
            }

            if *self == old_state { break; }
        }
    }
}
```

=== Example: Mutual Refinement in Safety Checks

Consider a rule that flags unsafe values, but only for small buffers:

```rust
if x >= 100 && x <= 200 {
    if y < 10 {
        error;
    }
}
```

+ The *Interval Domain* analyzes the condition and restricts `x` to `[100, 200]` and `y` to `[0, 9]`.
+ The *BDD Domain* tracks the boolean flags `in_range` and `is_small`.
+ *Reduction Cycle*:
  - Interval $->$ BDD: "The `x` range implies `in_range` is TRUE."
  - Interval $->$ BDD: "The `y` range implies `is_small` is TRUE."
  - BDD $->$ Interval: "Since `in_range` is TRUE, prune any paths where `x` is outside [100, 200]." (Redundant here, but useful if the BDD learned it from elsewhere).

Without reduction, the BDD might think `!in_range` is still possible if the control flow was complex.

== Divide and Conquer: State Partitioning

One of the biggest sources of imprecision is the *Merge* operation ($ljoin$).
When control flow paths join (e.g., after an `if/else`), we merge their abstract states to keep the analysis tractable.
However, merging destroys relationships (relational information).

If one path has `{type: A, val: 10}` and another has `{type: B, val: 20}`, merging them in a non-relational domain gives:
`{type: {A, B}, val: {10, 20}}`.
This now includes the spurious state `{type: B, val: 10}`, which might trigger a false alarm (e.g., "Type B with val 10 is invalid").

=== Trace Partitioning

The solution is *Partitioning*: keeping distinct states separate based on some criteria.
Instead of one monolithic abstract state, we maintain a map:
`Map<PartitionKey, AbstractState>`.

#definition(title: "Partitioned Domain")[
  Let $K$ be a set of partition keys (e.g., request types, call sites).
  The partitioned domain $D_K$ maps each key to an abstract state: $D_K = K -> D$.
  The concretization is the union of all partitions: $gamma(f) = union_(k in K) gamma(f(k))$.
]

#example-box(title: "Partitioning by Request Type")[
  In our Analyzer, the most effective partition key is often the *Request Type* (GET vs. POST vs. PUT).

  We maintain separate invariants for GET requests and POST requests.
  - The GET partition tracks query parameters.
  - The POST partition tracks body size and content type.

  This prevents "pollution" where POST requests are flagged for missing query parameters.
]

=== Implementation Strategy

We can implement this using a `HashMap`.
The `join` operation becomes complex: we only join states with matching keys.

```rust
struct PartitionedDomain<D> {
    partitions: HashMap<RequestType, D>,
}

impl<D: AbstractDomain> AbstractDomain for PartitionedDomain<D> {
    fn join(&self, other: &Self) -> Self {
        let mut new_map = self.partitions.clone();
        for (key, state) in &other.partitions {
            new_map
                .entry(key.clone())
                .and_modify(|s| *s = s.join(state))
                .or_insert(state.clone());
        }
        PartitionedDomain { partitions: new_map }
    }
}
```

This technique is also known as *Disjunctive Completion*.
We effectively delay the merge until the end of the analysis, or until the number of partitions grows too large.

=== Context Sensitivity (Inter-procedural)

When analyzing functions (e.g., helper methods or sub-routines), merging the state from all call sites leads to imprecision.
If `validate_input()` is called from a trusted module and an untrusted module, merging the states blurs the distinction.

*Context Sensitivity* partitions the state by the *Call String* (the stack of function calls).
- `validate_input` called from `main -> admin_module`
- `validate_input` called from `main -> user_module`

This allows the analyzer to verify that `validate_input` behaves correctly for *each* context independently.

== Accelerating Convergence: Widening and Narrowing

In @ch-fixpoint-algorithms, we discussed finding the fixpoint of loops.
For domains with infinite height (like Intervals or Polyhedra), standard iteration might never terminate.
We need a way to guess the limit.

=== Widening ($widen$)

Widening is an operator that extrapolates the growth of an abstract value.
It observes the trend between two iterations and jumps to a safe upper bound.
If we see a value growing from `[0, 1]` to `[0, 2]`, widening might guess `[0, infinity]`.

#definition(title: "Widening Operator")[
  The widening operator $widen$ must satisfy:
  + *Soundness*: $x lle (x widen y)$ and $y lle (x widen y)$.
  + *Termination*: For any sequence $x_0, x_1, ...$, the sequence $y_0 = x_0, y_(i+1) = y_i widen x_(i+1)$ eventually stabilizes.
]

#warning-box(title: "The Risk of Widening")[
  Widening guarantees termination, but it is *imprecise*.
  It often over-approximates too much, including states that are not actually reachable (like infinite buffer sizes).
  This can lead to false positives.
]

=== Thresholded Widening

To tame the widening, we use *Thresholds* (also called *Landmarks*).
Instead of jumping to infinity, we jump to known "interesting" values.

In systems programming, interesting values for buffer sizes include:
- 64 bytes (Cache Line)
- 4096 bytes (Page Size)
- 65536 bytes (Max Segment)
- Max Int

If the buffer size grows past 4096, we widen to 65536, not infinity.
This keeps the analysis precise enough to prove properties like "buffers never exceed Max Segment size".

```rust
fn widen_threshold(old: &Interval, new: &Interval, thresholds: &[u32]) -> Interval {
    let min = if new.min < old.min {
        // Growing downwards: jump to next lower threshold
        thresholds.iter().rev().find(|&&t| t <= new.min).copied().unwrap_or(0)
    } else { old.min };

    let max = if new.max > old.max {
        // Growing upwards: jump to next higher threshold
        thresholds.iter().find(|&&t| t >= new.max).copied().unwrap_or(u32::MAX)
    } else { old.max };

    Interval { min, max }
}
```

=== Narrowing ($narrow$)

After widening overshoots the target, we use *Narrowing* to shrink the result back down.
We run a few more iterations of the loop using the standard semantic function.
Since the widening established a safe upper bound, these subsequent iterations can only refine the result, recovering precision.

The complete fixpoint algorithm proceeds in two phases.
First, we iterate using the widening operator until convergence, establishing a post-fixpoint that safely over-approximates all reachable states.
Then, we apply narrowing for $k$ additional steps, refining this conservative approximation to recover precision lost to aggressive extrapolation.

== Engineering Heuristics

Beyond the mathematics, the success of an analyzer often depends on engineering choices.

=== BDD Variable Ordering

For BDDs, the order of variables determines the size of the graph.
A bad order can lead to exponential blowup.

#insight-box[
  *Heuristic:* Place variables that are tested together close together in the order.
  For programs, we typically order variables by scope or usage:
  + Global Flags
  + Control Flow Variables
  + Data Variables
]

*Why does this matter?*
Consider the function $(a_1 and b_1) or (a_2 and b_2) or ... or (a_n and b_n)$.
- If ordered $a_1, b_1, a_2, b_2, ...$, the BDD size is linear $O(n)$.
- If ordered $a_1, ..., a_n, b_1, ..., b_n$, the BDD size is exponential $O(2^n)$.

=== Resource Budgets

To prevent the analyzer from hanging on complex inputs, we enforce budgets.
We pass a `Context` object through the analysis that tracks consumption.

```rust
struct AnalysisContext {
    bdd_node_limit: usize,
    partition_limit: usize,
    start_time: Instant,
}

impl AnalysisContext {
    fn check_budget(&self) -> Result<(), Error> {
        if self.start_time.elapsed() > Duration::from_secs(5) {
            return Err(Error::Timeout);
        }
        Ok(())
    }
}
```

When a budget is hit, we force a merge (loss of precision) rather than crashing (loss of availability).
This is a "Fail-Open" or "Fail-Safe" strategy depending on the application.

== User Experience: Explaining the Result

A verification tool is only as good as its error messages.
Telling a user "Assertion Failed" is useless.
We need to provide a concrete input that triggers the failure, and explain *why* it triggers it.

=== Minimal Counterexamples

Because we use BDDs, we have the set of *all* failing inputs (the set of valuations that satisfy the negation of the property).
However, showing a BDD to a user is not helpful.
We want to present the *simplest* counterexample.

We define "simplest" using a cost function:
+ *Small integers* are simpler than large ones.
+ *False flags* are simpler than true flags.
+ *Standard values* (0, 1) are simpler than random large values.
+ *Unconstrained variables* should be ignored (don't care).

This corresponds to finding the *shortest path* to the `true` terminal in the BDD, where edge weights are determined by the "complexity" of the variable assignment.

#algorithm(title: "Shortest Path Counterexample")[
  *Input:* BDD Node $"root"$, Cost Function $"cost"("var", "val")$.

  *Output:* Minimal cost assignment $A$.

  + $"dist" <- lambda u . infinity$ $quad slash.double$ Initialize all distances.
  + $"dist"[#true] <- 0$
  + *for each* node $u$ in topological order (bottom-up) *do*
    + $x <- "var"(u)$
    + $l, h <- "low"(u), "high"(u)$
    + $"cost"_l <- "dist"[l] + "cost"(x, 0)$
    + $"cost"_h <- "dist"[h] + "cost"(x, 1)$
    + $"dist"[u] <- min("cost"_l, "cost"_h)$
    + $"choice"[u] <- ("cost"_l <= "cost"_h ? 0 : 1)$ $quad slash.double$ Store optimal branch.

  + $A <- emptyset$ $quad slash.double$ Reconstruct path top-down.
  + $"curr" <- "root"$
  + *while* $"curr" != #true$ *and* $"curr" != #false$ *do*
    + $"val" <- "choice"["curr"]$
    + $A <- A union {( "var"("curr"), "val" )}$
    + $"curr" <- ("val" == 0 ? "low"("curr") : "high"("curr"))$
  + *return* $A$
]

```rust
fn find_minimal_counterexample(bdd: &Bdd, root: Ref) -> Option<Input> {
    if bdd.is_zero(root) {
        return None; // No counterexample exists (property holds)
    }

    // 1. Compute costs bottom-up
    let mut costs = HashMap::new();
    costs.insert(bdd.one, 0);
    costs.insert(bdd.zero, usize::MAX);

    // We need to traverse nodes. Since BDDs are DAGs, we can use a recursive helper with memoization
    // or iterate if we have a topological sort. Here we use a simple recursive approach.
    fn compute_cost(bdd: &Bdd, u: Ref, costs: &mut HashMap<Ref, usize>) -> usize {
        if let Some(&c) = costs.get(&u) { return c; }

        let low = bdd.low_node(u);
        let high = bdd.high_node(u);
        let var = bdd.variable(u.index());

        let cost_low = compute_cost(bdd, low, costs).saturating_add(cost(var, 0));
        let cost_high = compute_cost(bdd, high, costs).saturating_add(cost(var, 1));

        let res = min(cost_low, cost_high);
        costs.insert(u, res);
        res
    }

    compute_cost(bdd, root, &mut costs);

    // 2. Construct path top-down
    let mut input = Input::default();
    let mut current = root;

    while !bdd.is_one(current) {
        let low = bdd.low_node(current);
        let high = bdd.high_node(current);
        let var = bdd.variable(current.index());

        let cost_low = costs[&low].saturating_add(cost(var, 0));
        let cost_high = costs[&high].saturating_add(cost(var, 1));

        if cost_low <= cost_high {
            input.set(var, false);
            current = low;
        } else {
            input.set(var, true);
            current = high;
        }
    }
    Some(input)
}
```

=== Trace Slicing

If an input is rejected, the user wants to know *why*.
A trace slice removes all rules that did not contribute to the decision.
If an input was rejected because of its ID, the slice should hide the Value checks.

This requires tracking *provenance* or *dependencies* during the analysis.
We can augment our abstract state to track the set of "active rules".

#example-box(title: "Trace Slicing Example")[
  *Original Policy*:
  + `allow type=A, id=1`
  + `allow type=A, id=2`
  + `deny value in [100, 200]`
  + `allow any`

  *Counterexample*: Input `value=105, id=3`.

  *Full Trace*:
  - Rule 1: No match (id 3 $!=$ 1)
  - Rule 2: No match (id 3 $!=$ 2)
  - Rule 3: Match! Action: Deny.

  *Sliced Trace*:
  - Rule 3: Deny `value=105` (Matches `[100, 200]`)

  Rules 1 and 2 are irrelevant because even if they matched, Rule 3 (being a deny) might still take precedence depending on the chain logic.
  However, in a "First Match" chain, Rules 1 and 2 *are* relevant because they *failed* to match.
  The slice explains: "It didn't match the allow rules, and then it hit this deny rule."
]

#chapter-summary[
  This chapter presented practical techniques for transforming abstract interpretation from theoretical framework to production-grade analysis tool.

  *Reduced products* enable cooperation between complementary domains through systematic information exchange.
  By allowing different abstractions to refine each other, they prove properties that neither domain could establish in isolation, overcoming the limitations of single-domain analysis.

  *State partitioning* addresses precision loss at control flow merge points by maintaining separate abstract states for incompatible execution contexts.
  Distinguishing GET from POST requests or different call sites prevents spurious interactions that generate false positives.

  *Widening with thresholds* reconciles the competing demands of termination and precision for infinite-height domains.
  By extrapolating to domain-specific landmarks like page boundaries rather than infinity, it ensures rapid convergence while respecting meaningful program boundaries.

  Finally, *engineering heuristics* like BDD variable ordering and resource budgets bridge the gap between polynomial theoretical complexity and practical scalability.
  These implementation details often determine whether an analyzer succeeds or fails on real-world programs.
]
