#import "../../theme.typ": *

= The Abstract Program State <ch-combining-domains>

We have the engine (BDDs) and the fuel (Abstract Domains).
Now we build the vehicle.

In this chapter, we define the *Abstract Program State* of our IMP Analyzer.
Instead of a single value for each variable, our state will be a *collection* of possibilities, each guarded by a BDD path condition.

This combination yields *path-sensitive abstract interpretation*.

#info-box(title: "Guide Roadmap")[
  This chapter introduces the *intuition* and *basic architecture* of path sensitivity using a simple example.

  For the rigorous mathematical formalization (Trace Partitioning, Reduced Products) and advanced techniques (Relational Domains), see @part-ii, specifically @ch-domain-combinations.
]

== The Core Idea: Trace Partitioning

Path-insensitive analysis loses precision by merging all paths:

```rust
let mut y = 0;
if x > 0 {
    y = 1;      // y = 1
} else {
    y = 2;      // y = 2
}
// Path-insensitive: y = 1 ⊔ 2 = [1, 2] (or Top)
// We lost the correlation that (x > 0 => y=1) and (x <= 0 => y=2).
```

Path-sensitive analysis maintains separate states:

```rust
// State 1: x > 0, y = 1
// State 2: x <= 0, y = 2
```

But with $n$ conditions, we get $2^n$ explicit states.

*Solution:* Represent path conditions _symbolically_ with BDDs.
We maintain a set of pairs $(b_i, rho_i)$, where $b_i$ is a BDD representing a set of paths (execution traces), and $rho_i$ is the abstract state of the variables on those paths.

This technique is called *Trace Partitioning*.

#figure(
  caption: [Trace Partitioning vs. Naive Merge],
  cetz.canvas({
    import cetz.draw: *

    // --- Styles & Helpers ---
    let style-box = (fill: colors.bg-code, stroke: colors.primary + 1pt, radius: 0.2)
    let style-arrow = (mark: (end: ">"), stroke: colors.text-light + 0.8pt)

    let draw-state(pos, name, body, fill: colors.bg-code, width: 3, height: 1) = {
      let (x, y) = pos
      let w = width / 2
      let h = height / 2
      rect((x - w, y - h), (x + w, y + h), name: name, fill: fill, stroke: colors.primary + 1pt, radius: 0.2)
      content(pos, body)
    }

    let draw-arrow(from, to) = {
      line(from, to, ..style-arrow)
    }

    // --- Layout Constants ---
    let x-left = -4
    let x-right = 4
    let y-start = 5
    let y-branch = 3
    let y-merge = 1
    let dx-branch = 1.5
    let dx-branch-wide = 2.4

    // --- Path Insensitive (Left) ---
    content((x-left, y-start + 1), text(weight: "bold")[Path Insensitive])

    // Initial
    draw-state((x-left, y-start), "l_init", [$top$], width: 2)

    // Branches
    draw-state((x-left - dx-branch, y-branch), "l_b1", [$y=1$], width: 2)
    draw-state((x-left + dx-branch, y-branch), "l_b2", [$y=2$], width: 2)

    // Merge
    draw-state((x-left, y-merge), "l_merge", [$y in {1,2}$], fill: colors.warning.lighten(80%), width: 3)
    content((x-left, y-merge - 1), text(size: 0.8em, fill: colors.error)[Relation Lost!])

    // Edges
    draw-arrow("l_init", "l_b1")
    draw-arrow("l_init", "l_b2")
    draw-arrow("l_b1", "l_merge")
    draw-arrow("l_b2", "l_merge")

    // --- Path Sensitive (Right) ---
    content((x-right, y-start + 1), text(weight: "bold")[Trace Partitioning])

    // Initial
    draw-state((x-right, y-start), "r_init", [${(#true, top)}$], width: 4)

    // Partitions
    draw-state((x-right - dx-branch-wide, y-branch), "r_p1", [${(x > 0, y=1)}$], width: 4.2)
    draw-state((x-right + dx-branch-wide, y-branch), "r_p2", [${(x <= 0, y=2)}$], width: 4.2)

    // Result (No Merge)
    draw-state(
      (x-right, y-merge),
      "r_res",
      [${(x > 0, 1), (x <= 0, 2)}$],
      fill: colors.success.lighten(80%),
      width: 6,
    )
    content((x-right, y-merge - 1), text(size: 0.8em, fill: colors.success)[Relation Preserved!])

    // Edges
    draw-arrow("r_init", "r_p1")
    draw-arrow("r_init", "r_p2")
    // Draw arrows straight down to the result box
    draw-arrow("r_p1", ((), "|-", "r_res.north"))
    draw-arrow("r_p2", ((), "|-", "r_res.north"))
  }),
) <fig:split-merge>

== Architecture

The architecture has three components working together.
+ The *BDD Path Tracker* tracks feasible paths using BDD operations.
+ The *Abstract Environment* tracks variable properties like signs or intervals.
+ The *Combined Domain* pairs the BDD control state with the abstract environment to give us the full picture.

#definition(title: "BDD-based Path-Sensitive Abstract State")[
  A state is a pair $(b, rho)$ where:
  - $b$ is a BDD representing the path condition (which inputs reach here)
  - $rho$ is an abstract environment mapping variables to abstract values

  The state represents: "For inputs satisfying $b$, the variables have values given by $rho$."
]

== Upgrading the AnalysisManager

In @ch-bdd-programming, we built an `AnalysisManager` that maps `Condition` AST nodes to BDD variables.
This structure is perfect for our needs.

We also need to handle *negation* intelligently.
If we have allocated a variable for `x > 0`, and we encounter `x <= 0` (which is `!(x > 0)`), we shouldn't allocate a new variable.
We should just return the *negation* of the existing one.

```rust
impl AnalysisManager {
    pub fn get_bdd(&mut self, c: &Condition) -> Ref {
        // 1. Check exact match
        if let Some(&id) = self.mapping.get(c) {
            return self.bdd.mk_var(id as u32);
        }

        // 2. Check negation (simplified for this guide)
        // In a full implementation, we would check if we have the "opposite" condition.
        // e.g. if c is "x <= 0", check if we have "x > 0" and return !var.

        // 3. Allocate new
        let id = self.next_var_id;
        self.next_var_id += 1;
        self.mapping.insert(c.clone(), id);
        self.bdd.mk_var(id as u32)
    }
}
```

Now, the analysis automatically correlates related branches across the program.
If the program checks `x > 0` twice, the BDD will recognize it's the same condition.

== The Power of Partitioning

Merging all paths into a single abstract environment loses precision.
Instead, we maintain a *partitioned state*: a collection of abstract environments, each guarded by a BDD path condition.

This is often called *Trace Partitioning*.

=== Partitioned State

```rust
#[derive(Clone)]
struct PartitionedState<D: AbstractDomain> {
    // Invariant: Path conditions are disjoint
    partitions: Vec<(Ref, D)>,
    // We use Rc<RefCell> for shared mutable access to the manager
    control: Rc<RefCell<AnalysisManager>>,
}

impl<D: AbstractDomain> PartitionedState<D> {
    fn new(control: Rc<RefCell<AnalysisManager>>) -> Self {
        let bdd = control.borrow().bdd.clone();
        Self {
            partitions: vec![(bdd.mk_true(), D::bottom())], // Start with true path
            control,
        }
    }
}
```

The state is a disjunction: "Either the execution matches $b_1$ with values $rho_1$, OR it matches $b_2$ with values $rho_2$, ...".

=== Smart Joining

When we join two states, we don't blindly merge everything.
We use BDDs to compress the representation.
If two paths lead to the *same* (or similar) data state, we can merge their path conditions!

$ (b_1, rho) ljoin (b_2, rho) = (b_1 or b_2, rho) $

```rust
impl<D: AbstractDomain + PartialEq + Clone> PartitionedState<D> {
    fn join(&self, other: &Self) -> Self {
        let mut new_partitions = self.partitions.clone();
        let bdd = &self.control.borrow().bdd;

        for (path2, env2) in &other.partitions {
            // Try to merge with existing partition
            let mut merged = false;
            for (path1, env1) in &mut new_partitions {
                // Heuristic: If data states are identical, merge the paths.
                // In production, we might also merge "similar" states (e.g., one includes the other)
                // or force a merge if the number of partitions exceeds a limit (k-limiting).
                if env1 == env2 {
                    *path1 = bdd.apply_or(*path1, *path2);
                    merged = true;
                    break;
                }
            }
            if !merged {
                new_partitions.push((*path2, env2.clone()));
            }
        }

        // Optional: Enforce a partition limit to prevent explosion
        if new_partitions.len() > 10 {
            self.force_merge(&mut new_partitions);
        }

        Self {
            partitions: new_partitions,
            control: self.control.clone()
        }
    }
}
```

This approach allows the analysis to distinguish `y = 1` from `y = 2` indefinitely, only merging them if they converge to the same value later.

== Refining Abstract Values

The BDD tells us *which* paths we are on.
We can use this to refine our data knowledge.
When we branch on a condition like `x < 10`, we should update the abstract value of `x` in the true branch!

To decouple the Abstract Domain from the AST, we introduce a `Refineable` trait.

```rust
trait Refineable {
    // Refine the abstract state based on a constraint
    fn refine(&mut self, constraint: &Condition);
}

impl<D: AbstractDomain + Refineable> PartitionedState<D> {
    fn assume(&mut self, c: &Condition) {
        let mut new_partitions = Vec::new();
        let bdd_cond = self.control.borrow_mut().get_bdd(c);
        let bdd = &self.control.borrow().bdd;

        for (path, mut env) in self.partitions.drain(..) {
            // 1. Update Control: Add condition to path
            let new_path = bdd.apply_and(path, bdd_cond);

            if !bdd.is_zero(new_path) {
                // 2. Update Data: Refine environment
                // The domain interprets the constraint to tighten values
                env.refine(c);
                new_partitions.push((new_path, env));
            }
        }
        self.partitions = new_partitions;
    }
}
```

Now, when the analysis sees `if x < 10`, it automatically learns that `x` is small in the true branch, even if the interval domain didn't know it before.

== The Interpreter Loop

Finally, let's see how this fits into the main analysis loop.
The `eval_stmt` function takes a statement and updates the current state.

```rust
fn eval_stmt<D: AbstractDomain>(stmt: &Stmt, state: &mut PartitionedState<D>) {
    match stmt {
        Stmt::Assign(var, expr) => {
            // Update variable state in all partitions
            state.assign(var, expr);
        }
        Stmt::If(cond, then_block, else_block) => {
            // 1. Clone state for branches
            let mut true_state = state.clone();
            let mut false_state = state.clone();

            // 2. Assume conditions
            true_state.assume(cond);
            false_state.assume(&cond.negate());

            // 3. Recurse
            eval_block(then_block, &mut true_state);
            eval_block(else_block, &mut false_state);

            // 4. Join results
            *state = true_state.join(&false_state);
        }
        // ... handle loops ...
    }
}
```

This recursive structure naturally handles nested blocks, while the `PartitionedState` manages the complexity of path conditions under the hood.

== Product Construction Theory <sec-product-theory>

 A combined abstract state carries two kinds of information.
 Control records which execution traces reach the program point.
 Data records abstract values of variables along those traces.
 The pair $(b, rho)$ behaves like a product ordered componentwise.
 Precision improves when constraints flow in both directions.

 #info-box(title: "Where Formal Theory Lives")[
 Formal lattice definitions (standard product, reduced product, multi-domain reduction) live in @ch-advanced-galois.
 This section focuses on *design intuition* only; refer there for proofs and algebraic detail.
]

 - *Control restricts data*: Branch predicate `x > 0` rules out negative interval bounds.
 - *Data refutes control*: Interval $[5,5]$ makes predicate `x < 0` infeasible.
 - *Reduction*: Propagate constraints until no component tightens further.
 - *Contradiction*: Empty path or impossible data collapses state to bottom.
 - *Local fixpoint*: Stabilization after a propagation round means reduction reached equilibrium.

 #insight-box[
 Partitioning and product address different axes.
 Partitioning decides *how many* $(b_i, rho_i)$ pairs we keep.
 Product interaction explains *inside each pair* how control and data cooperate via reduction.
]

=== BDD Control as Product Component

Our BDD path condition acts as one component of a product.
The BDD domain has:

- *Order*: $b_1 lle b_2$ iff $b_1 => b_2$ (logical implication)
- *Join*: $b_1 ljoin b_2 = b_1 or b_2$
- *Meet*: $b_1 lmeet b_2 = b_1 and b_2$
- *Bottom*: False (no paths)
- *Top*: True (all paths)
#definition(title: "BDD Control Lattice")[
  The lattice of BDD formulas $(cal(B), =>, "False", "True", or, and)$ forms a complete boolean algebra.
  Each element represents a set of program execution traces.
]

The combined domain $(cal(B) times D, lle, (F, bot_D), (T, top_D))$ uses standard product ordering.
Reduction propagates constraints: when path condition becomes unsatisfiable, the entire state becomes bottom.

=== Partition Representation

Instead of a single pair $(b, rho)$, we maintain a set ${(b_1, rho_1), ..., (b_n, rho_n)}$ with disjoint path conditions.
This is equivalent to the disjunction:

$ (b_1 and rho_1) or ... or (b_n and rho_n) $

#definition(title: "Partitioned Abstract State")[
  A partitioned state $S = {(b_i, rho_i)}_(i=1)^n$ represents the union of states where execution satisfying $b_i$ has environment $rho_i$.
  The concretization is $gamma(S) = union.big_(i=1)^n gamma(b_i) times gamma(rho_i)$.
]

#theorem(title: "Partition Equivalence")[
  Let $S_1 = {(b_i, rho_i)}$ and $S_2 = {(c_j, sigma_j)}$ be partitioned states.
  $S_1 equiv S_2$ iff $gamma(S_1) = gamma(S_2)$.
]

#proof[
  *Forward direction:* If partitions differ only in syntactic representation (e.g., BDD variable order) but denote the same boolean function and abstract values, concretizations match.

  *Reverse direction:* Two distinct concretizations imply existence of distinguishing concrete state.
]

== Reduction Algorithms <sec-reduction-algorithms>
 BDD tracks control predicates (boolean).
 Relational domain tracks numeric relations.
 Reduction extracts numeric bounds from BDD (when possible) and injects into polyhedron.

Maintaining disjoint partitions with optimal abstraction requires reduction passes.

=== Path Condition Simplification

After operations, path conditions may become redundant or contradictory.
We apply BDD simplification and feasibility checks.

#algorithm(title: "Partition Reduction")[
  *Input:* Partition set ${(b_i, rho_i) | i = 1..n}$.

  *Output:* Reduced partition set.

  + *for each* $(b_i, rho_i)$ *in* partitions *do*
    + *if* $b_i equiv bot$ *then* + *remove* partition $i$ $quad slash.double$ Infeasible guard.
    + *for each* $(b_j, rho_j)$ *where* $j != i$ *do*
      + *if* $rho_i = rho_j$ *then* + *merge* $b_i or b_j$, *remove* $j$ $quad slash.double$ Identical states.
      + *if* $rho_i lle rho_j$ *and* $b_i => b_j$ *then* + *remove* $i$ $quad slash.double$ Subsumed partition.
    + *end for*
  + *end for*
  + *return* reduced partitions
]

Complexity depends on BDD operations and domain equality checks.
Heuristic: limit partition count to bound $k$ (k-limiting) forcing merge when exceeded.

=== Cross Domain Constraints

When BDD path condition encodes arithmetic constraints (e.g., `x > 0` mapped to BDD variable), we can extract these and refine the data domain.

#implementation-box[
  Implement `extract_constraints(b: Ref) -> Vec<Constraint>` parsing BDD structure to recover arithmetic bounds.
  Feed these to domain refinement methods.
  This closes the loop between control and data.
]

=== Partition Explosion Control

Unconstrained partitioning leads to exponential state counts.
Mitigation strategies include:

- *k-Limiting*: Cap partition count at $k$, force merge least similar states when exceeded.
- *Similarity Heuristic*: Measure distance between abstract environments using domain metrics.
- *Lazy Partitioning*: Delay partition splits until domain precision would genuinely improve.

#pitfall-box[
  Aggressive partitioning without limits can exhaust memory quickly.
  Always instrument partition counts and trigger warnings when thresholds approach.
]

#exercise-box(difficulty: "Medium")[
  Implement k-limiting with $k=5$.
  On overflow, merge the two partitions whose abstract environments have smallest lattice height difference.
  Measure precision loss on branching programs.
]

== Concrete Example: Temperature Controller <sec-temperature-example>

Consider an embedded temperature controller with safety bounds:

```rust
fn control_temp(sensor: i32) -> i32 {
  let mut heater_power = 0;
  if sensor < 15 {
    heater_power = 100;  // Full power
  } else if sensor < 20 {
    heater_power = 50;   // Half power
  } else {
    heater_power = 0;    // Off
  }
  heater_power
}
```

*Goal*: Prove `heater_power` is always in $[0, 100]$.

=== Path-Insensitive Interval Analysis

- Initial: `sensor` $= top = (-oo, +oo)$
- After all branches merge: `heater_power` $= [0, 100] ljoin [0, 50] ljoin [0, 0] = [0, 100]$
- Result: Correct but provides no insight into correlations

=== Path-Sensitive BDD Analysis

- Partition 1: $("sensor" < 15, "heater\_power" = 100)$
- Partition 2: $(15 <= "sensor" < 20, "heater\_power" = 50)$
- Partition 3: $("sensor" >= 20, "heater\_power" = 0)$

Each partition maintains exact value correlation with input range.
We can query: "Under what input conditions is heater at full power?"
Answer: BDD for $"sensor" < 15$.

#insight-box[
  Path-sensitivity transforms "what are possible values" into "under which conditions do these values occur".
  This enables conditional verification queries.
]

== Combining Multiple Data Domains <sec-multiple-domains>

Beyond BDD control, we can combine multiple data abstractions in a reduced product.

*Sign × Interval*:
- Signs detect zero division, intervals track bounds.
- Reduction: If sign = Zero, refine interval to $[0, 0]$.
- If interval = $[5, 10]$, refine sign to Positive.

*Interval × Congruence*:
- Intervals for bounds, congruences for divisibility.
- Reduction: Interval $[8, 12]$ with congruence $equiv 0 mod 4$ refines to ${8, 12}$ (only 8 and 12 satisfy both).

*Polyhedra × Interval*:
- Polyhedra capture linear relations, intervals provide quick bounds.
- Reduction: Project polyhedron onto single variable to tighten interval.

#example-reference(
  "domains",
  "combined.rs",
  "combined_domain",
  [Implements a reduced product of sign and interval domains with bidirectional constraint propagation.],
)

#exercise-box(difficulty: "Hard")[
  Design a reduced product of interval and parity (even/odd) domains.
  Implement reduction: interval $[2, 5]$ with parity Even refines to ${2, 4}$.
  Measure overhead versus precision gain.
]

== Relational Domains and BDD Synergy <sec-relational-domains>

Relational domains like octagons or polyhedra track constraints between variables (e.g., $x - y <= 5$).
BDD path-sensitivity adds *conditional* relations: "$x - y <= 5$ holds when $z > 0$".

Combining them requires careful coordination:

+ BDD tracks control predicates (boolean).
+ Relational domain tracks numeric relations.
+ Reduction extracts numeric bounds from BDD (when possible) and injects into polyhedron.

#warning-box[
  Relational domains have cubic complexity in variable count.
  Partition explosion with relational domains can become intractable quickly.
  Consider simpler domains (intervals) for control-heavy code and relational domains for data-heavy loops.
]

#exercise-box(difficulty: "Hard")[
  Sketch integration of octagon domain with BDD control.
  Propose reduction operator extracting difference bounds from path predicates.
  Discuss complexity trade offs.
]


== Research Spotlight: Trace Partitioning vs Powerset <sec-trace-partitioning-spotlight>

Trace partitioning maintains disjoint path sets with separate abstract values.
The *powerset* domain represents arbitrary sets of abstract elements without disjointness.
Trace partitioning is a restricted powerset: partitions correspond to control flow divergence points.

#historical-note(person: "Mauborgne and Rival", year: 2005, title: "Trace Partitioning")[
  Formalized trace partitioning as a systematic framework for path-sensitive analysis distinguishing syntactic control predicates from semantic abstract values.
]

Recent work explores:

- *Dynamic Partitioning*: Adjust partition granularity based on precision needs.
- *Predicate Abstraction*: Choose relevant predicates via counterexample-guided refinement (CEGAR).
- *Hybrid Partitioning*: Combine trace partitioning with relational domains for specific variable clusters.

#exercise-box(difficulty: "Hard")[
  Compare trace partitioning (our approach) with full powerset on a loop with nested conditionals.
  Measure state count, analysis time, and precision (count false alarms).
]


== Implementation Trade-offs <sec-implementation-tradeoffs>

Practical path-sensitive analyzers balance precision with performance.

- *Eager Merge*: Join states at every merge point, losing path-sensitivity early but bounding states.
- *Lazy Merge*: Maintain partitions as long as possible, only merging when forced (loop convergence, state limit).
- *Selective Sensitivity*: Partition only on predicates likely to improve precision (e.g., null checks, array bounds).
- *Predicate Sampling*: Allocate BDD variables for a subset of program conditions, merging others.

#implementation-box[
  Expose a configuration parameter `sensitivity_mode: Enum { Full, Limited(k), Selective }`.
  Profile analysis runs measuring partition counts, memory usage, and precision metrics.
]

#exercise-box(number: 5, difficulty: "Medium")[
  Implement selective sensitivity: partition only on predicates marked `@sensitive` in annotations.
  Compare precision and performance versus full partitioning on annotated programs.
]


== Summary

Combining BDDs with abstract domains gives path-sensitive analysis:
- BDDs track feasible paths compactly
- Abstract domains track variable properties
- States are pairs $(b, rho)$: path condition + variable environment

Operations:
- *Assume:* Split state, update BDD path condition
- *Assign:* Update variable environment, keep path condition
- *Join:* Merge BDDs with OR, join data domains

Trade-offs:
- Early join: loses precision, bounded states
- Late join: maintains precision, risks state explosion
- Heuristics balance precision and performance

Generic design allows any abstract domain with BDD control.

Let's see how these concepts come together in a working path-sensitive analyzer:

#example-reference(
  "integration",
  "sign_with_bdd.rs",
  "sign_with_bdd",
  [
    Complete implementation of path-sensitive analysis combining sign domain with BDD control.
    Shows branching, path feasibility checking, and precision gains over path-insensitive analysis.
  ],
)

#info-box(title: "Combining Multiple Domains")[
  You can also combine multiple *data* domains (not just control+data).
  The reduced product construction maintains relationships between domains.
  See #inline-example("domains", "combined.rs", "combined_domain") for an example combining sign and interval domains.
]


In the next chapter, we build a complete symbolic executor using these techniques.

#chapter-summary[
  - *Combined state: $(b, rho)$ where $b$ is BDD path condition, $rho$ is abstract environment.*
    BDD tracks which paths are feasible, domain tracks variable values.

  - *BDD control domain allocates variables for program conditions.*
    Each boolean condition (e.g., `x > 0`) gets a unique BDD variable.

  - *Branching creates two states with updated path conditions.*
    True branch: $"path" and "cond"$.
    False branch: $"path" and not "cond"$.

  - *Assignment updates data domain, keeps path unchanged.*
    Only variable properties change on assignment, not control flow.

  - *Joining merges paths with OR, joins data with domain operations.*
    Necessary at merge points but loses path-sensitivity.

  - *Trade-off between precision and state explosion.*
    Joining early: fast but imprecise. Joining late: precise but exponential states.

  - *Generic design works with any abstract domain.*
    Swap intervals for signs or constants.
    BDD control layer is orthogonal.

  - *Path-sensitivity alone doesn't guarantee precision.*
    Need sufficiently precise data domains (intervals better than signs).

  - *Main insight:* BDDs provide compact representation of path conditions, enabling path-sensitive abstract interpretation without explicit path enumeration.
]
