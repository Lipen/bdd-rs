#import "../../theme.typ": *

= The Abstract Program State <ch-combining-domains>

We have the engine (BDDs) and the fuel (Abstract Domains).
Now we build the vehicle that brings them together.

This chapter shows how to combine BDDs with abstract domains to track program state.
Instead of storing a single abstract value per variable, we maintain *many* possibilities.
Each possibility is guarded by a BDD representing which execution paths lead to it.

This combination is called *path-sensitive abstract interpretation*.

#info-box(title: "Guide Roadmap")[
  This chapter introduces the *intuition* and *basic architecture* of path sensitivity using a simple example.

  For the rigorous mathematical formalization (Trace Partitioning, Reduced Products) and advanced techniques (Relational Domains), see @part-ii, specifically @ch-domain-combinations.
]

== The Core Idea: Trace Partitioning

When analysis ignores which path was taken, it loses precision.
Consider this simple branch:

```rust
let mut y = 0;
if x > 0 {
    y = 1;      // Path A: x > 0 implies y = 1
} else {
    y = 2;      // Path B: x <= 0 implies y = 2
}
// After merge point:
// Path-insensitive: y = {1} ⊔ {2} = {1, 2}
// Lost information: (x > 0 <=> y = 1) and (x <= 0 <=> y = 2)
```

*What went wrong?*
Path-insensitive analysis merges all incoming states regardless of how they were reached.
The join operation $y = 1 ljoin y = 2$ produces $y in {1, 2}$, forgetting which value corresponds to which input condition.

Path-sensitive analysis maintains separate states:

```rust
// State 1: (path_condition: x > 0,  environment: {y ↦ 1})
// State 2: (path_condition: x <= 0, environment: {y ↦ 2})
```

Now we preserve the correlation: for any concrete input $x$, we can determine the exact value of $y$.

*The scaling problem:* With $n$ independent conditions, explicit enumeration requires $2^n$ states.
A program with 30 boolean variables would need over a billion states.

=== BDD-Based Solution

Use BDDs to represent path conditions *symbolically*.
Instead of enumerating $2^n$ states explicitly, we maintain a set of pairs:

$ S = {(b_1, rho_1), (b_2, rho_2), ..., (b_k, rho_k)} $

where:
- Each $b_i$ is a BDD encoding a *set* of execution traces
- Each $rho_i$ is the abstract environment for variables along those traces
- The BDD operations (AND, OR, NOT) manipulate exponentially many paths in polynomial time

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

Our design has three layers.
+ *BDD Path Tracker*: Uses BDD operations to track which execution paths are feasible.
+ *Abstract Environment*: Maps each variable to an abstract value (sign, interval, etc.).
+ *Combined Domain*: Pairs a BDD path condition with an abstract environment.

#definition(title: "BDD-based Path-Sensitive Abstract State")[
  A state is a pair $(b, rho)$ where:
  - $b$ is a BDD representing the path condition (which inputs reach here)
  - $rho$ is an abstract environment mapping variables to abstract values

  The state represents: "For inputs satisfying $b$, the variables have values given by $rho$."
]

== Upgrading the AnalysisManager

Recall from @ch-bdd-programming that `AnalysisManager` maps program conditions to BDD variables.
We need one enhancement: *smart negation handling*.

=== The Negation Recognition Problem

When we see `x > 0` followed later by `x <= 0`, these are opposite conditions.
Naive allocation would create two independent BDD variables:
- Variable $v_1$ for `x > 0`
- Variable $v_2$ for `x <= 0`

But this misses a crucial optimization: $v_2 equiv not v_1$.
By recognizing this relationship, we:
+ Save BDD variables (halve the variable count for negation pairs)
+ Let BDD operations automatically detect contradictions ($v_1 and not v_1 = F$)
+ Enable path merging when branches rejoin ($v_1 or not v_1 = T$)

=== Enhanced Implementation

We extend the `AnalysisManager` with three key components:

+ *Condition representation*: Capture program predicates in a uniform way
+ *Negation computation*: Detect opposite conditions syntactically
+ *Smart BDD allocation*: Reuse variables for negated predicates

The implementation builds on the basic manager from @ch-bdd-programming, adding negation awareness.

*Condition Enumeration:*

First, define a type for program conditions:

```rust
use std::collections::HashMap;

#[derive(Debug, Clone, Hash, Eq, PartialEq)]
enum Condition {
    Greater(String, i32),    // x > c
    GreaterEq(String, i32),  // x >= c
    Less(String, i32),       // x < c
    LessEq(String, i32),     // x <= c
    Equals(String, i32),     // x == c
    NotEquals(String, i32),  // x != c
}

impl Condition {
    /// Compute the logical negation of this condition
    ///
    /// Returns the opposite predicate such that:
    /// c.negate().negate() == c  (involution)
    /// c AND c.negate() == False (contradiction)
    fn negate(&self) -> Self {
        match self {
            Condition::Greater(var, val) => Condition::LessEq(var.clone(), *val),
            Condition::GreaterEq(var, val) => Condition::Less(var.clone(), *val),
            Condition::Less(var, val) => Condition::GreaterEq(var.clone(), *val),
            Condition::LessEq(var, val) => Condition::Greater(var.clone(), *val),
            Condition::Equals(var, val) => Condition::NotEquals(var.clone(), *val),
            Condition::NotEquals(var, val) => Condition::Equals(var.clone(), *val),
        }
    }
}
```

The `negate` method implements DeMorgan's laws for numeric comparisons.
This is purely syntactic --- no semantic reasoning about variable ranges needed.

*Manager with Negation Cache:*

Now extend `AnalysisManager` to recognize negations:

```rust
struct AnalysisManager {
    bdd: Bdd,
    /// Map: Condition -> BDD variable ID
    mapping: HashMap<Condition, usize>,
    next_var_id: usize,
}

impl AnalysisManager {
    fn new(bdd: Bdd) -> Self {
        Self {
            bdd,
            mapping: HashMap::new(),
            next_var_id: 1,  // BDD variables start at 1
        }
    }

    /// Get or allocate BDD variable for a condition
    ///
    /// Three-step lookup strategy:
    /// 1. Check if condition already has a variable (exact match)
    /// 2. Check if negation has a variable (reuse with NOT)
    /// 3. Allocate new variable (both failed)
    pub fn get_bdd(&mut self, c: &Condition) -> Ref {
        // STEP 1: Check exact match (cache hit)
        if let Some(&id) = self.mapping.get(c) {
            return self.bdd.mk_var(id as u32);
        }

        // STEP 2: Check if we have the negation already
        let neg_c = c.negate();
        if let Some(&id) = self.mapping.get(&neg_c) {
            // Negation exists: return NOT of that variable
            // This ensures: get_bdd(c) == NOT(get_bdd(c.negate()))
            let var = self.bdd.mk_var(id as u32);
            return self.bdd.mk_not(var);
        }

        // STEP 3: Allocate new variable (cache miss for both)
        let id = self.next_var_id;
        self.next_var_id += 1;
        self.mapping.insert(c.clone(), id);
        self.bdd.mk_var(id as u32)
    }
}
```

*Key insight:* Step 2 avoids allocating a new BDD variable when we already have the opposite condition.
This halves the variable space for predicate pairs and enables automatic contradiction detection.

=== Benefits in Action

Consider this program:

```rust
if x > 0 {        // Allocates BDD variable v1
    // ...
}
if x <= 0 {       // Recognizes negation, returns !v1
    // ...
}
```

The BDD for the second branch is automatically $not v_1$.
If both branches are taken (infeasible path), the conjunction becomes:
$ v_1 and not v_1 = F $

The BDD library detects this contradiction immediately, pruning the impossible path.

== The Power of Partitioning

If we merge all paths immediately, we lose the correlation between control flow and data values.
The solution: maintain multiple abstract environments in parallel.
Each environment is guarded by a BDD representing the paths that reach it.
This is *Trace Partitioning*.

=== Partitioned State Representation

The core data structure maintains multiple $("path", "data")$ pairs:

```rust
use std::rc::Rc;
use std::cell::RefCell;

#[derive(Clone)]
struct PartitionedState<D: AbstractDomain> {
    /// List of (path_condition, abstract_environment) pairs
    ///
    /// INVARIANT: Path conditions should be mutually disjoint for efficiency.
    /// That is, for i ≠ j: path_i ∧ path_j = False
    ///
    /// This ensures each concrete execution matches at most one partition.
    partitions: Vec<(Ref, D)>,

    /// Shared reference to BDD manager and condition mapping
    /// Wrapped in Rc<RefCell<>> for shared mutable access across cloned states
    control: Rc<RefCell<AnalysisManager>>,
}

impl<D: AbstractDomain> PartitionedState<D> {
    /// Create initial state: universal path with bottom environment
    fn new(control: Rc<RefCell<AnalysisManager>>) -> Self {
        let bdd = control.borrow().bdd.clone();
        Self {
            // Start with: "all paths are possible, but no variables have been assigned"
            partitions: vec![(bdd.mk_true(), D::bottom())],
            control,
        }
    }
}
```

=== Semantic Interpretation

The partitioned state $S = {(b_1, rho_1), ..., (b_k, rho_k)}$ represents a *disjunction*:

$ S equiv (b_1 and rho_1) or (b_2 and rho_2) or ... or (b_k and rho_k) $

Reading: "Either the execution satisfies path condition $b_1$ with variable environment $rho_1$, OR it satisfies $b_2$ with environment $rho_2$, ..."

*Concrete execution matching:* Given a concrete input $sigma$:
+ Find partition $i$ where $sigma$ satisfies $b_i$ (at most one if disjoint)
+ Check if actual variable values match abstraction $rho_i$

#example-box(title: "State Evolution Example")[
  Consider program:
  ```rust
  let mut y = 0;
  if x > 0 { y = 1; }
  else { y = 2; }
  ```

  State evolution:
  + *Initial:* ${ (T, {y arrow.bar bot}) }$
  + *After `y = 0`:* ${ (T, {y arrow.bar 0}) }$
  + *After split:*
    - True branch: ${ (x > 0, {y arrow.bar 1}) }$
    - False branch: ${ (not (x > 0), {y arrow.bar 2}) }$
  + *After join:* ${ (x > 0, {y arrow.bar 1}), (not (x > 0), {y arrow.bar 2}) }$

  Final state has two partitions preserving exact correlation between $x$ and $y$.
]

=== Smart Joining Strategy

When two control flow paths converge, we must join their states.
Naive approach: create a single partition with joined environments.
Smart approach: preserve distinctions when possible.

*Optimization 1: Environment-Based Merging*

When two partitions have *identical* abstract environments, merge their path conditions:

$ (b_1, rho) ljoin (b_2, rho) = (b_1 or b_2, rho) $

This exploits a key insight: if the data abstraction is the same, we only need to track *which* paths lead here, not maintain separate representations.

#example-box(title: "Merge Opportunity")[
  Two branches assign the same value:
  ```rust
  if x > 0 { y = 5; }      // Partition: (x > 0, {y ↦ [5,5]})
  else { y = 5; }          // Partition: (x <= 0, {y ↦ [5,5]})
  ```

  After join: single partition $(T, {y arrow.bar [5,5]})$ because:
  - Environments are identical: ${y arrow.bar [5,5]}$
  - Path conditions merge: $(x > 0) or (x lt.eq 0) = T$
]

*Full Implementation with Complexity Analysis:*

```rust
impl<D: AbstractDomain + PartialEq + Clone> PartitionedState<D> {
    /// Join two partitioned states at control flow merge points
    ///
    /// Complexity: O(k1 × k2 × (C_eq + C_or))
    /// where k1, k2 are partition counts, C_eq is environment equality cost,
    /// C_or is BDD OR operation cost (usually O(|BDD1| × |BDD2|))
    fn join(&self, other: &Self) -> Self {
        let mut new_partitions = self.partitions.clone();
        let bdd = &self.control.borrow().bdd;

        // For each partition from 'other', try to merge with existing
        for (path2, env2) in &other.partitions {
            let mut merged = false;

            // Scan existing partitions for environment match
            for (path1, env1) in &mut new_partitions {
                if env1 == env2 {  // O(C_eq) - depends on domain
                    // Same data abstraction: merge path conditions
                    *path1 = bdd.apply_or(*path1, *path2);  // O(|path1| × |path2|)
                    merged = true;
                    break;
                }
            }

            if !merged {
                // Different environment: keep as separate partition
                new_partitions.push((*path2, env2.clone()));
            }
        }

        // Optional: Enforce partition count limit
        const MAX_PARTITIONS: usize = 10;
        if new_partitions.len() > MAX_PARTITIONS {
            self.force_merge(&mut new_partitions, MAX_PARTITIONS);
        }

        Self {
            partitions: new_partitions,
            control: self.control.clone()
        }
    }

    /// Force merge partitions when count exceeds limit (k-limiting)
    fn force_merge(&self, partitions: &mut Vec<(Ref, D)>, max_k: usize) {
        while partitions.len() > max_k {
            // Find two "most similar" partitions to merge
            // Heuristic: smallest BDD size product, or smallest lattice distance
            let (i, j) = self.find_best_merge_candidates(partitions);

            let bdd = &self.control.borrow().bdd;
            let (path_i, env_i) = &partitions[i];
            let (path_j, env_j) = &partitions[j];

            // Merge paths with OR, environments with domain join
            let merged_path = bdd.apply_or(*path_i, *path_j);
            let merged_env = env_i.join(env_j);

            partitions[i] = (merged_path, merged_env);
            partitions.swap_remove(j);  // Remove j (order doesn't matter)
        }
    }
}
```

*Why This Matters:*

Without smart joining:
- Every branch doubles partition count
- $n$ branches $arrow.r.double$ $2^n$ partitions
- Memory exhaustion inevitable

With smart joining:
- Partitions merge when data converges
- Common case: $O(k)$ partitions where $k lt.double 2^n$
- $k$-limiting provides hard bound: $k lt.eq K$ for constant $K$

== Refining Abstract Values: Bidirectional Constraint Flow

BDDs track control flow predicates.
Abstract domains track data value properties.
The key insight: these two components can *inform each other*.

=== The Refinement Problem

Consider:
```rust
let mut x = read_input();  // x: [-∞, +∞]
if x < 10 {
    // What do we know about x here?
}
```

After the branch, the BDD path condition records $x < 10$, but the interval domain still has $x in [-oo, +oo]$ unless we explicitly communicate this constraint.

*Solution:* Extract the numeric constraint from the branch condition and use it to *refine* the abstract environment.

=== Generic Refinement Interface

To keep domains independent of program syntax, we define a `Refineable` trait:

```rust
/// Domains that support constraint-based refinement
trait Refineable {
    /// Refine abstract state by assuming a constraint holds
    ///
    /// For interval domain: `x < 10` narrows interval upper bound
    /// For sign domain: `x > 0` restricts to Positive
    fn refine(&mut self, constraint: &Condition);
}

// Example: Interval domain implementation
impl Refineable for IntervalDomain {
    fn refine(&mut self, constraint: &Condition) {
        match constraint {
            Condition::Less(var, value) => {
                // x < value: tighten upper bound
                if let Some(interval) = self.env.get_mut(var) {
                    interval.upper = interval.upper.min(value - 1);
                }
            }
            Condition::Greater(var, value) => {
                // x > value: tighten lower bound
                if let Some(interval) = self.env.get_mut(var) {
                    interval.lower = interval.lower.max(value + 1);
                }
            }
            // ... other constraint types
        }
    }
}
```

=== Assume Operation: Coordinating Both Layers

The `assume` operation updates both control (BDD) and data (domain) components:

```rust
impl<D: AbstractDomain + Refineable> PartitionedState<D> {
    /// Assume a condition holds: update both path and environment
    fn assume(&mut self, c: &Condition) {
        let mut new_partitions = Vec::new();

        // Get BDD representation of condition
        let bdd_cond = self.control.borrow_mut().get_bdd(c);
        let bdd = &self.control.borrow().bdd;

        for (path, mut env) in self.partitions.drain(..) {
            // STEP 1: Update CONTROL layer
            // Add condition to path: path' = path ∧ condition
            let new_path = bdd.apply_and(path, bdd_cond);

            // Check feasibility: if path becomes False, this partition is unreachable
            if !bdd.is_zero(new_path) {
                // STEP 2: Update DATA layer
                // Refine abstract environment using the constraint
                env.refine(c);

                // Keep refined partition
                new_partitions.push((new_path, env));
            } else {
                // Infeasible path: drop this partition
                // (represents unreachable code)
            }
        }

        self.partitions = new_partitions;
    }
}
```

=== Example: Interval Refinement in Action

```rust
// Initial state: {(True, {x ↦ [-∞, +∞]})}
let mut state = PartitionedState::new(control);

// After: if x < 10
state.assume(&Condition::Less("x", 10));
// State: {(x < 10, {x ↦ [-∞, 9]})}
//          ^^^^^^   ^^^^^^^^^^^
//          BDD      Interval refined!

// After: if x > 5 (nested condition)
state.assume(&Condition::Greater("x", 5));
// State: {((x < 10) ∧ (x > 5), {x ↦ [6, 9]})}
//          ^^^^^^^^^^^^^^^^^^   ^^^^^^^^^^
//          BDD tracks both      Interval refined twice!
```

The interval domain automatically tightens bounds based on branch conditions, even though these constraints come from control flow, not assignments.

#insight-box[
  Refinement creates a *feedback loop* between control and data:
  - BDD operations determine path feasibility
  - Constraints extracted from paths refine data abstractions
  - Refined data can rule out additional paths (via reduction, see @sec-reduction-algorithms)
]

== The Interpreter Loop: Putting It All Together

Now we connect everything in the main analysis loop.
The abstract interpreter walks through program statements, maintaining partitioned state.

=== Core Statement Handling

```rust
fn eval_stmt<D: AbstractDomain + Refineable + Clone>(stmt: &Stmt, state: &mut PartitionedState<D>) {
    match stmt {
        Stmt::Assign(var, expr) => {
            // Assignment: update data layer, control unchanged
            // For each partition (b, ρ): keep b, update ρ with new value
            state.assign(var, expr);
        }

        Stmt::If(cond, then_block, else_block) => {
            // Branching: split state, analyze both paths, merge results

            // STEP 1: Clone state for independent analysis
            let mut true_state = state.clone();
            let mut false_state = state.clone();

            // STEP 2: Refine each branch with its condition
            true_state.assume(cond);           // path ∧ cond, refine data
            false_state.assume(&cond.negate()); // path ∧ ¬cond, refine data

            // STEP 3: Analyze each branch independently
            eval_block(then_block, &mut true_state);
            eval_block(else_block, &mut false_state);

            // STEP 4: Join results at merge point
            *state = true_state.join(&false_state);
        }

        Stmt::While(cond, body) => {
            // Loop: iterate until fixpoint (state stops changing)
            eval_loop(cond, body, state);
        }

        Stmt::Assert(cond) => {
            // Assertion: verify condition holds on all paths
            // If any partition violates it, report potential bug
            state.check_assertion(cond);
        }
    }
}

/// Helper: analyze a block (sequence of statements)
fn eval_block<D: AbstractDomain + Refineable + Clone>(block: &[Stmt], state: &mut PartitionedState<D>) {
    for stmt in block {
        eval_stmt(stmt, state);
    }
}
```

=== Loop Handling: Fixpoint Iteration

Loops require special treatment: we iterate until the state stabilizes.

```rust
fn eval_loop<D: AbstractDomain + Refineable + Clone>(
    cond: &Condition,
    body: &[Stmt],
    state: &mut PartitionedState<D>,
) {
    // Save state at loop header
    let mut header_state = state.clone();

    loop {
        // Assume condition holds (enter loop)
        let mut body_state = header_state.clone();
        body_state.assume(cond);

        // Analyze loop body
        eval_block(body, &mut body_state);

        // Join back to header (loop-back edge)
        let new_header = header_state.join(&body_state);

        // Check fixpoint: has state changed?
        if new_header.equivalent_to(&header_state) {
            break;  // Fixpoint reached!
        }

        // State changed: iterate again with wider state
        header_state = new_header;
    }

    // Exit loop: assume condition false
    state.assume(&cond.negate());
}
```

#warning-box[
  Loop analysis can diverge if the abstract domain has infinite chains.
  Use widening (Chapter 10) to force convergence:
  ```rust
  if iteration_count > WIDENING_THRESHOLD {
      new_header = header_state.widen(&body_state);
  }
  ```
]

=== Example: Nested Conditionals

Consider:
```rust
if x > 0 {
    if x > 10 {
        y = 1;
    } else {
        y = 2;
    }
} else {
    y = 3;
}
```

State evolution:
+ *Initial:* ${ (T, bot) }$

+ *Outer split:*
  - True: ${ (x > 0, bot) }$
  - False: ${ (not (x > 0), bot) }$

+ *Inner split (true branch):*
  - True-True: ${ ((x > 0) and (x > 10), {y arrow.bar 1}) }$
  - True-False: ${ ((x > 0) and not (x > 10), {y arrow.bar 2}) }$
  - False: ${ (not (x > 0), {y arrow.bar 3}) }$

+ *After merges:*
  $
    { ((x > 0) and (x > 10), {y arrow.bar 1}),
      ((x > 0) and (x lt.eq 10), {y arrow.bar 2}),
      (x lt.eq 0, {y arrow.bar 3}) }
  $

The recursive structure automatically builds correct BDD formulas for nested branches.

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

BDD path conditions form a lattice.
This lets us treat them as one component of a product domain.

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

A single pair $(b, rho)$ represents one possible program state.
To handle multiple paths, we maintain a set ${(b_1, rho_1), ..., (b_n, rho_n)}$ where the path conditions are disjoint.
This set represents a disjunction:

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

BDDs track control flow (which branches were taken).
Abstract domains track data properties (variable values).
Reduction connects them: extract constraints from one and feed them to the other.

As partitions accumulate, we need cleanup passes to stay efficient.

=== Path Condition Simplification

After several operations, some path conditions become redundant or contradictory.
We apply BDD simplification and check feasibility.

#algorithm(title: "Partition Reduction")[
  *Input:* Partition set ${(b_i, rho_i) | i = 1..n}$.

  *Output:* Reduced partition set.

  + *for each* $(b_i, rho_i)$ *in* partitions *do*
    + *if* $b_i equiv bot$ *then* + *remove* partition $i$ $quad slash.double$ Infeasible guard.
    + *for each* $(b_j, rho_j)$ *where* $j != i$ *do*
      + *if* $rho_i = rho_j$ *then*
        + *merge* $b_i or b_j$, *remove* $j$ $quad slash.double$ Identical states.
      + *if* $rho_i lle rho_j$ *and* $b_i => b_j$ *then*
        + *remove* $i$ $quad slash.double$ Subsumed partition.
  + *return* reduced partitions
]

Complexity depends on BDD operations and abstract domain equality checks.
Practical heuristic: cap partition count at $k$ and force merges when this limit is exceeded ($k$-limiting).

=== Cross Domain Constraints

Sometimes BDD path conditions encode numeric facts.
Example: if we map `x > 0` to a BDD variable, we can extract this constraint and feed it to the interval domain.
This closes the loop between control and data.

#implementation-box[
  Implement `extract_constraints(b: Ref) -> Vec<Constraint>` parsing BDD structure to recover arithmetic bounds.
  Feed these to domain refinement methods.
  This closes the loop between control and data.
]

=== Partition Explosion Control

Without limits, partition counts grow exponentially.
Three common mitigation strategies:

- *$k$-Limiting*: Cap partition count at $k$, force merge least similar states when exceeded.
- *Similarity Heuristic*: Measure distance between abstract environments using domain metrics.
- *Lazy Partitioning*: Delay partition splits until domain precision would genuinely improve.

#pitfall-box[
  Aggressive partitioning without limits can exhaust memory quickly.
  Always instrument partition counts and trigger warnings when thresholds approach.
]

#exercise-box(difficulty: "Medium")[
  Implement $k$-limiting with $k=5$.
  On overflow, merge the two partitions whose abstract environments have smallest lattice height difference.
  Measure precision loss on branching programs.
]

== Concrete Example: Temperature Controller <sec-temperature-example>

Let's analyze a realistic embedded system to see path-sensitivity in action.
Consider a temperature controller with safety-critical bounds:

```rust
fn control_temp(sensor: i32) -> i32 {
    let mut heater_power = 0;
    if sensor < 15 {
        heater_power = 100;  // Full power: cold room
    } else if sensor < 20 {
        heater_power = 50;   // Half power: moderate
    } else {
        heater_power = 0;    // Off: warm enough
    }
    heater_power
}
```

*Safety property*: `heater_power` must always be in $[0, 100]$ (hardware constraint).

=== Path-Insensitive Interval Analysis

Uses a single interval per variable, merging all paths:

*Step-by-step:*
+ Entry: `sensor` $= top$ (unknown), `heater_power` $= bot$

+ After `heater_power = 0`:
  - `heater_power` $= [0, 0]$

+ First branch (`sensor < 15`):
  - True: `heater_power` $= [100, 100]$
  - False: `heater_power` $= [0, 0]$

+ Merge after first `if`:
  - `heater_power` $= [0, 0] ljoin [100, 100] = [0, 100]$

+ Second branch (`sensor < 20` on false path):
  - True: `heater_power` $= [50, 50]$
  - False: `heater_power` $= [0, 0]$

+ Final merge:
  - `heater_power` $= [0, 100] ljoin [50, 50] ljoin [0, 0] = [0, 100]$*Result*: $"heater_power" in [0, 100]$ ✓ (safety property holds)

*Limitation*: Cannot answer:
- "Under what conditions is heater at full power?"
- "Is `heater_power = 75` ever possible?"
- "What sensor range triggers half power?"

=== Path-Sensitive BDD Analysis

Maintains separate partitions for each control flow path:

*Step-by-step:*

+ *Entry:*
  $ { (T, {"heater_power" arrow.bar bot, "sensor" arrow.bar top}) } $

+ *After `heater_power = 0`:*
  $ { (T, {"heater_power" arrow.bar [0,0], "sensor" arrow.bar top}) } $

+ *First split (`sensor < 15`):*
  - *True partition:*
    $ ("sensor" < 15, {"heater_power" arrow.bar [100,100], "sensor" arrow.bar [-oo, 14]}) $
  - *False partition:*
    $ (not ("sensor" < 15), {"heater_power" arrow.bar [0,0], "sensor" arrow.bar [15, +oo]}) $

+ *Second split on false partition (`sensor < 20`):*
  - *True partition (from false):*
    $ ((not (s < 15)) and (s < 20), {"heater_power" arrow.bar [50,50], s arrow.bar [15,19]}) $
  - *False partition (from false):*
    $ ((not (s < 15)) and not (s < 20), {"heater_power" arrow.bar [0,0], s arrow.bar [20, +oo]}) $

+ *Final state (three partitions):*$ S = { & ("sensor" < 15, {"hp" arrow.bar 100, "sensor" arrow.bar [-oo, 14]}), \
        & (("sensor" gt.eq 15) and ("sensor" < 20), {"hp" arrow.bar 50, "sensor" arrow.bar [15, 19]}), \
        & ("sensor" gt.eq 20, {"hp" arrow.bar 0, "sensor" arrow.bar [20, +oo]}) } $

*Verification:* Check each partition's `heater_power` value:
- Partition 1: $100 in [0, 100]$ ✓
- Partition 2: $50 in [0, 100]$ ✓
- Partition 3: $0 in [0, 100]$ ✓

Property holds on all paths!

=== Advanced Queries Enabled by Path-Sensitivity

*Query 1:* "When is heater at full power?"
```rust
// Find partitions where heater_power = 100
let full_power_condition = find_partition_bdd(|env| env["heater_power"] == 100);
// Answer: sensor < 15
```

*Query 2:* "Is `heater_power = 75` possible?"
```rust
// Check if any partition allows heater_power = 75
let is_possible = partitions.iter().any(|(_, env)| env["heater_power"].contains(75));
// Answer: No (only 0, 50, 100 are possible)
```

*Query 3:* "What sensor values cause half power?"
```rust
// Extract interval from partition where heater_power = 50
let half_power_range = find_partition_data(|env| env["heater_power"] == 50, "sensor");
// Answer: sensor ∈ [15, 19]
```

#insight-box[
  Path-sensitivity transforms static analysis from "what values are possible" into "under which conditions do these values occur".
  This enables:
  - *Conditional verification*: properties that depend on input constraints
  - *Root cause analysis*: tracing bugs back to specific input conditions
  - *Test generation*: extracting concrete inputs that trigger each path
]

== Combining Multiple Data Domains <sec-multiple-domains>

Beyond pairing BDDs with one abstract domain, we can combine *multiple* data abstractions.
Each domain contributes different information.
Reduction lets them refine each other.

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

Relational domains (octagons, polyhedra) track relationships between variables, like $x - y <= 5$.
Combining them with BDDs enables *conditional* relations: "$x - y <= 5$ when $z > 0$".

This requires careful design:

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

Trace partitioning maintains disjoint path sets, each with its own abstract value.
The *powerset* domain allows arbitrary sets of abstract elements without disjointness constraints.
Trace partitioning is a restricted powerset where partitions align with control flow splits.

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

Real path-sensitive analyzers balance precision against performance.
Four common strategies:

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

Path-sensitive analysis combines BDDs with abstract domains:
- BDDs represent sets of execution paths compactly
- Abstract domains track variable properties
- States are pairs $(b, rho)$: path condition + abstract environment

Key operations:
- *Assume*: Strengthen BDD path condition when branching
- *Assign*: Update abstract environment, keep path condition unchanged
- *Join*: Merge BDD conditions with OR, join abstract values with domain operations

Trade-offs:
- Join early: fast but loses precision
- Join late: precise but risks exponential blowup
- Use heuristics ($k$-limiting, similarity metrics) to balance both

The design is generic: swap any abstract domain into the framework.
BDD control layer works independently of data domain choice.

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
