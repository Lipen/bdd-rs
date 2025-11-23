#import "../../theme.typ": *

= The Abstract Program State <ch-combining-domains>

We have the engine (BDDs) and the fuel (Abstract Domains).
Now we build the vehicle that brings them together.

This chapter shows how to combine BDDs with abstract domains to track program state.
Instead of storing a single abstract value per variable, we maintain *many* possibilities.
Each possibility is guarded by a BDD representing which execution paths lead to it.

This combination is called *path-sensitive abstract interpretation*.

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

The problem is that path-insensitive analysis merges all incoming states regardless of how they were reached.
The join operation $y = 1 ljoin y = 2$ produces $y in {1, 2}$, forgetting which value corresponds to which input condition.
We lost the correlation between the condition and the value.

Path-sensitive analysis maintains separate states:

```rust
// State 1: (path_condition: x > 0,  environment: {y ↦ 1})
// State 2: (path_condition: x <= 0, environment: {y ↦ 2})
```

Now we preserve the correlation: for any concrete input $x$, we can determine the exact value of $y$.

However, maintaining separate states for each path faces a scaling challenge.
With $n$ independent conditions, explicit enumeration requires $2^n$ states.
A program with 30 boolean variables would need over a billion states, making explicit enumeration impractical.

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

Our design has three layers:
+ *BDD Path Tracker*: Uses BDD operations to track which execution paths are feasible.
+ *Abstract Environment*: Maps each variable to an abstract value (sign, interval, etc.).
+ *Combined State*: Pairs a BDD path condition with an abstract environment.

#definition(title: "BDD-based Path-Sensitive Abstract State")[
  A state is a pair $(b, rho)$ where:
  - $b$ is a BDD representing the path condition (which inputs reach here)
  - $rho$ is an abstract environment mapping variables to abstract values

  The state represents: "For inputs satisfying $b$, the variables have values given by $rho$."
]

== Implementation: PathSensitiveState

Here's the complete structure:

```rust
use std::collections::HashMap;
use std::rc::Rc;
use bdd_rs::bdd::Bdd;
use bdd_rs::reference::Ref;

struct PathSensitiveState {
    bdd: Rc<Bdd>,
    path: Ref,                  // BDD representing path condition
    env: HashMap<String, Sign>, // Variable → Sign mapping
    next_var: u32,              // Next BDD variable to allocate
}
```

Each state tracks:
+ `path`: BDD formula describing which paths reach this state
+ `env`: Abstract environment mapping variables to values
+ `next_var`: Counter for fresh BDD variable allocation

=== Core Operations

Creating initial state:

```rust
impl PathSensitiveState {
    fn new(bdd: Rc<Bdd>) -> Self {
        Self {
            bdd: bdd.clone(),
            path: bdd.mk_true(), // Initially: all paths feasible
            env: HashMap::new(),
            next_var: 1,
        }
    }
}
```

Checking feasibility:

```rust
fn is_feasible(&self) -> bool {
    !self.bdd.is_zero(self.path)
}
```

When a path's BDD becomes False, that path is impossible.

=== Branching: Splitting Paths

At a branch point, we create two states with refined path conditions:

```rust
fn branch(&self) -> (Self, Self) {
    // Allocate fresh BDD variable for this condition
    let cond_var = self.next_var;
    let cond_bdd = self.bdd.mk_var(cond_var);

    // True branch: path ∧ condition
    let true_path = self.bdd.apply_and(self.path, cond_bdd);

    // False branch: path ∧ ¬condition
    let not_cond = self.bdd.apply_not(cond_bdd);
    let false_path = self.bdd.apply_and(self.path, not_cond);

    // Return both states (details omitted)
    (true_state, false_state)
}
```

Each branch gets a copy of the environment with a refined path condition.

Example usage:

```rust
let (mut true_state, mut false_state) = state.branch();

// True branch: x = 5
true_state.assign("x", Sign::Pos);

// False branch: x = -3
false_state.assign("x", Sign::Neg);
```

=== Joining: Merging Paths

When paths reconverge, we join them:

```rust
fn join(&self, other: &Self) -> Self {
    // Merge path conditions: path₁ ∨ path₂
    let merged_path = self.bdd.apply_or(self.path, other.path);

    // Join data environments
    let mut merged_env = HashMap::new();
    for var in all_variables {
        let val1 = self.get(var);
        let val2 = other.get(var);
        merged_env.insert(var, val1.join(&val2));
    }
    // ... return merged state
}
```

The join operation combines path conditions with OR and abstract values with domain join ($ljoin$).

== Advanced: Condition Management

Production analyzers optimize BDD variable allocation by recognizing negated predicates.

=== Condition Representation

Define an enum for program predicates:

```rust
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

=== Negation-Aware BDD Allocation

The `AnalysisManager` caches conditions and reuses BDD variables for negations:

```rust
struct AnalysisManager {
    bdd: Bdd,
    mapping: HashMap<Condition, usize>,  // Condition -> BDD variable ID
    next_var_id: usize,
}

impl AnalysisManager {
    pub fn get_bdd(&mut self, c: &Condition) -> Ref {
        // 1. Check if condition already has a variable
        if let Some(&id) = self.mapping.get(c) {
            return self.bdd.mk_var(id as u32);
        }

        // 2. Check if negation has a variable (reuse with NOT)
        let neg_c = c.negate();
        if let Some(&id) = self.mapping.get(&neg_c) {
            let var = self.bdd.mk_var(id as u32);
            return self.bdd.mk_not(var);
        }

        // 3. Allocate new variable
        let id = self.next_var_id;
        self.next_var_id += 1;
        self.mapping.insert(c.clone(), id);
        self.bdd.mk_var(id as u32)
    }
}
```

Step 2 halves variable usage for predicate pairs like `x > 0` and `x <= 0`.

=== Automatic Contradiction Detection

Consider sequential branches:

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

== Alternative Design: Partitioning

The `PathSensitiveState` shown earlier clones states at each branch.
An alternative design maintains *all* path-environment pairs in a single structure.
This section sketches this approach to illustrate the design space.

Instead of cloning, we store multiple $"path", "data"$ pairs in one container.
Each pair represents a partition of the program's execution space.

=== Partitioned State Representation

The core data structure:

```rust
struct PartitionedState<D: AbstractDomain> {
    partitions: Vec<(Ref, D)>,  // List of (path, environment) pairs
    control: Rc<RefCell<AnalysisManager>>,
}
```

Invariant: path conditions should be mutually disjoint.
That is, for $i eq.not j$: $"path"_i and "path"_j = F$.

=== Semantic Interpretation

The partitioned state $S = {(b_1, rho_1), ..., (b_k, rho_k)}$ represents a *disjunction*:

$ S equiv (b_1 and rho_1) or (b_2 and rho_2) or ... or (b_k and rho_k) $

Reading: "Either the execution satisfies path condition $b_1$ with variable environment $rho_1$, OR it satisfies $b_2$ with environment $rho_2$, ..."

=== Matching Concrete Executions

Given a concrete input $sigma$, we can determine which partition corresponds to that execution:

+ Search for partition $i$ where the concrete input $sigma$ satisfies the BDD condition $b_i$.
  Since partitions are disjoint, at most one will match.
+ Once found, check whether the actual variable values match the abstract environment $rho_i$.

This allows us to verify that our abstract analysis correctly covers all concrete behaviors.

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

When two partitions have *identical* abstract environments, merge their path conditions:

$ (b_1, rho) ljoin (b_2, rho) = (b_1 or b_2, rho) $

#example-box(title: "Merge Opportunity")[
  Two branches assign the same value:
  ```rust
  if x > 0 { y = 5; }      // Partition: (x > 0, {y ↦ [5,5]})
  else { y = 5; }          // Partition: (x <= 0, {y ↦ [5,5]})
  ```

  After join: single partition $(T, {y arrow.bar [5,5]})$ because environments are identical.
]

Join algorithm:
```rust
fn join(&self, other: &Self) -> Self {
    let mut result = self.partitions.clone();

    for (path2, env2) in &other.partitions {
        // Try to find matching environment
        if let Some((path1, _)) = result.iter_mut().find(|(_, e)| e == env2) {
            *path1 = bdd.apply_or(*path1, *path2);  // Merge paths
        } else {
            result.push((*path2, env2.clone()));     // Add new partition
        }
    }
    // ...
}
```

Without smart joining: $n$ branches $arrow.r.double$ $2^n$ partitions.
With smart joining: common case $O(k)$ partitions where $k lt.double 2^n$.

== Refining Abstract Values: Bidirectional Flow

BDDs track control flow predicates.
Abstract domains track data value properties.
Key insight: these two components can *inform each other*.

=== The Refinement Problem

Consider:
```rust
let mut x = read_input();  // x: [-∞, +∞]
if x < 10 {
    // What do we know about x here?
}
```

After the branch, the BDD path condition records $x < 10$, but the interval domain still has $x in [-oo, +oo]$ unless we explicitly communicate this constraint.

To solve this, we extract the numeric constraint from the branch condition and use it to *refine* the abstract environment.
This ensures both components stay synchronized.

=== Generic Refinement Interface

Define a trait for domains that support constraint-based refinement:

```rust
trait Refineable {
    fn refine(&mut self, constraint: &Condition);
}

impl Refineable for IntervalDomain {
    fn refine(&mut self, constraint: &Condition) {
        match constraint {
            Condition::Less(var, val) => /* tighten upper bound */,
            Condition::Greater(var, val) => /* tighten lower bound */,
            // ...
        }
    }
}
```

=== Assume Operation: Coordinating Both Layers

The `assume` operation updates both control (BDD) and data (domain) components:

```rust
fn assume(&mut self, c: &Condition) {
    let bdd_cond = self.control.get_bdd(c);

    for (path, env) in &mut self.partitions {
        *path = bdd.apply_and(*path, bdd_cond);  // Update control
        env.refine(c);                            // Update data
    }

    // Remove infeasible partitions (path = False)
    self.partitions.retain(|(p, _)| !bdd.is_zero(*p));
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
  - Refined data can rule out additional paths
]

== Putting It Together: The Interpreter Loop

Now that we have all the pieces --- branching, joining, refinement --- let's see how they fit together.
The abstract interpreter walks through program statements, applying these operations:

```rust
fn eval_stmt(stmt: &Stmt, state: &mut State) {
    match stmt {
        Stmt::Assign(var, expr) => {
            state.assign(var, expr);
        }
        Stmt::If(cond, then_block, else_block) => {
            let mut true_state = state.clone();
            let mut false_state = state.clone();

            true_state.assume(cond);
            false_state.assume(&cond.negate());

            eval_block(then_block, &mut true_state);
            eval_block(else_block, &mut false_state);

            *state = true_state.join(&false_state);
        }
        Stmt::While(cond, body) => {
            // Fixpoint iteration (see Chapter 10)
        }
    }
}
```

The interpreter handles three types of statements, each with different effects on state:

*Assignment statements:*
Update the variable environment with new values.
The path condition remains unchanged since assignments don't affect control flow.

*Branch statements:*
Split the state into two copies, one for each branch direction.
Refine both path conditions and environments using the `assume` operation.
After analyzing both branches, join the results back together.

*Loop statements:*
Require fixpoint iteration to handle potential unbounded execution.
Chapter 10 covers the widening operators needed to ensure termination.

== Understanding the Product: How BDDs and Domains Cooperate

Let's step back and understand the fundamental mechanism at work.
The key insight: BDDs and abstract domains form a *feedback loop*.

Each state $(b, rho)$ combines:
- $b$: BDD tracking which paths are feasible
- $rho$: abstract environment with variable values

These two components inform each other.
This is an instance of *product domain* construction (see formal definition in @ch-domain-combinations).

=== Control Flow Refines Data Values

When we take a branch, the control flow condition provides information about variable values.
Consider:

```rust
if x > 0 {
    // BDD records: path ∧ (x > 0)
    // Domain refines: x ∈ [1, +∞]
}
```

The branch condition `x > 0` not only updates the BDD path condition, but also allows the interval domain to tighten its bounds.
Inside the branch, we know $x > 0$, so the interval can be refined from $[-oo, +oo]$ to $[1, +oo]$.

=== Data Values Eliminate Infeasible Paths

Conversely, when the abstract domain has precise information, it can prove that certain paths are impossible.
Consider:

```rust
x = 5;              // Domain: x ∈ [5, 5]
if x < 0 {          // BDD would add: path ∧ (x < 0)
    // Unreachable!  // But [5,5] ∩ (-∞,0) = ∅
}                    // Drop this partition
```

Here, the interval domain knows $x in [5, 5]$.
When we encounter the condition `x < 0`, the intersection $[5,5] inter (-oo, 0) = emptyset$ is empty.
This proves the path is infeasible, so we can drop this partition entirely.

This bidirectional refinement is called *reduction*.
The process continues until neither component can tighten further.
For formal reduction operators with soundness proofs, see @ch-domain-combinations.

#insight-box[
  Constraints flow between domains until stabilization.
  When neither the BDD control layer nor the data domain can further refine the other, the system has reached a stable reduced state.
]

== Managing Partition Growth

As programs execute, partitions multiply.
Without management, memory exhausts quickly.
We need strategies to keep the number of partitions under control while preserving as much precision as possible.

=== Strategy 1: Remove Infeasible Partitions

The simplest strategy is to remove partitions whose BDD becomes False.
These represent impossible execution paths and contribute nothing to the analysis.

```rust
partitions.retain(|(path, _)| !bdd.is_zero(*path));
```

This is essentially free --- we're discarding partitions that are already proven unreachable.

=== Strategy 2: Merge Partitions with Identical Environments

When two partitions have the same abstract values for all variables, we can merge their path conditions.
For example:

```rust
// (x > 0, {y ↦ 5}) and (x < 10, {y ↦ 5})
// → ((x > 0) ∨ (x < 10), {y ↦ 5})
```

This reduces the number of partitions without losing precision, since the abstract environments are identical.

=== Strategy 3: Cap Partition Count (k-limiting)

When all else fails, we can impose a hard limit on the number of partitions.
For example, set a maximum of $k = 10$ partitions.

```rust
const MAX_PARTITIONS: usize = 10;
if partitions.len() > MAX_PARTITIONS {
    merge_most_similar(&mut partitions);
}
```

When this limit is exceeded, we force-merge the most similar partitions (those with closest abstract values).
This trades precision for performance, but ensures the analysis remains tractable.

With these management strategies in place, let's see path-sensitive analysis in action.

== Complete Example: Temperature Controller Analysis

Let's apply everything we've learned to a realistic embedded system.
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

Uses a single interval per variable, merging all paths.

Analysis trace:
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
  - `heater_power` $= [0, 100] ljoin [50, 50] ljoin [0, 0] = [0, 100]$

The analysis concludes that $"heater_power" in [0, 100]$, so the safety property holds.

However, this path-insensitive analysis has lost significant information.
It cannot answer important questions:
- "Under what conditions is heater at full power?"
- "Is `heater_power = 75` ever possible?"
- "What sensor range triggers half power?"

Path-sensitivity will let us answer these questions precisely.

=== Path-Sensitive BDD Analysis

Maintains separate partitions for each control flow path.

Analysis trace:

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

Now we can verify the safety property on each partition separately:
- Partition 1: $100 in [0, 100]$ ✓
- Partition 2: $50 in [0, 100]$ ✓
- Partition 3: $0 in [0, 100]$ ✓

The property holds on all paths, confirming the system is safe.

=== Advanced Queries Enabled by Path-Sensitivity

Path-sensitivity enables queries about the relationship between inputs and outputs:

- "When is heater at full power?" → `sensor < 15`
- "Is `heater_power = 75` possible?" → No (only 0, 50, 100)
- "What sensor values cause half power?" → `sensor` $in$ [15, 19]

This transforms analysis from "what values are possible" into "under which conditions do these values occur".

== Beyond Single Domains: Combining Multiple Abstractions <sec-multiple-domains>

So far we've paired BDDs with a single abstract domain (sign, interval, etc.).
But we can go further: combine *multiple* data abstractions simultaneously.
Each domain contributes different information, and reduction lets them refine each other.
See #inline-example("domains", "combined.rs", "combined") for runnable examples.

=== Sign × Interval Product

The sign domain detects zero division and distinguishes `Pos` from `Neg` values.
The interval domain tracks numeric bounds.
Together, they can refine each other:

- If the sign domain determines a value is `Zero`, the interval domain can refine its bounds to $[0, 0]$.
- Conversely, if the interval domain has bounds $[5, 10]$, the sign domain can refine its value to `Pos`.

=== Interval × Congruence Product

Intervals provide bounds, while congruences track divisibility properties (e.g., `Even` or "divisible by 4").
When combined, they can significantly reduce the set of possible values:

- Interval $[8, 12]$ with congruence $equiv 0 mod 4$ refines to ${8, 12}$.
  Only 8 and 12 in this range satisfy the divisibility constraint.

=== Polyhedra × Interval Product

Polyhedra capture linear relations between variables (e.g., $x - y <= 5$).
Intervals provide quick bounds for individual variables.
Reduction works by projecting the polyhedron:

- Project the polyhedron onto a single variable to extract tighter bounds.
- Use interval bounds to simplify polyhedron constraints.

#example-reference(
  "domains",
  "combined.rs",
  "combined_domain",
  [Implements a reduced product of sign and parity domains, demonstrating how reduction eliminates impossible combinations like $("Zero", "Odd")$.],
)

#exercise-box(difficulty: "Hard")[
  Design a reduced product of interval and parity (`Even`/`Odd`) domains.
  Implement reduction: interval $[2, 5]$ with parity `Even` refines to ${2, 4}$.
  Measure overhead versus precision gain.
]

== Relational Domains and BDD Synergy <sec-relational-domains>

#warning-box[
  *Advanced Content*: Relational domains are covered in detail in Part II, Chapter 14.
  This section is optional for introductory readers.
]

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


== Research Spotlight: Trace Partitioning in Context <sec-trace-partitioning-spotlight>

#info-box(title: "Research Context")[
  This section discusses the theoretical foundations and research literature.
  Useful for readers interested in the formal underpinnings, but not essential for practical implementation.
]

The trace partitioning approach we've used throughout this chapter has deep theoretical roots.
Trace partitioning maintains disjoint path sets, each with its own abstract value.
The *powerset* domain allows arbitrary sets of abstract elements without disjointness constraints.
Trace partitioning is a restricted powerset where partitions align with control flow splits.

#historical-note(person: "Mauborgne and Rival", year: 2005, title: "Trace Partitioning")[
  Formalized trace partitioning as a systematic framework for path-sensitive analysis distinguishing syntactic control predicates from semantic abstract values.
]

Recent work explores several promising directions:

*Dynamic partitioning:*
Adjust partition granularity dynamically based on precision needs.
Maintain fine-grained partitions where precision matters, coarser partitions elsewhere.

*Predicate abstraction:*
Automatically choose relevant predicates to track using counterexample-guided refinement (CEGAR).
Start with coarse abstraction and refine only when necessary to eliminate false alarms.

*Hybrid partitioning:*
Combine trace partitioning with relational domains for specific variable clusters.
Use path-sensitivity for control-heavy code, relational domains for data-intensive loops.

#exercise-box(difficulty: "Hard")[
  Compare trace partitioning (our approach) with full powerset on a loop with nested conditionals.
  Measure state count, analysis time, and precision (count false alarms).
]


== Engineering Perspective: Implementation Trade-offs <sec-implementation-tradeoffs>

#info-box(title: "Engineering Considerations")[
  This section discusses practical engineering trade-offs in production analyzers.
  Part III (Performance and Optimization) covers these topics in depth with benchmarks.
]

We've focused on correctness and precision, but production analyzers must also consider performance.
Path-sensitive analysis can be expensive, so real systems balance precision against speed.

=== Eager Merge Strategy

Join states at every merge point in the control flow graph.
This loses path-sensitivity early but bounds the number of states.
Suitable for programs where path-sensitivity provides little benefit.

=== Lazy Merge Strategy

Maintain partitions as long as possible, only merging when absolutely necessary.
Merging is forced at loop convergence points or when hitting state limits.
Provides maximum precision at the cost of potentially exponential state growth.

=== Selective Sensitivity Strategy

Partition only on predicates likely to improve precision.
For example, track null checks and array bounds precisely, but merge on other conditions.
Requires heuristics or annotations to identify important predicates.

=== Predicate Sampling Strategy

Allocate BDD variables for only a subset of program conditions.
Other conditions are handled by merging their states.
Balances precision and performance by focusing resources on critical predicates.

#implementation-box[
  Expose a configuration parameter `sensitivity_mode: Enum { Full, Limited(k), Selective }`.
  Profile analysis runs measuring partition counts, memory usage, and precision metrics.
]

#exercise-box(number: 5, difficulty: "Medium")[
  Implement selective sensitivity: partition only on predicates marked `@sensitive` in annotations.
  Compare precision and performance versus full partitioning on annotated programs.
]


== Summary

Path-sensitive analysis combines BDDs with abstract domains to track precise program state.

Core concepts:
- States are pairs $(b, rho)$: BDD path condition + abstract environment
- BDDs compactly represent exponentially many paths
- Abstract domains track variable properties on each path

Key operations:

*Branching splits states:*
Create two refined path conditions: $"path" and "cond"$ for true branch, $"path" and not "cond"$ for false branch.
Each branch gets its own copy of the environment to track independently.

*Assignment updates values:*
Modify the variable environment with new abstract values.
The path condition stays the same since assignments don't create new paths.

*Joining merges paths:*
Combine path conditions with logical OR.
Join data environments using the domain's join operation ($ljoin$).

*Feasibility checking prunes paths:*
When a BDD becomes False, that path is impossible and can be discarded immediately.

Implementation patterns:
```rust
// Basic: PathSensitiveState (code-examples/integration/sign_with_bdd.rs)
struct PathSensitiveState {
    path: Ref,                  // BDD path condition
    env: HashMap<String, Sign>, // Variable → abstract value
}

// Advanced: PartitionedState (production)
struct PartitionedState {
    partitions: Vec<(Ref, Domain)>, // Multiple (path, env) pairs
}
```

Trade-offs:
- Join early: fast, loses precision
- Join late: precise, exponential blowup
- $k$-limiting: cap partitions, balance both

#example-reference(
  "integration",
  "sign_with_bdd.rs",
  "sign_with_bdd",
  [Complete working implementation of basic path-sensitive analysis.],
)

In the next chapter, we build a symbolic executor using these techniques.

#chapter-summary[
  This chapter synthesized control flow and data abstraction into a unified path-sensitive analysis framework.

  The key architectural insight is *layered state representation*: $(b, rho)$ pairs a BDD tracking feasible execution paths with an abstract domain tracking variable values.
  This separation enables *orthogonal composition* --- the BDD layer handles control flow sensitivity independently of the chosen data abstraction (signs, intervals, polyhedra, etc.).

  *Path condition refinement* occurs automatically at branches.
  The true branch conjoins the condition to the path BDD ($"path" and "cond"$), while the false branch conjoins its negation.
  When a path BDD becomes False, that execution path has been proven infeasible through contradiction, enabling *automatic infeasible path pruning*.

  This architecture *represents $2^n$ paths symbolically* while performing operations in polynomial time.
  Rather than explicitly enumerating execution paths, Boolean operations on BDDs manipulate entire path families implicitly.

  The *control-data cooperation* reveals its power when path conditions constrain data domains.
  If a path BDD encodes $x = 5$, the data domain can strengthen its approximation accordingly, recovering precision lost to path-insensitive merging.

  This framework's *genericity* enables experimenting with different partitioning strategies, trading between path sensitivity (precision) and state space size (performance).
]
