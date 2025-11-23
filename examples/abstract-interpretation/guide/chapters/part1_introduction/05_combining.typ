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

== Concrete Example: Temperature Controller <sec-temperature-example>

Let's analyze a realistic embedded system:

```rust
fn control_temp(sensor: i32) -> i32 {
    let mut heater_power = 0;
    if sensor < 15 {
        heater_power = 100;  // Full power when cold
    } else if sensor < 20 {
        heater_power = 50;   // Half power
    }
    heater_power
}
```

Safety property: `heater_power` $in [0, 100]$ (hardware constraint).

=== Path-Insensitive Interval Analysis

Using a single interval per variable merges all paths:

+ Entry: `sensor` $= top$, `heater_power` $= bot$
+ After `heater_power = 0`: `heater_power` $= [0, 0]$
+ First branch (`sensor < 15`):
  - True: `heater_power` $= [100, 100]$
  - False: `heater_power` $= [0, 0]$
+ Merge: `heater_power` $= [0, 100]$
+ Second branch (`sensor < 20`):
  - True: `heater_power` $= [50, 50]$
  - False: unchanged
+ Final: `heater_power` $= [0, 100]$ ✓

Property holds, but precision is lost. Cannot answer "when is heater at full power?"

=== Path-Sensitive BDD Analysis

Maintains separate states for each path. Using `PathSensitiveState`:

```rust
let bdd = Rc::new(Bdd::default());
let mut state = PathSensitiveState::new(bdd.clone());

// heater_power = 0
state.env.insert("heater_power", Interval::constant(0));

// First branch: sensor < 15
let (mut branch1, mut state) = state.branch();
branch1.env.insert("heater_power", Interval::constant(100));

// Second branch: sensor < 20
let (mut branch2, mut branch3) = state.branch();
branch2.env.insert("heater_power", Interval::constant(50));

// Final: three states
// State 1: (v₁, {heater_power ↦ [100, 100]})        -- sensor < 15
// State 2: (¬v₁ ∧ v₂, {heater_power ↦ [50, 50]})    -- 15 ≤ sensor < 20
// State 3: (¬v₁ ∧ ¬v₂, {heater_power ↦ [0, 0]})     -- sensor ≥ 20
```

Each partition preserves exact correlation between sensor reading and heater power:
- $100 in [0, 100]$ #YES
- $50 in [0, 100]$ #YES
- $0 in [0, 100]$ #YES

Path-sensitivity enables queries:
- "When is heater at full power?" $=>$ `sensor < 15`
- "Is heater_power = 75 possible?" $=>$ No
- "What triggers half power?" $=>$ `15 ≤ sensor < 20`

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

*Solution:* Extract the numeric constraint from the branch condition and use it to *refine* the abstract environment.

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

== The Interpreter Loop

The abstract interpreter walks through program statements:

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

Key operations:
- *Assignment*: update environment, preserve path
- *Branch*: split state, refine both branches, join results
- *Loop*: iterate until fixpoint with widening

== How BDDs and Domains Cooperate

The key insight: BDDs and abstract domains form a *feedback loop*.

Each state $(b, rho)$ combines:
- $b$: BDD tracking which paths are feasible
- $rho$: abstract environment with variable values

These two components inform each other.
This is an instance of *product domain* construction (formal definition in @ch-advanced-galois).

*Control constrains data:*
```rust
if x > 0 {
    // BDD records: path ∧ (x > 0)
    // Domain refines: x ∈ [1, +∞]
}
```
The branch condition tightens the interval for `x`.

*Data prunes paths:*
```rust
x = 5;              // Domain: x ∈ [5, 5]
if x < 0 {          // BDD would add: path ∧ (x < 0)
    // Unreachable!  // But [5,5] ∩ (-∞,0) = ∅
}                    // Drop this partition
```
When data contradicts control, that path is impossible.

This bidirectional refinement is called *reduction*.
The process continues until neither component can tighten further.
For formal reduction operators with soundness proofs, see @ch-advanced-galois.

#insight-box[
  Constraints flow between domains until stabilization.
  When neither the BDD control layer nor the data domain can further refine the other, the system has reached a stable reduced state.
]

== Managing Partition Growth

As programs execute, partitions multiply.
Without management, memory exhausts quickly.

Three practical strategies:

*Remove infeasible partitions:*
When BDD becomes False, drop that partition.
```rust
partitions.retain(|(path, _)| !bdd.is_zero(*path));
```

*Merge identical environments:*
If two partitions have the same abstract values, combine their paths.
```rust
// (x > 0, {y ↦ 5}) and (x < 10, {y ↦ 5})
// → ((x > 0) ∨ (x < 10), {y ↦ 5})
```

*Cap partition count ($k$-limiting):*
Set a maximum (e.g., $k = 10$).
When exceeded, force-merge the most similar partitions.
```rust
const MAX_PARTITIONS: usize = 10;
if partitions.len() > MAX_PARTITIONS {
    merge_most_similar(&mut partitions);
}
```

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
  - `heater_power` $= [0, 100] ljoin [50, 50] ljoin [0, 0] = [0, 100]$*Result*: $"heater_power" in [0, 100]$ ✓ (safety property holds)

*Limitation*: Cannot answer:
- "Under what conditions is heater at full power?"
- "Is `heater_power = 75` ever possible?"
- "What sensor range triggers half power?"

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

*Verification:* Check each partition's `heater_power` value:
- Partition 1: $100 in [0, 100]$ ✓
- Partition 2: $50 in [0, 100]$ ✓
- Partition 3: $0 in [0, 100]$ ✓

Property holds on all paths!

=== Advanced Queries Enabled by Path-Sensitivity

Path-sensitivity enables queries about the relationship between inputs and outputs:

- "When is heater at full power?" → `sensor < 15`
- "Is `heater_power = 75` possible?" → No (only 0, 50, 100)
- "What sensor values cause half power?" → `sensor` $in$ [15, 19]

This transforms analysis from "what values are possible" into "under which conditions do these values occur".

== Combining Multiple Data Domains <sec-multiple-domains>

Beyond pairing BDDs with one abstract domain, we can combine *multiple* data abstractions.
See #inline-example("domains", "combined.rs", "combined") for runnable examples.
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
  [Implements a reduced product of sign and parity domains, demonstrating how reduction eliminates impossible combinations like (Zero, Odd).],
)

#exercise-box(difficulty: "Hard")[
  Design a reduced product of interval and parity (even/odd) domains.
  Implement reduction: interval $[2, 5]$ with parity Even refines to ${2, 4}$.
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


== Research Spotlight: Trace Partitioning vs Powerset <sec-trace-partitioning-spotlight>

#info-box(title: "Research Context")[
  This section discusses research literature on trace partitioning strategies.
  Useful for readers interested in the theoretical foundations, but not essential for practical implementation.
]

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

#info-box(title: "Engineering Considerations")[
  This section discusses practical trade-offs in production analyzers.
  Part III (Performance) covers these topics in depth with benchmarks.
]

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

Path-sensitive analysis combines BDDs with abstract domains to track precise program state.

Core concepts:
- States are pairs $(b, rho)$: BDD path condition + abstract environment
- BDDs compactly represent exponentially many paths
- Abstract domains track variable properties on each path

Key operations:
- *Branch*: Split state, refine path conditions ($"path" and "cond"$, $"path" and not "cond"$)
- *Assign*: Update environment, preserve path condition
- *Join*: Merge paths with OR, join data with domain operations ($ljoin$)
- *Feasibility*: Prune when BDD becomes False

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
  - *BDDs enable path-sensitive abstract interpretation without explicit path enumeration.*
    Represent $2^n$ paths symbolically, manipulate in polynomial time.

  - *Combined state $(b, rho)$: control layer + data layer.*
    BDD tracks feasible paths, domain tracks variable values.

  - *Branching refines path conditions.*
    True branch: $"path" and "cond"$. False branch: $"path" and not "cond"$.

  - *Automatic infeasible path pruning.*
    When BDD becomes False, that path is impossible.

  - *Generic design works with any abstract domain.*
    Sign, interval, congruence, polyhedra --- BDD layer is orthogonal.

  - *Precision-performance trade-off.*
    Partitioning strategies balance path sensitivity against state explosion.
]
