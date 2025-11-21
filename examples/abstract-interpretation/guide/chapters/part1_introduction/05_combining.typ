#import "../../theme.typ": *

= Combining BDDs with Abstract Domains <ch-combining-domains>

We've seen abstract domains (@ch-abstraction) and BDDs (@ch-bdds, @ch-bdd-programming) separately.
Now we combine them: BDDs track _which paths are feasible_, abstract domains track _what values variables can have_.

This combination yields path-sensitive abstract interpretation.

#info-box(title: "Guide Roadmap")[
  This chapter introduces the *intuition* and *basic architecture* of path sensitivity using a simple example.

  For the rigorous mathematical formalization (Trace Partitioning, Reduced Products) and advanced techniques (Relational Domains), see *Part II: Deep Dive*, specifically @ch-domain-combinations.
]

== The Core Idea

Path-insensitive analysis loses precision by merging all paths:

```rust
let mut x = 0;
if condition {
    x = 5;      // x = +
} else {
    x = -3;     // x = -
}
// Path-insensitive: x = + ⊔ - = ⊤ (unknown)
```

Path-sensitive analysis maintains separate states:

```rust
// State 1: condition=true, x=+
// State 2: condition=false, x=-
```

But with $n$ conditions, we get $2^n$ explicit states.

*Solution:* Represent path conditions _symbolically_ with BDDs.

#definition(title: "BDD-based Path-Sensitive Abstract State")[
  A state is a pair $(b, rho)$ where:
  - $b$ is a BDD representing the path condition (which paths reach here)
  - $rho$ is an abstract environment mapping variables to abstract values

  The state represents: "On paths where $b$ is true, variables have values given by $rho$."
]

== Architecture

The architecture has three components working together.
+ The *BDD control domain* tracks feasible paths using BDD operations.
+ The *abstract data domain* tracks variable properties like signs or intervals.
+ The *combined domain* pairs the BDD control state with the abstract data state to give us the full picture.

#figure(
  caption: [Three-component architecture for path-sensitive analysis. The combined state pairs a BDD representing the path condition with an abstract environment. When paths branch, the BDD splits while the data domain is copied. At join points, BDDs merge with OR and data domains join in the abstract lattice.],

  cetz.canvas({
    import cetz.draw: *

    // Helper functions
    let draw-component-box(pos, width, height, label, color) = {
      rect(pos, (pos.at(0) + width, pos.at(1) + height), fill: colors.bg-code, stroke: color + 2pt, radius: 0.15)
      content(
        (pos.at(0) + width / 2, pos.at(1) + height - 0.3),
        text(fill: color, weight: "bold", size: 0.85em)[#label],
        anchor: "north",
      )
    }

    let draw-content-line(pos, body, size: 0.75) = {
      content(pos, text(size: size * 1em)[#body], anchor: "west")
    }

    let draw-bracket(x1, x2, y, label) = {
      line((x1, y), (x2, y), stroke: colors.text-light + 1pt)
      line((x1, y), (x1, y - 0.1), stroke: colors.text-light + 1pt)
      line((x2, y), (x2, y - 0.1), stroke: colors.text-light + 1pt)
      content(((x1 + x2) / 2, y + 0.15), text(size: 0.7em, fill: colors.text-light)[#label], anchor: "south")
    }

    // Main combined state box
    draw-component-box((0, 2), 7, 2.5, "Combined Analysis State", colors.primary)

    // BDD control component
    draw-component-box((0.3, 2.5), 3, 1.5, "BDD Control", colors.secondary)
    draw-content-line((0.5, 3.3), [Path condition:])
    draw-content-line((0.5, 2.95), [$b = x_1 and not x_2$])

    // Data domain component
    draw-component-box((3.7, 2.5), 3, 1.5, "Data Domain", colors.accent)
    draw-content-line((3.9, 3.3), [Variable map:])
    draw-content-line((3.9, 2.95), [$x arrow.r.bar plus.minus$])
    draw-content-line((3.9, 2.65), [$y arrow.r.bar top$])

    // Operation arrows below
    content((3.5, 1.5), text(fill: colors.primary, weight: "bold", size: 0.85em)[Key Operations:], anchor: "north")

    // Branch operation
    content((1.5, 0.8), text(size: 0.75em)[*Branch:*], anchor: "north")
    content((1.5, 0.5), text(size: 0.7em)[Update BDD $->$], anchor: "north")
    content((1.5, 0.25), text(size: 0.7em)[Keep data], anchor: "north")

    // Assign operation
    content((3.5, 0.8), text(size: 0.75em)[*Assign:*], anchor: "north")
    content((3.5, 0.5), text(size: 0.7em)[Keep BDD $->$], anchor: "north")
    content((3.5, 0.25), text(size: 0.7em)[Update data], anchor: "north")

    // Join operation
    content((5.5, 0.8), text(size: 0.75em)[*Join:*], anchor: "north")
    content((5.5, 0.5), text(size: 0.7em)[BDD: OR $->$], anchor: "north")
    content((5.5, 0.25), text(size: 0.7em)[Data: $union.sq$], anchor: "north")

    draw-bracket(0.3, 3.3, 2.2, "Control state")
    draw-bracket(3.7, 6.7, 2.2, "Data state")
  }),
) <fig:three-component-architecture>

The key operations follow naturally from this structure.
- When we *branch*, we update the BDD with the condition while keeping the data domain unchanged.
- During *assignment*, we keep the BDD path and update only the data domain.
- At *join* points, we merge BDDs with OR and join the data domains together.

== The BDD Control Domain

Allocates BDD variables to represent Boolean conditions in the program.

```rust
use bdd_rs::Bdd;
use std::rc::Rc;

struct BddControlDomain {
    bdd: Rc<Bdd>,
    next_var: u32,
}

impl BddControlDomain {
    fn new() -> Self {
        Self {
            bdd: Rc::new(Bdd::default()),
            next_var: 1,  // Start from 1 (0 is reserved)
        }
    }

    // Allocate a fresh BDD variable for a condition
    fn alloc_var(&mut self) -> u32 {
        let var = self.next_var;
        self.next_var += 1;
        var
    }

    // Create BDD for a variable
    fn mk_var(&self, var: u32) -> Ref {
        self.bdd.mk_var(var)
    }
}
```

Each program condition (e.g., `x > 0`) gets a unique BDD variable.

== Example: Sign Domain with BDDs

Let's implement path-sensitive sign analysis.

=== Data Domain: Sign Lattice

From @ch-abstraction:

```rust
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
enum Sign {
    Bot,    // Unreachable
    Neg,    // Negative
    Zero,   // Zero
    Pos,    // Positive
    Top,    // Unknown
}

impl Sign {
    fn join(&self, other: &Self) -> Self {
        use Sign::*;
        match (self, other) {
            (Bot, x) | (x, Bot) => *x,
            (x, y) if x == y => *x,
            _ => Top,
        }
    }

    fn abs_add(&self, other: &Self) -> Self {
        use Sign::*;
        match (self, other) {
            (Bot, _) | (_, Bot) => Bot,
            (Top, _) | (_, Top) => Top,
            (Zero, x) | (x, Zero) => *x,
            (Pos, Pos) => Pos,
            (Neg, Neg) => Neg,
            _ => Top,  // Mixed signs
        }
    }
}
```

=== Combined State

```rust
struct PathSensitiveState {
    control: Rc<BddControlDomain>,
    path: Ref,                      // BDD representing path condition
    env: HashMap<String, Sign>,     // Variable → Sign
}

impl PathSensitiveState {
    fn new(control: Rc<BddControlDomain>) -> Self {
        Self {
            control: control.clone(),
            path: control.bdd.mk_true(),  // Initially: all paths enabled
            env: HashMap::new(),
        }
    }
}
```

=== Branching

When encountering a branch, split into two states:

```rust
impl PathSensitiveState {
    fn branch(&self, condition_var: u32) -> (Self, Self) {
        let cond_bdd = self.control.mk_var(condition_var);

        // True branch: path ∧ condition
        let true_path = self.control.bdd.apply_and(self.path, cond_bdd);
        let true_state = Self {
            control: self.control.clone(),
            path: true_path,
            env: self.env.clone(),
        };

        // False branch: path ∧ ¬condition
        let not_cond = self.control.bdd.apply_not(cond_bdd);
        let false_path = self.control.bdd.apply_and(self.path, not_cond);
        let false_state = Self {
            control: self.control.clone(),
            path: false_path,
            env: self.env.clone(),
        };

        (true_state, false_state)
    }
}
```

Each branch gets a separate state with updated path condition.
Data environment is cloned (remains unchanged by branching).

#figure(
  caption: [State branching on a condition. The input state splits into two: true branch gets path $(b and c)$, false branch gets $(b and not c)$. The data environment is copied to both branches unchanged. Later, at the join point, paths merge with OR and data values join in the lattice.],

  cetz.canvas({
    import cetz.draw: *

    // Helper functions
    let draw-state-box(pos, width, height, path-label, data-label) = {
      rect(
        pos,
        (pos.at(0) + width, pos.at(1) + height),
        fill: colors.bg-code,
        stroke: colors.primary + 1.5pt,
        radius: 0.1,
      )

      // Path section
      rect(
        (pos.at(0), pos.at(1) + height / 2),
        (pos.at(0) + width, pos.at(1) + height),
        fill: rgb("#e0e7ff"),
        stroke: none,
      )
      content(
        (pos.at(0) + width / 2, pos.at(1) + height - 0.25),
        text(size: 0.7em, fill: colors.secondary)[#path-label],
        anchor: "north",
      )

      // Data section
      content((pos.at(0) + width / 2, pos.at(1) + 0.25), text(size: 0.7em)[#data-label], anchor: "south")
    }

    let draw-arrow(from-pos, to-pos, label: none) = {
      line(from-pos, to-pos, stroke: colors.primary + 1.5pt, mark: (end: ">"))
      if label != none {
        let mid-x = (from-pos.at(0) + to-pos.at(0)) / 2
        let mid-y = (from-pos.at(1) + to-pos.at(1)) / 2
        content((mid-x + 0.5, mid-y), text(size: 0.65em, fill: colors.text-light)[#label], anchor: "west")
      }
    }

    // Initial state
    draw-state-box((0, 2.5), 2.2, 1, "Path: $b$", "Env: $x arrow.r.bar plus.minus$")
    content((-0.3, 3), text(size: 0.75em, fill: colors.text-light)[Input state], anchor: "east")

    // Branch point
    content((1.1, 1.8), text(size: 0.8em, fill: colors.primary, weight: "bold")[Branch on $c$])

    // True branch state
    draw-state-box((-1.5, 0.2), 2.2, 1, "Path: $b and c$", "Env: $x arrow.r.bar plus.minus$")
    content((-2.8, 0.7), text(size: 0.7em, fill: colors.success)[True branch], anchor: "east")

    // False branch state
    draw-state-box((2, 0.2), 2.2, 1, "Path: $b and not c$", "Env: $x arrow.r.bar plus.minus$")
    content((4.5, 0.7), text(size: 0.7em, fill: colors.error)[False branch], anchor: "west")

    // Branching arrows
    draw-arrow((1.1, 2.5), (-0.4, 1.2), label: "true")
    draw-arrow((1.1, 2.5), (3.1, 1.2), label: "false")

    // Join point
    content((1.1, -0.5), text(size: 0.8em, fill: colors.primary, weight: "bold")[Join])

    // Joined state
    draw-state-box((0, -2), 2.2, 1, "Path: $b$", "Env: $x arrow.r.bar plus.minus$")

    // Join arrows
    draw-arrow((-0.4, 0.2), (1.1, -1))
    draw-arrow((3.1, 0.2), (1.1, -1))

    // Annotations
    content((-2.5, -1.5), text(size: 0.65em, fill: colors.text-light)[$(b and c) or$], anchor: "east")
    content((-2.5, -1.75), text(size: 0.65em, fill: colors.text-light)[$(b and not c) = b$], anchor: "east")
  }),
) <fig:state-branching>

=== Assignment

```rust
impl PathSensitiveState {
    fn assign(&mut self, var: &str, value: Sign) {
        self.env.insert(var.to_string(), value);
        // Path condition unchanged
    }

    fn get(&self, var: &str) -> Sign {
        self.env.get(var).copied().unwrap_or(Sign::Top)
    }
}
```

Assignments update data domain only.

=== Joining States

When control flow merges (e.g., after if-else), join states:

```rust
impl PathSensitiveState {
    fn join(&self, other: &Self) -> Self {
        // Merge path conditions: path₁ ∨ path₂
        let merged_path = self.control.bdd.apply_or(self.path, other.path);

        // Join data environments
        let mut merged_env = HashMap::new();
        let all_vars: HashSet<_> = self.env.keys()
            .chain(other.env.keys())
            .collect();

        for var in all_vars {
            let val1 = self.get(var);
            let val2 = other.get(var);
            merged_env.insert(var.to_string(), val1.join(&val2));
        }

        Self {
            control: self.control.clone(),
            path: merged_path,
            env: merged_env,
        }
    }
}
```

BDD paths are merged with OR.
Data values are joined in the abstract domain.

#warning-box[
  *Joining loses path-sensitivity.*

  After joining states from different paths, we can no longer distinguish them.
  This is necessary at merge points but sacrifices some precision.

  To maintain full path-sensitivity, keep states separate and analyze them independently.
  Trade-off: precision vs. state explosion.
]

== Complete Example: Path-Sensitive Analysis

Analyze this function:

```rust
fn analyze(x: i32) -> i32 {
    let mut result = 0;
    if x > 0 {
        result = x;     // result = +
    } else {
        result = -x;    // result = ?
    }
    result
}
```

Path-insensitive: `result = ⊤` after merge.
Path-sensitive: `result = +` on _both_ paths (if we're smart).

Implementation:

```rust
fn analyze_function() {
    let control = Rc::new(BddControlDomain::new());
    let mut state = PathSensitiveState::new(control.clone());

    // Initial: result = 0
    state.assign("result", Sign::Zero);

    // Allocate BDD variable for condition "x > 0"
    let cond_var = control.borrow_mut().alloc_var();

    // Branch on x > 0
    let (mut true_state, mut false_state) = state.branch(cond_var);

    // True branch: x > 0, so x is positive
    // result = x → result = +
    true_state.assign("x", Sign::Pos);
    true_state.assign("result", Sign::Pos);

    // False branch: x ≤ 0, so x is non-positive
    // result = -x → result = ?
    // (Could be 0 if x=0, or positive if x<0)
    false_state.assign("x", Sign::Neg.join(&Sign::Zero));
    // Abstract interpretation of -x:
    // -(Neg ⊔ Zero) = Pos ⊔ Zero
    false_state.assign("result", Sign::Pos.join(&Sign::Zero));

    // Merge at end of function
    let final_state = true_state.join(&false_state);

    // Result: + ⊔ (+ ⊔ 0) = + ⊔ 0 = ⊤ (due to join with Zero)
    let result_sign = final_state.get("result");
    println!("Result sign: {:?}", result_sign);
}
```

#example-box(number: "5.1", title: "Analysis Precision")[
  Even with path-sensitivity, we get `⊤` here because:
  - True branch: `result = +`
  - False branch: `result = + ⊔ 0` (since x could be 0 or negative)
  - Join: `+ ⊔ (+ ⊔ 0) = ⊤`

  To prove `result = +`, we'd need a richer domain (e.g., intervals) that tracks `x ≤ 0 ⇒ -x ≥ 0`.

  This illustrates: _Path-sensitivity helps but doesn't solve everything._
  Domain precision matters too.
]

== Multiple Paths: Real Path Sensitivity

Consider:

```rust
fn multi_path(a: bool, b: bool) -> i32 {
    let mut x = 0;
    if a {
        x = 5;
    }
    if b {
        x = x + 1;
    }
    x
}
```

Four paths:
1. `¬a ∧ ¬b`: x = 0
2. `¬a ∧ b`: x = 0 + 1 = 1
3. `a ∧ ¬b`: x = 5
4. `a ∧ b`: x = 5 + 1 = 6

Path-insensitive analysis: `x = ⊤` (0, 1, 5, 6 → unknown)

Path-sensitive with BDDs:

```rust
fn analyze_multi_path() {
    let control = Rc::new(BddControlDomain::new());
    let mut state = PathSensitiveState::new(control.clone());

    state.assign("x", Sign::Zero);

    // First branch: if a
    let var_a = control.borrow_mut().alloc_var();
    let (mut state_a_true, mut state_a_false) = state.branch(var_a);

    state_a_true.assign("x", Sign::Pos);  // x = 5
    // state_a_false: x = 0

    // Second branch: if b (on both paths)
    let var_b = control.borrow_mut().alloc_var();

    let (mut state_ab_true, state_ab_false) = state_a_true.branch(var_b);
    state_ab_true.assign("x", Sign::Pos);  // x = 5 + 1 = 6 (pos)
    // state_ab_false: x = 5 (pos)

    let (mut state_not_a_b_true, state_not_a_b_false) = state_a_false.branch(var_b);
    state_not_a_b_true.assign("x", Sign::Pos);  // x = 0 + 1 = 1 (pos)
    // state_not_a_b_false: x = 0 (zero)

    // Merge all four paths
    let final_state = state_ab_true
        .join(&state_ab_false)
        .join(&state_not_a_b_true)
        .join(&state_not_a_b_false);

    // Result: Pos ⊔ Pos ⊔ Pos ⊔ Zero = Pos ⊔ Zero = ⊤
    let x_sign = final_state.get("x");
    println!("x sign: {:?}", x_sign);
}
```

Still loses precision due to joining Zero with Pos.

#insight-box[
  *Key Insight:* Path-sensitivity alone doesn't guarantee precision.
  We also need:
  1. Fine-grained abstract domains (intervals, not just signs)
  2. Relational domains (tracking x=y+1, not just individual values)
  3. Smart join strategies (delaying joins when possible)
]

== Avoiding Premature Joins

One strategy: maintain _multiple states_ without joining.

```rust
struct MultiState {
    control: Rc<BddControlDomain>,
    states: Vec<PathSensitiveState>,
}

impl MultiState {
    fn new(control: Rc<BddControlDomain>) -> Self {
        Self {
            control: control.clone(),
            states: vec![PathSensitiveState::new(control)],
        }
    }

    fn branch_all(&mut self, condition_var: u32) {
        let mut new_states = Vec::new();
        for state in &self.states {
            let (t, f) = state.branch(condition_var);
            new_states.push(t);
            new_states.push(f);
        }
        self.states = new_states;
    }

    // Only join when necessary (e.g., at function exit)
    fn join_all(&self) -> PathSensitiveState {
        self.states.iter()
            .fold(PathSensitiveState::new(self.control.clone()), |acc, s| acc.join(s))
    }
}
```

This maintains full path-sensitivity but risks state explosion.

#warning-box[
  *State explosion trade-off:*
  - Joining early: loses precision, bounded states
  - Joining late: maintains precision, exponential states

  Real analyses use heuristics:
  - Join at loop headers (required for termination)
  - Join after long sequences of branches
  - Use BDD size as indicator (merge when BDD grows too large)
]

== Integration with Abstract Domains

Recall the `AbstractDomain` trait (from @ch-abstraction):

```rust
trait AbstractDomain {
    fn bottom() -> Self;
    fn top() -> Self;
    fn join(&self, other: &Self) -> Self;
    fn meet(&self, other: &Self) -> Self;
    fn widen(&self, other: &Self) -> Self;
    fn le(&self, other: &Self) -> bool;
}
```

We can make our path-sensitive state generic:

```rust
struct GenericPathSensitiveState<D: AbstractDomain> {
    control: Rc<BddControlDomain>,
    path: Ref,
    env: HashMap<String, D>,
}

impl<D: AbstractDomain> GenericPathSensitiveState<D> {
    fn join(&self, other: &Self) -> Self {
        let merged_path = self.control.bdd.apply_or(self.path, other.path);

        let mut merged_env = HashMap::new();
        let all_vars: HashSet<_> = self.env.keys()
            .chain(other.env.keys())
            .collect();

        for var in all_vars {
            let val1 = self.env.get(var.as_str()).unwrap_or(&D::bottom());
            let val2 = other.env.get(var.as_str()).unwrap_or(&D::bottom());
            merged_env.insert(var.to_string(), val1.join(val2));
        }

        Self {
            control: self.control.clone(),
            path: merged_path,
            env: merged_env,
        }
    }
}
```

Now we can use _any_ abstract domain: signs, intervals, octagons, etc.

#info-box(title: "Going Deeper")[
  This generic structure is formally known as a *Direct Product Domain*.

  In @ch-domain-combinations, we will enhance this with:
  - *Reduction*: Allowing the BDD and Data domain to exchange information (refining data based on path conditions).
  - *Widening*: Handling loops correctly to ensure termination.
  - *Relational Domains*: Tracking correlations between variables.
]

#example-box(number: "5.2", title: "Interval Domain")[
  Replace signs with intervals:

  ```rust
  #[derive(Debug, Clone)]
  struct Interval {
      low: i64,
      high: i64,
  }

  impl AbstractDomain for Interval {
      fn join(&self, other: &Self) -> Self {
          Interval {
              low: self.low.min(other.low),
              high: self.high.max(other.high),
          }
      }
      // ... other methods
  }
  ```

  With intervals, our earlier example gives better precision:
  - True branch: `result ∈ [1, ∞)`
  - False branch: `result ∈ [0, ∞)` (since -x ≥ 0 when x ≤ 0)
  - Join: `result ∈ [0, ∞)` (non-negative)

  Much more precise than sign analysis!
]

== Summary

Combining BDDs with abstract domains gives path-sensitive analysis:
- BDDs track feasible paths compactly
- Abstract domains track variable properties
- States are pairs $(b, rho)$: path condition + data environment

Operations:
- *Branch:* Split state, update BDD path condition
- *Assign:* Update data environment, keep path condition
- *Join:* Merge BDDs with OR, join data domains

Trade-offs:
- Early join: loses precision, bounded states
- Late join: maintains precision, risks state explosion
- Heuristics balance precision and performance

Generic design allows any abstract domain with BDD control.

In the next chapter, we build a complete symbolic executor using these techniques.

#chapter-summary(
  [
    *Combined state: $(b, rho)$ where $b$ is BDD path condition, $rho$ is abstract environment.*
    BDD tracks which paths are feasible, domain tracks variable values.
  ],
  [
    *BDD control domain allocates variables for program conditions.*
    Each boolean condition (e.g., `x > 0`) gets a unique BDD variable.
  ],
  [
    *Branching creates two states with updated path conditions.*
    True branch: $"path" and "condition"$. False branch: $"path" and not "condition"$.
  ],
  [
    *Assignment updates data domain, keeps path unchanged.*
    Only data properties change on assignment, not control flow.
  ],
  [
    *Joining merges paths with OR, joins data with domain operations.*
    Necessary at merge points but loses path-sensitivity.
  ],
  [
    *Trade-off between precision and state explosion.*
    Joining early: fast but imprecise. Joining late: precise but exponential states.
  ],
  [
    *Generic design works with any abstract domain.*
    Swap signs for intervals, octagons, polyhedra. BDD control layer is orthogonal.
  ],
  [
    *Path-sensitivity alone doesn't guarantee precision.*
    Need sufficiently precise data domains (intervals better than signs).
  ],
  [
    *Main insight:*
    BDDs provide compact representation of path conditions, enabling path-sensitive abstract interpretation without explicit path enumeration.
  ],
)

#v(2em)
