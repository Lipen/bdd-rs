#import "../../theme.typ": *

= Combining BDDs with Abstract Domains <combining-bdds-abstract-domains>

We've seen abstract domains (Chapter 1) and BDDs (Chapters 3-4) separately.
Now we combine them: BDDs track _which paths are feasible_, abstract domains track _what values variables can have_.

This combination yields path-sensitive abstract interpretation.

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

Three components:

1. *BDD control domain:* Tracks feasible paths using BDD operations
2. *Abstract data domain:* Tracks variable properties (signs, intervals, etc.)
3. *Combined domain:* Pairs BDD control state with abstract data state

[Architecture diagram would go here]

```
┌─────────────────────────────────────┐
│  Combined Analysis State            │
├─────────────────────────────────────┤
│                                     │
│  ┌─────────────┐  ┌──────────────┐ │
│  │ BDD Control │  │ Data Domain  │ │
│  │             │  │              │ │
│  │ Path: b     │  │ x ↦ +        │ │
│  │             │  │ y ↦ ⊤        │ │
│  └─────────────┘  └──────────────┘ │
│                                     │
└─────────────────────────────────────┘
```

Operations:
- *Branch:* Update BDD with condition, keep data domain
- *Assignment:* Keep BDD, update data domain
- *Join:* Merge BDDs with OR, join data domains

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

From Chapter 1:

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

== Integration with Abstract Domains from Chapter 1

Recall the `AbstractDomain` trait:

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
    *Main Insight:*
    BDDs provide compact representation of path conditions, enabling path-sensitive abstract interpretation without explicit path enumeration.
  ],
)

#v(2em)
