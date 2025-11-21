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

== Canonicalizing Conditions

To leverage the power of BDDs, we must ensure that the same logical condition is always represented by the same BDD variable.
If we encounter `x > 0` in two different places, we must use the same variable.
If we encounter `x <= 0`, we should use the *negation* of that variable.

We introduce a `ConditionManager` to handle this mapping:

```rust
use std::collections::HashMap;
use std::rc::Rc;
use bdd_rs::{Bdd, Ref};

#[derive(Hash, Eq, PartialEq, Clone, Debug)]
enum Condition {
    Gt(String, i32), // x > c
    Eq(String, i32), // x == c
    // ... other conditions
}

struct ConditionManager {
    bdd: Rc<Bdd>,
    mapping: HashMap<Condition, u32>,
    next_var: u32,
}

impl ConditionManager {
    fn new() -> Self {
        Self {
            bdd: Rc::new(Bdd::default()),
            mapping: HashMap::new(),
            next_var: 1,
        }
    }

    fn get_bdd(&mut self, cond: &Condition) -> Ref {
        if let Some(&var) = self.mapping.get(cond) {
            return self.bdd.mk_var(var);
        }

        // In a real implementation, we would also check for negations here.
        // e.g., if requesting (x <= c), check if we have (x > c) and return NOT.

        // Allocate new if not found
        let var = self.next_var;
        self.next_var += 1;
        self.mapping.insert(cond.clone(), var);
        self.bdd.mk_var(var)
    }
}
```

Now, the analysis automatically correlates related branches across the program.
If the program branches on `x > 0` twice, the BDD will recognize it's the same condition.

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
    control: Rc<RefCell<ConditionManager>>,
}

impl<D: AbstractDomain> PartitionedState<D> {
    fn new(control: Rc<RefCell<ConditionManager>>) -> Self {
        let bdd = control.borrow().bdd.clone();
        Self {
            partitions: vec![(bdd.mk_true(), D::bottom())], // Start with true path
            control,
        }
    }
}
```

The state is a disjunction: "Either we are on path $b_1$ with data $rho_1$, OR on path $b_2$ with data $rho_2$, ...".

=== Smart Joining

When we join two states, we don't blindly merge everything.
We use BDDs to compress the representation.
If two paths lead to the *same* data state, we can merge their path conditions!

$(b_1, rho) join (b_2, rho) = (b_1 or b_2, rho)$

```rust
impl<D: AbstractDomain + PartialEq + Clone> PartitionedState<D> {
    fn join(&self, other: &Self) -> Self {
        let mut new_partitions = self.partitions.clone();
        let bdd = &self.control.borrow().bdd;

        for (path2, env2) in &other.partitions {
            // Try to merge with existing partition
            let mut merged = false;
            for (path1, env1) in &mut new_partitions {
                if env1 == env2 {
                    // MAGIC: Same data state? Merge the paths!
                    *path1 = bdd.apply_or(*path1, *path2);
                    merged = true;
                    break;
                }
            }
            if !merged {
                new_partitions.push((*path2, env2.clone()));
            }
        }

        // Optional: If too many partitions, force a merge of similar states
        // to prevent exponential blowup.

        Self {
            partitions: new_partitions,
            control: self.control.clone()
        }
    }
}
```

This approach allows the analysis to distinguish `x=5` from `x=-3` indefinitely, only merging them if they converge to the same value later.

== Refining Abstract Values

The BDD tells us *which* paths we are on. We can use this to refine our data knowledge.
When we branch on a condition like `x > 0`, we should update the abstract value of `x` in the true branch!

```rust
impl<D: AbstractDomain + Refineable> PartitionedState<D> {
    fn assume(&mut self, cond: &Condition) {
        let mut new_partitions = Vec::new();
        let bdd_cond = self.control.borrow_mut().get_bdd(cond);
        let bdd = &self.control.borrow().bdd;

        for (path, mut env) in self.partitions.drain(..) {
            // 1. Update Control: Add condition to path
            let new_path = bdd.apply_and(path, bdd_cond);

            if !bdd.is_false(new_path) {
                // 2. Update Data: Refine environment
                // e.g., if cond is "x > 0", refine x to Positive
                env.refine(cond);
                new_partitions.push((new_path, env));
            }
        }
        self.partitions = new_partitions;
    }
}
```

Now, when the analysis sees `if x > 0`, it automatically learns that `x` is positive in the true branch, even if the interval domain didn't know it before.

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

With our new architecture:

```rust
fn analyze_function() {
    let control = Rc::new(RefCell::new(ConditionManager::new()));
    let mut state = PartitionedState::<Sign>::new(control.clone());

    // Initial: result = 0
    state.assign("result", Sign::Zero);

    // Branch on x > 0
    let cond = Condition::Gt("x".to_string(), 0);

    // True branch: assume(x > 0)
    let mut true_state = state.clone();
    true_state.assume(&cond);
    // Refinement automatically sets x to Pos!
    true_state.assign_var("result", "x"); // result = Pos

    // False branch: assume(!(x > 0)) -> assume(x <= 0)
    let mut false_state = state.clone();
    let not_cond = Condition::Le("x".to_string(), 0); // Negation
    false_state.assume(&not_cond);
    // Refinement sets x to NonPos (Zero | Neg)

    // result = -x
    // -(Zero | Neg) = Zero | Pos
    false_state.assign_neg("result", "x");

    // Merge at end of function
    let final_state = true_state.join(&false_state);

    // Result:
    // Partition 1 (x>0): result = Pos
    // Partition 2 (x<=0): result = Zero | Pos
    //
    // If we query "result", we get the join of all partitions:
    // Pos ⊔ (Zero ⊔ Pos) = NonNeg
    println!("Result: {:?}", final_state.get("result"));
}
```

We achieved better precision!
And crucially, if we had a later check `if x > 0`, the BDD would know that Partition 2 is impossible, automatically pruning the path.

#insight-box[
  *Key Insight:*
  The combination of *Partitioning* (keeping states separate) and *Refinement* (learning from path conditions) is what makes BDD-based analysis powerful.
]

== Integration with Abstract Domains

Recall the `AbstractDomain` trait (from @ch-abstraction):

```rust
trait AbstractDomain: Clone + PartialEq + Debug {
    fn bottom() -> Self;
    fn top() -> Self;
    fn join(&self, other: &Self) -> Self;
    fn meet(&self, other: &Self) -> Self;
    fn widen(&self, other: &Self) -> Self;
    fn le(&self, other: &Self) -> bool;
}
```

Our `PartitionedState<D>` is already generic!
We can plug in *any* abstract domain `D` that implements this trait.

```rust
// The structure we defined earlier is already generic:
struct PartitionedState<D: AbstractDomain> {
    partitions: Vec<(Ref, D)>, // List of (Path Condition, Data State)
    control: Rc<RefCell<ConditionManager>>,
}
```

This allows us to easily swap the underlying data analysis.
If we want to track ranges of values instead of just signs, we simply use `PartitionedState<Interval>`.
The BDD logic for path partitioning remains exactly the same.

#info-box(title: "Going Deeper")[
  This generic structure is formally known as a *Disjunctive Completion* or *Trace Partitioning Domain*.

  In @ch-domain-combinations, we will enhance this with:
  - *Reduction*: Allowing the BDD and Data domain to exchange information (refining data based on path conditions).
  - *Widening*: Handling loops correctly to ensure termination.
  - *Relational Domains*: Tracking correlations between variables.
]

#example-box(number: "5.2", title: "Interval Domain")[
  Replace signs with intervals:

  ```rust
  #[derive(Debug, Clone, PartialEq)]
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
