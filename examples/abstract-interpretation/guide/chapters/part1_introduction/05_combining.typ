#import "../../theme.typ": *

= The Abstract State <ch-combining-domains>

We have the engine (BDDs) and the fuel (Abstract Domains).
Now we build the vehicle.

In this chapter, we define the *Abstract State* of our MiniVerifier.
Instead of a single value for each variable, our state will be a *collection* of possibilities, each guarded by a BDD path condition.

This combination yields *path-sensitive abstract interpretation*.

#info-box(title: "Guide Roadmap")[
  This chapter introduces the *intuition* and *basic architecture* of path sensitivity using a simple example.

  For the rigorous mathematical formalization (Trace Partitioning, Reduced Products) and advanced techniques (Relational Domains), see @part-ii, specifically @ch-domain-combinations.
]

== The Core Idea: Trace Partitioning

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
We maintain a set of pairs $(b_i, rho_i)$, where $b_i$ is a BDD representing a set of paths, and $rho_i$ is the abstract state on those paths.

This technique is called *Trace Partitioning*.

#figure(
  caption: [Trace Partitioning: Split and Merge. At a branch, the abstract state splits into two partitions, each guarded by a BDD path condition. These partitions evolve independently (e.g., different assignments). At the merge point, we can either keep them separate (maintaining precision) or merge them (joining data domains and unioning BDDs) to save space.],
  cetz.canvas({
    import cetz.draw: *

    let style-state = (fill: colors.bg-code, stroke: colors.primary + 1pt, radius: 0.2)
    let style-bdd = (fill: colors.secondary.lighten(80%), stroke: colors.secondary + 1pt)
    let style-data = (fill: colors.accent.lighten(80%), stroke: colors.accent + 1pt)

    let draw-state(pos, bdd-text, data-text, label) = {
      let (x, y) = pos
      rect((x - 1.5, y - 1), (x + 1.5, y + 1), ..style-state)
      content((x, y + 1.3), text(size: 0.8em, weight: "bold")[#label])

      // BDD part
      rect((x - 1.3, y + 0.1), (x + 1.3, y + 0.8), ..style-bdd)
      content((x, y + 0.45), text(size: 0.7em, font: fonts.mono)[#bdd-text])

      // Data part
      rect((x - 1.3, y - 0.8), (x + 1.3, y - 0.1), ..style-data)
      content((x, y - 0.45), text(size: 0.7em, font: fonts.mono)[#data-text])
    }

    // Initial State
    draw-state((0, 6), "True", "x: Top", "Initial State")

    // Branch
    line((0, 5), (-3, 4), mark: (end: ">"))
    content((-1.5, 4.8), text(size: 0.8em)[if x > 0])

    line((0, 5), (3, 4), mark: (end: ">"))
    content((1.5, 4.8), text(size: 0.8em)[else])

    // Split States
    draw-state((-3, 3), "x > 0", "x: Pos", "True Branch")
    draw-state((3, 3), "!(x > 0)", "x: Neg|0", "False Branch")

    // Evolution (Assignments)
    line((-3, 2), (-3, 1), mark: (end: ">"))
    content((-3.5, 1.5), text(size: 0.8em, font: fonts.mono)[y = 1])

    line((3, 2), (3, 1), mark: (end: ">"))
    content((3.5, 1.5), text(size: 0.8em, font: fonts.mono)[y = -1])

    draw-state((-3, 0), "x > 0", "y: 1", "State A")
    draw-state((3, 0), "!(x > 0)", "y: -1", "State B")

    // Merge
    line((-3, -1), (0, -2), mark: (end: ">"))
    line((3, -1), (0, -2), mark: (end: ">"))
    content((0, -1.5), text(size: 0.8em, weight: "bold")[Join])

    // Merged State
    draw-state((0, -3), "True", "y: Top", "Merged State")

    // Annotation for loss of precision
    content((2.5, -3), text(size: 0.7em, fill: colors.error)[Precision Loss!], anchor: "west")

    // Alternative: Partitioned State
    line((-3, -1), (-3, -4), mark: (end: ">"), stroke: (dash: "dashed"))
    line((3, -1), (3, -4), mark: (end: ">"), stroke: (dash: "dashed"))

    content((0, -4.5), text(size: 0.8em, weight: "bold")[Trace Partitioning])

    rect((-4.5, -6), (4.5, -3.5), fill: none, stroke: (paint: colors.success, dash: "dashed"), radius: 0.2)
    content((0, -3.8), text(size: 0.8em, fill: colors.success)[Keeps states separate!])

    content((-3, -5), text(size: 0.7em, font: fonts.mono)[(x>0, y:1)])
    content((3, -5), text(size: 0.7em, font: fonts.mono)[(!(x>0), y:-1)])

  }),
) <fig:split-merge>

== Architecture

The architecture has three components working together.
+ The *BDD control domain* tracks feasible paths using BDD operations.
+ The *abstract data domain* tracks variable properties like signs or intervals.
+ The *combined domain* pairs the BDD control state with the abstract data state to give us the full picture.

#definition(title: "BDD-based Path-Sensitive Abstract State")[
  A state is a pair $(b, rho)$ where:
  - $b$ is a BDD representing the path condition (which paths reach here)
  - $rho$ is an abstract environment mapping variables to abstract values

  The state represents: "On paths where $b$ is true, variables have values given by $rho$."
]

== Upgrading the ConditionManager

In @ch-bdd-programming, we built a `ConditionManager` that maps `Cond` AST nodes to BDD variables.
This structure is perfect for our needs.

```rust
// Recall from Chapter 1 and 4:
// pub enum Cond {
//     Lt(Expr, Expr),
//     Eq(Expr, Expr),
//     ...
// }
```

We also need to handle *negation* intelligently.
If we have allocated a variable for `x > 0`, and we encounter `x <= 0`, we shouldn't allocate a new variable.
We should just return the *negation* of the existing one.

```rust
impl ConditionManager {
    pub fn get_bdd(&mut self, cond: &Cond) -> Ref {
        // 1. Check exact match
        if let Some(&id) = self.mapping.get(cond) {
            return self.bdd.mk_var(id);
        }

        // 2. Check negation (simplified for this guide)
        // In a full implementation, we would check if we have the "opposite" condition.
        // e.g. if cond is "x <= 0", check if we have "x > 0" and return !var.

        // 3. Allocate new
        let id = self.next_var_id;
        self.next_var_id += 1;
        self.mapping.insert(cond.clone(), id);
        self.bdd.mk_var(id)
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

$(b_1, rho) ljoin (b_2, rho) = (b_1 or b_2, rho)$

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

This approach allows the analysis to distinguish `x = 5` from `x = -3` indefinitely, only merging them if they converge to the same value later.

== Refining Abstract Values

The BDD tells us *which* paths we are on.
We can use this to refine our data knowledge.
When we branch on a condition like `x > 0`, we should update the abstract value of `x` in the true branch!

```rust
impl<D: AbstractDomain + Refineable> PartitionedState<D> {
    fn assume(&mut self, cond: &Cond) {
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
    let cond = Cond::Lt(Expr::Const(0), Expr::Var("x".into())); // 0 < x

    // True branch: assume(x > 0)
    let mut true_state = state.clone();
    true_state.assume(&cond);
    // Refinement automatically sets x to Pos!
    true_state.assign_var("result", "x"); // result = Pos

    // False branch: assume(!(x > 0)) -> assume(x <= 0)
    let mut false_state = state.clone();
    let not_cond = Cond::Not(Box::new(cond.clone())); // Negation
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
  - False branch: `result ∈ [0, ∞)` (since $-x >= 0$ when $x <= 0$)
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
    True branch: $"path" and "condition"$.
    False branch: $"path" and not "condition"$.

  - *Assignment updates data domain, keeps path unchanged.*
    Only data properties change on assignment, not control flow.

  - *Joining merges paths with OR, joins data with domain operations.*
    Necessary at merge points but loses path-sensitivity.

  - *Trade-off between precision and state explosion.*
    Joining early: fast but imprecise. Joining late: precise but exponential states.

  - *Generic design works with any abstract domain.*
    Swap signs for intervals, octagons, polyhedra.
    BDD control layer is orthogonal.

  - *Path-sensitivity alone doesn't guarantee precision.*
    Need sufficiently precise data domains (intervals better than signs).

  - *Main insight:* BDDs provide compact representation of path conditions, enabling path-sensitive abstract interpretation without explicit path enumeration.
]
