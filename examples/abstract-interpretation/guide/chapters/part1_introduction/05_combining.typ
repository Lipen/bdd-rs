#import "../../theme.typ": *

= The Abstract Packet State <ch-combining-domains>

We have the engine (BDDs) and the fuel (Abstract Domains).
Now we build the vehicle.

In this chapter, we define the *Abstract Packet State* of our Firewall Checker.
Instead of a single value for each header field, our state will be a *collection* of possibilities, each guarded by a BDD path condition.

This combination yields *path-sensitive abstract interpretation*.

#info-box(title: "Guide Roadmap")[
  This chapter introduces the *intuition* and *basic architecture* of path sensitivity using a simple example.

  For the rigorous mathematical formalization (Trace Partitioning, Reduced Products) and advanced techniques (Relational Domains), see @part-ii, specifically @ch-domain-combinations.
]

== The Core Idea: Trace Partitioning

Path-insensitive analysis loses precision by merging all paths:

```rust
let mut mark = 0;
if proto == TCP {
    mark = 1;      // mark = 1
} else {
    mark = 2;      // mark = 2
}
// Path-insensitive: mark = 1 ⊔ 2 = [1, 2] (or Top)
// We lost the correlation that (TCP => 1) and (UDP => 2).
```

Path-sensitive analysis maintains separate states:

```rust
// State 1: proto=TCP, mark=1
// State 2: proto!=TCP, mark=2
```

But with $n$ conditions, we get $2^n$ explicit states.

*Solution:* Represent path conditions _symbolically_ with BDDs.
We maintain a set of pairs $(b_i, rho_i)$, where $b_i$ is a BDD representing a set of paths (packet flows), and $rho_i$ is the abstract state of the headers on those paths.

This technique is called *Trace Partitioning*.

#figure(
  caption: [Trace Partitioning: Split and Merge. At a branch, the abstract state splits into two partitions, each guarded by a BDD path condition. These partitions evolve independently (e.g., different NAT rules). At the merge point, we can either keep them separate (maintaining precision) or merge them (joining data domains and unioning BDDs) to save space.],
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
    draw-state((0, 6), "True", "p: Top", "Initial State")

    // Branch
    line((0, 5), (-3, 4), mark: (end: ">"))
    content((-1.5, 4.8), text(size: 0.8em)[if tcp])

    line((0, 5), (3, 4), mark: (end: ">"))
    content((1.5, 4.8), text(size: 0.8em)[else])

    // Split States
    draw-state((-3, 3), "tcp", "p: 6", "TCP Branch")
    draw-state((3, 3), "!tcp", "p: !6", "Other Branch")

    // Evolution (Assignments)
    line((-3, 2), (-3, 1), mark: (end: ">"))
    content((-3.5, 1.5), text(size: 0.8em, font: fonts.mono)[mark=1])

    line((3, 2), (3, 1), mark: (end: ">"))
    content((3.5, 1.5), text(size: 0.8em, font: fonts.mono)[mark=2])

    draw-state((-3, 0), "tcp", "m: 1", "State A")
    draw-state((3, 0), "!tcp", "m: 2", "State B")

    // Merge
    line((-3, -1), (0, -2), mark: (end: ">"))
    line((3, -1), (0, -2), mark: (end: ">"))
    content((0, -1.5), text(size: 0.8em, weight: "bold")[Join])

    // Merged State
    draw-state((0, -3), "True", "m: Top", "Merged State")

    // Annotation for loss of precision
    content((2.5, -3), text(size: 0.7em, fill: colors.error)[Precision Loss!], anchor: "west")

    // Alternative: Partitioned State
    line((-3, -1), (-3, -4), mark: (end: ">"), stroke: (dash: "dashed"))
    line((3, -1), (3, -4), mark: (end: ">"), stroke: (dash: "dashed"))

    content((0, -4.5), text(size: 0.8em, weight: "bold")[Trace Partitioning])

    rect((-4.5, -6), (4.5, -3.5), fill: none, stroke: (paint: colors.success, dash: "dashed"), radius: 0.2)
    content((0, -3.8), text(size: 0.8em, fill: colors.success)[Keeps states separate!])

    content((-3, -5), text(size: 0.7em, font: fonts.mono)[(tcp, m:1)])
    content((3, -5), text(size: 0.7em, font: fonts.mono)[(!tcp, m:2)])

  }),
) <fig:split-merge>

== Architecture

The architecture has three components working together.
+ The *BDD Path Tracker* tracks feasible paths using BDD operations.
+ The *Abstract Header Domain* tracks header field properties like IP ranges or port sets.
+ The *Combined Domain* pairs the BDD control state with the abstract header state to give us the full picture.

#definition(title: "BDD-based Path-Sensitive Abstract State")[
  A state is a pair $(b, rho)$ where:
  - $b$ is a BDD representing the path condition (which packets reach here)
  - $rho$ is an abstract environment mapping header fields to abstract values

  The state represents: "For packets satisfying $b$, the headers have values given by $rho$."
]

== Upgrading the FilterManager

In @ch-bdd-programming, we built a `FilterManager` that maps `Match` AST nodes to BDD variables.
This structure is perfect for our needs.

We also need to handle *negation* intelligently.
If we have allocated a variable for `src_ip == 10.0.0.1`, and we encounter `src_ip != 10.0.0.1`, we shouldn't allocate a new variable.
We should just return the *negation* of the existing one.

```rust
impl FilterManager {
    pub fn get_bdd(&mut self, m: &Match) -> Ref {
        // 1. Check exact match
        if let Some(&id) = self.mapping.get(m) {
            return self.bdd.mk_var(id as u32);
        }

        // 2. Check negation (simplified for this guide)
        // In a full implementation, we would check if we have the "opposite" rule.
        // e.g. if m is "src != A", check if we have "src == A" and return !var.

        // 3. Allocate new
        let id = self.next_var_id;
        self.next_var_id += 1;
        self.mapping.insert(m.clone(), id);
        self.bdd.mk_var(id as u32)
    }
}
```

Now, the analysis automatically correlates related branches across the firewall chains.
If the chain matches on `tcp` twice, the BDD will recognize it's the same condition.

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
    control: Rc<RefCell<FilterManager>>,
}

impl<D: AbstractDomain> PartitionedState<D> {
    fn new(control: Rc<RefCell<FilterManager>>) -> Self {
        let bdd = control.borrow().bdd.clone();
        Self {
            partitions: vec![(bdd.mk_true(), D::bottom())], // Start with true path
            control,
        }
    }
}
```

The state is a disjunction: "Either the packet matches $b_1$ with headers $rho_1$, OR it matches $b_2$ with headers $rho_2$, ...".

=== Smart Joining

When we join two states, we don't blindly merge everything.
We use BDDs to compress the representation.
If two paths lead to the *same* header state, we can merge their path conditions!

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
                    // MAGIC: Same header state? Merge the paths!
                    *path1 = bdd.apply_or(*path1, *path2);
                    merged = true;
                    break;
                }
            }
            if !merged {
                new_partitions.push((*path2, env2.clone()));
            }
        }

        // Note: In a real implementation, we would also merge "similar" states
        // (e.g., using widening) to prevent the number of partitions from growing indefinitely.

        Self {
            partitions: new_partitions,
            control: self.control.clone()
        }
    }
}
```

This approach allows the analysis to distinguish `mark = 1` from `mark = 2` indefinitely, only merging them if they converge to the same value later.

== Refining Abstract Values

The BDD tells us *which* paths we are on.
We can use this to refine our data knowledge.
When we branch on a condition like `port < 1024`, we should update the abstract value of `port` in the true branch!

```rust
impl<D: AbstractDomain + Refineable> PartitionedState<D> {
    fn assume(&mut self, m: &Match) {
        let mut new_partitions = Vec::new();
        let bdd_cond = self.control.borrow_mut().get_bdd(m);
        let bdd = &self.control.borrow().bdd;

        for (path, mut env) in self.partitions.drain(..) {
            // 1. Update Control: Add condition to path
            let new_path = bdd.apply_and(path, bdd_cond);

            if !bdd.is_false(new_path) {
                // 2. Update Data: Refine environment (if supported)
                // e.g., if match is "port < 1024", refine port to [0, 1023]
                env.refine(m);
                new_partitions.push((new_path, env));
            }
        }
        self.partitions = new_partitions;
    }
}
```

Now, when the analysis sees `if port < 1024`, it automatically learns that `port` is privileged in the true branch, even if the interval domain didn't know it before.

== The Interpreter Loop

Finally, let's see how this fits into the main analysis loop.
The `eval_rule` function takes a rule and updates the current state.

```rust
fn eval_rule<D: AbstractDomain>(rule: &Rule, state: &mut PartitionedState<D>) {
    match rule {
        Rule::ModField(field, val) => {
            // Update header state in all partitions
            state.assign(field, val);
        }
        Rule::Match(m, then_chain, else_chain) => {
            // 1. Clone state for branches
            let mut true_state = state.clone();
            let mut false_state = state.clone();

            // 2. Assume conditions
            true_state.assume(m);
            false_state.assume(&m.negate());

            // 3. Recurse
            eval_chain(then_chain, &mut true_state);
            eval_chain(else_chain, &mut false_state);

            // 4. Join results
            *state = true_state.join(&false_state);
        }
        // ... handle jumps ...
    }
}
```

This recursive structure naturally handles nested chains, while the `PartitionedState` manages the complexity of path conditions under the hood.

== Summary

Combining BDDs with abstract domains gives path-sensitive analysis:
- BDDs track feasible paths compactly
- Abstract domains track header field properties
- States are pairs $(b, rho)$: path condition + header environment

Operations:
- *Match:* Split state, update BDD path condition
- *Modify:* Update header environment, keep path condition
- *Join:* Merge BDDs with OR, join header domains

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
    BDD tracks which paths are feasible, domain tracks header values.

  - *BDD control domain allocates variables for packet matches.*
    Each boolean match (e.g., `tcp`) gets a unique BDD variable.

  - *Branching creates two states with updated path conditions.*
    True branch: $"path" and "match"$.
    False branch: $"path" and not "match"$.

  - *Modification updates data domain, keeps path unchanged.*
    Only header properties change on modification, not control flow.

  - *Joining merges paths with OR, joins data with domain operations.*
    Necessary at merge points but loses path-sensitivity.

  - *Trade-off between precision and state explosion.*
    Joining early: fast but imprecise. Joining late: precise but exponential states.

  - *Generic design works with any abstract domain.*
    Swap intervals for sets or prefix trees.
    BDD control layer is orthogonal.

  - *Path-sensitivity alone doesn't guarantee precision.*
    Need sufficiently precise data domains (intervals better than signs).

  - *Main insight:* BDDs provide compact representation of path conditions, enabling path-sensitive abstract interpretation without explicit path enumeration.
]
