#import "../../theme.typ": *

= A Complete Example: Symbolic Firewall Checker <ch-symbolic-executor>

Theory and fragments are valuable, but nothing beats a complete working example.
This chapter implements a simple symbolic execution engine for firewall rules using BDDs.

This chapter will analyze real firewall chains, track packet flows symbolically, and detect configuration errors.

== What is Symbolic Execution?

Symbolic execution runs programs (or policies) with _symbolic_ inputs instead of concrete values.

Traditional packet filtering:

```rust
fn check(pkt: Packet) -> Action {
    if pkt.proto == TCP { Accept } else { Drop }
}

// Concrete: check(tcp_pkt) = Accept
```

Symbolic execution:

```rust
// Symbolic: pkt is symbol α
// Path 1: α.proto == TCP → Action = Accept
// Path 2: α.proto != TCP → Action = Drop
```

Symbolic execution generates path conditions (Boolean formulas) and symbolic states for packet headers.

#definition(title: "Symbolic Packet Execution")[
  Symbolic execution simulates packet flows with symbolic headers while maintaining three key elements.
  + The *path condition* is a Boolean formula describing the constraints on the packet to reach this point.
  + The *symbolic state* maps each header field to a symbolic expression or value set.
  + During *flow exploration*, we fork at match rules to explore both matching and non-matching packets.
]

This implementation takes a hybrid approach.
Rather than using explicit formulas or constraint solvers for path conditions, it represents them compactly as BDDs.
The symbolic values themselves remain as expressions, but the feasibility of paths is tracked through BDD operations.
This combines the precision of symbolic execution with the efficiency of BDD-based path representation explored in earlier chapters.

== Architecture Overview

Components:

+ *Match Language:* Represent packet matching rules
+ *Symbolic State:* Path condition (BDD) + header environment
+ *Chain Walker:* Execute rules, update state
+ *Flow Explorer:* Manage multiple paths, detect conflicts

This chapter brings together everything we've learned --- abstract domains, BDDs, control flow, and path-sensitive analysis --- into a complete symbolic execution engine.
Study this implementation to see all the pieces working in harmony:

#example-reference(
  "symbolic_execution",
  "executor.rs",
  "symbolic_executor",
  [
    Complete symbolic execution engine implementation with rule evaluation, path branching, conflict checking, and bug detection.
    This is the culmination of all concepts from previous chapters working together in a production-ready system.
  ],
)

#figure(
  caption: [Symbolic executor architecture. The flow explorer manages a worklist of symbolic states, each containing a BDD path condition and symbolic header environment. The chain walker processes rules, forking states at matches. Conflict detectors check for shadowing or redundancy by querying path feasibility.],

  cetz.canvas({
    import cetz.draw: *

    // Helper functions
    let draw-component(pos, width, height, label, color) = {
      rect(pos, (pos.at(0) + width, pos.at(1) + height), fill: colors.bg-code, stroke: color + 2pt, radius: 0.15)
      content((pos.at(0) + width / 2, pos.at(1) + height / 2), text(
        fill: color,
        weight: "bold",
        size: 0.8em,
      )[#label])
    }

    let draw-data-box(pos, width, height, label) = {
      rect(pos, (pos.at(0) + width, pos.at(1) + height), fill: white, stroke: colors.secondary + 1pt, radius: 0.08)
      content((pos.at(0) + width / 2, pos.at(1) + height - 0.2), text(size: 0.7em)[#label], anchor: "north")
    }

    let draw-connection(from-pos, to-pos) = {
      line(from-pos, to-pos, stroke: colors.primary + 1pt, mark: (end: ">"))
    }

    // Main components
    draw-component((0, 3.2), 2.5, 0.8, [Flow Explorer], colors.primary)
    draw-component((3.5, 3.2), 2.5, 0.8, [Chain Walker], colors.accent)
    draw-component((6.5, 3.2), 2, 0.8, [Conflict Detector], colors.error)

    // Worklist of states
    content((1.25, 2.5), text(size: 0.75em, fill: colors.text-light)[Worklist:], anchor: "north")
    draw-data-box((0.2, 1.5), 2.1, 0.8, [Flow 1])
    draw-data-box((0.2, 0.5), 2.1, 0.8, [Flow 2])
    content((1.25, -0.1), text(size: 0.7em, fill: colors.text-light)[...], anchor: "north")

    // Symbolic state details
    content((4.75, 2.5), text(size: 0.75em, fill: colors.text-light)[Symbolic State:], anchor: "north")
    draw-data-box((3.5, 1.8), 2.5, 0.5, [Path: BDD])
    draw-data-box((3.5, 1.1), 2.5, 0.5, [Env: Field $->$ Val])

    // Connections
    draw-connection((1.25, 3.2), (4.75, 3.2))
    draw-connection((4.75, 3.2), (7.5, 3.2))
    draw-connection((2.3, 2.0), (3.5, 2.0))

    // Labels on connections
    content((2.5, 3.4), text(size: 0.65em, fill: colors.text-light)[pop flow], anchor: "south")
    content((5.75, 3.4), text(size: 0.65em, fill: colors.text-light)[check], anchor: "south")
    content((2.5, 2.2), text(size: 0.65em, fill: colors.text-light)[current], anchor: "south")
  }),
) <fig:symbolic-executor-architecture>

== Match Language

We use the AST defined in @ch-abstraction.

```rust
// Recall from Chapter 1:
// pub enum HeaderField { SrcIp, DstPort, ... }
// pub enum Match { Exact(HeaderField, u32), ... }
```

Example:

```rust
// tcp.dst_port == 80
let m = Match::Exact(HeaderField::DstPort, 80);
```

== Symbolic State

We reuse the `FilterManager` we built in @ch-combining-domains to manage our BDD variables.
This ensures that if we encounter `tcp` in different parts of the policy, they map to the same BDD variable.

```rust
use bdd_rs::{Bdd, Ref};
use std::rc::Rc;
use std::cell::RefCell;
use std::collections::HashMap;

// Recall FilterManager from Chapter 5
struct SymbolicState {
    ctx: Rc<RefCell<FilterManager>>,
    path: Ref,                           // Path condition (BDD)
    env: HashMap<HeaderField, u32>,      // Field → Symbolic Value (simplified)
}

impl SymbolicState {
    fn new(ctx: Rc<RefCell<FilterManager>>) -> Self {
        let true_path = ctx.borrow().bdd.mk_true();
        Self {
            ctx,
            path: true_path,
            env: HashMap::new(),
        }
    }

    fn is_feasible(&self) -> bool {
        let bdd = &self.ctx.borrow().bdd;
        self.path != bdd.mk_false()
    }
}
```

== Modifications and Actions

Evaluate modifications symbolically (e.g., NAT):

```rust
impl SymbolicState {
    fn modify(&mut self, field: HeaderField, value: u32) {
        // In a real symbolic executor, value would be an expression
        self.env.insert(field, value);
    }
}
```

Example:

```rust
let mut state = SymbolicState::new(Rc::new(Bdd::default()));

// NAT: Set DstIp to 10.0.0.1
state.modify(HeaderField::DstIp, 0x0A000001);
```

== Branching

When encountering a `Match` rule, we must split execution.
Crucially, we first *evaluate* the match to its symbolic form, then check if we've seen it before.

```rust
impl SymbolicState {
    fn branch(&mut self, m: &Match) -> SymbolicState {
        // 1. Get canonical BDD from manager
        // The manager ensures that identical matches map to the same BDD node
        let match_bdd = self.ctx.borrow_mut().get_bdd(m);
        let bdd = &self.ctx.borrow().bdd;

        // True path: path ∧ match
        let true_path = bdd.apply_and(self.path, match_bdd);
        let mut true_state = self.clone();
        true_state.path = true_path;

        // False path: path ∧ ¬match
        let false_path = bdd.apply_and(self.path, bdd.apply_not(match_bdd));
        let mut false_state = self.clone();
        false_state.path = false_path;

        // Update self to true branch, return false branch
        *self = true_state;
        false_state
    }
}
```

By using the `FilterManager`, we ensure that if the policy checks `if tcp` twice, we use the same BDD variable.
This allows the BDD to automatically deduce that the second check is redundant!

#figure(
  caption: [Flow forking at match rules. Starting from an initial state, each `Match` allocates a fresh BDD variable and splits into two states. The true branch updates the path with $(p and m)$, the false branch with $(p and not m)$ where $p$ is the current path condition. Both branches inherit the symbolic environment.],

  cetz.canvas({
    import cetz.draw: *

    // Helper functions
    let draw-exec-state(pos, path-label, env-label) = {
      rect(
        (pos.at(0) - 1, pos.at(1) - 0.5),
        (pos.at(0) + 1, pos.at(1) + 0.5),
        fill: colors.bg-code,
        stroke: colors.primary + 1.5pt,
        radius: 0.1,
      )
      content((pos.at(0), pos.at(1) + 0.15), text(size: 0.65em)[#path-label])
      content((pos.at(0), pos.at(1) - 0.15), text(size: 0.65em, fill: colors.text-light)[#env-label])
    }

    let draw-condition(pos, cond-label) = {
      circle(pos, radius: 0.3, fill: white, stroke: colors.accent + 1.5pt)
      content(pos, text(size: 0.7em, fill: colors.accent)[#cond-label])
    }

    let draw-fork-edge(from-pos, to-pos, is-true: true) = {
      let color-choice = if is-true { colors.success } else { colors.error }
      line(from-pos, to-pos, stroke: color-choice + 1.5pt, mark: (end: ">"))
    }

    // Initial state
    draw-exec-state((0, 3), [Path: $top$], [ip: $alpha$])
    content((-1.5, 3), text(size: 0.7em, fill: colors.text-light)[Initial], anchor: "east")

    // First condition
    draw-condition((0, 1.8), $m_1$)
    line((0, 2.5), (0, 2.1), stroke: colors.primary + 1pt, mark: (end: ">"))

    // First fork
    draw-exec-state((-2.5, 0.5), [Path: $m_1$], [ip: $alpha$])
    draw-exec-state((2.5, 0.5), [Path: $not m_1$], [ip: $alpha$])

    draw-fork-edge((0, 1.5), (-2.5, 1.0), is-true: true)
    draw-fork-edge((0, 1.5), (2.5, 1.0), is-true: false)

    content((-1, 1.2), text(size: 0.6em, fill: colors.success)[match], anchor: "south")
    content((1, 1.2), text(size: 0.6em, fill: colors.error)[next], anchor: "south")

    // Second conditions on branches
    draw-condition((-2.5, -0.7), $m_2$)
    line((-2.5, 0), (-2.5, -0.4), stroke: colors.primary + 1pt, mark: (end: ">"))

    draw-condition((2.5, -0.7), $m_3$)
    line((2.5, 0), (2.5, -0.4), stroke: colors.primary + 1pt, mark: (end: ">"))

    // Final states
    draw-exec-state((-4, -2), [Path: $m_1 and m_2$], [ip: $alpha$])
    draw-exec-state((-1, -2), [Path: $m_1 and not m_2$], [ip: $alpha$])
    draw-exec-state((1.5, -2), [Path: $not m_1 and m_3$], [ip: $alpha$])
    draw-exec-state((4, -2), [Path: $not m_1 and not m_3$], [ip: $alpha$])

    // Fork edges to final states
    draw-fork-edge((-2.5, -1.0), (-4, -1.5), is-true: true)
    draw-fork-edge((-2.5, -1.0), (-1, -1.5), is-true: false)
    draw-fork-edge((2.5, -1.0), (1.5, -1.5), is-true: true)
    draw-fork-edge((2.5, -1.0), (4, -1.5), is-true: false)

    // Annotation
    content(
      (0, -2.8),
      text(size: 0.7em, fill: colors.text-light, style: "italic")[4 flows explored],
      anchor: "north",
    )
  }),
) <fig:path-forking>

== Policy Representation

We use the `Rule` enum from @ch-abstraction.

```rust
// Recall from Chapter 1:
// pub enum Rule {
//     Match(Match, Box<Rule>, Box<Rule>), // if match then ... else ...
//     ModField(HeaderField, u32),
//     Accept,
//     Drop,
//     Seq(Box<Rule>, Box<Rule>),
//     ...
// }
```

== Chain Walker

Execute rules, tracking symbolic state:

```rust
struct ChainWalker {
    ctx: Rc<RefCell<FilterManager>>,
}

impl ChainWalker {
    fn new() -> Self {
        Self {
            ctx: Rc::new(RefCell::new(FilterManager::new())),
        }
    }

    fn execute(&self, rule: &Rule) -> Vec<SymbolicState> {
        let initial = SymbolicState::new(self.ctx.clone());
        self.execute_rule(rule, initial)
    }

    fn execute_rule(&self, rule: &Rule, mut state: SymbolicState) -> Vec<SymbolicState> {
        if !state.is_feasible() {
            return vec![];  // Dead path
        }

        match rule {
            Rule::ModField(field, val) => {
                state.modify(*field, *val);
                vec![state]
            }

            Rule::Seq(r1, r2) => {
                let states = self.execute_rule(r1, state);
                states.into_iter()
                    .flat_map(|s| self.execute_rule(r2, s))
                    .collect()
            }

            Rule::Match(m, then_branch, else_branch) => {
                let false_state = state.branch(m);

                // Execute both branches
                let mut then_states = self.execute_rule(then_branch, state);
                let mut else_states = self.execute_rule(else_branch, false_state);

                then_states.append(&mut else_states);
                then_states
            }

            Rule::Accept | Rule::Drop => {
                // Terminal states
                vec![state]
            }
        }
    }
}
```

== Conflict Detection

To detect bugs, we check for *Shadowing* or *Redundancy*.
If a rule is unreachable (its path condition is False), it is shadowed.

```rust
impl ChainWalker {
    // In a real implementation, this would be part of execute_rule
    fn check_reachability(&self, state: &SymbolicState) -> Option<String> {
        if !state.is_feasible() {
             Some("Rule is unreachable (Shadowed)".to_string())
        } else {
            None
        }
    }
}
```

#example-box(number: "6.1", title: "Shadowing Detection")[
  ```rust
  // Buggy chain: Rule 1 shadows Rule 2
  let buggy_chain = Rule::Seq(
      Box::new(Rule::Match(
          Match::Exact(HeaderField::Proto, 6), // TCP
          Box::new(Rule::Accept),
          Box::new(Rule::Skip),
      )),
      Box::new(Rule::Match(
          Match::Exact(HeaderField::Proto, 6), // TCP again!
          Box::new(Rule::Drop), // Unreachable!
          Box::new(Rule::Skip),
      )),
  );

  // The walker would find that the path to the second TCP match is False (because we already handled TCP in the first rule's true branch, or if we are in the else branch, it's NOT TCP).
  ```
]

== Complete Example: Simple Firewall

Let's analyze a simple firewall chain end-to-end.

```rust
fn firewall_example() {
    // Policy:
    // if tcp {
    //     accept;
    // } else {
    //     drop;
    // }

    let policy = Rule::Match(
        Match::Exact(HeaderField::Proto, 6),
        Box::new(Rule::Accept),
        Box::new(Rule::Drop),
    );

    let walker = ChainWalker::new();
    let final_states = walker.execute(&policy);

    println!("Number of final flows: {}", final_states.len());

    for (i, state) in final_states.iter().enumerate() {
        println!("\nFlow {}:", i);
        println!("  Path: {:?}", state.path);
        println!("  Headers:");
        for (field, val) in &state.env {
            println!("    {:?} = {}", field, val);
        }
    }
}
```

Output:

```
Number of final flows: 2

Flow 0:
  Path: [BDD node representing proto == TCP]
  Headers: {} (Accept)

Flow 1:
  Path: [BDD node representing proto != TCP]
  Headers: {} (Drop)
```

Two flows, both feasible, covering the entire packet space.

== Enhancements for Real Systems

This toy executor lacks several features needed for production use.
It needs *Header Space Analysis* (HSA) to handle IP ranges and bitmasks efficiently.
*Abstract domain integration* would let us use intervals or prefix trees to refine paths.
*SMT solver integration* is essential for checking complex arithmetic constraints (e.g., packet length).
*Loop handling* (for routing loops) requires fixpoint iteration.
*Jump chains* demand inter-procedural analysis.

For production:

```rust
// Integration with abstract domain
struct RefinedState<D: AbstractDomain> {
    path: Ref,
    symbolic_env: HashMap<HeaderField, Expr>,
    abstract_env: HashMap<HeaderField, D>,
}
```

#info-box(title: "Symbolic Execution vs Abstract Interpretation")[

  *Symbolic Execution:*
  - Explores flows explicitly (or with BDDs)
  - Maintains precise symbolic headers
  - Uses SMT solvers for feasibility
  - Goal: Find specific packet that violates policy

  *Abstract Interpretation:*
  - Over-approximates all flows
  - Uses abstract domains (CIDR blocks, Port Ranges)
  - Guaranteed termination
  - Goal: Prove policy correctness for *all* packets

  *Hybrid approach:*
  - BDDs for control (ACLs)
  - Abstract domains for headers
  - Best of both worlds
]

== Practical Considerations

=== Path Explosion

Even with BDDs, deeply nested chains create explosion.

Mitigation strategies:
- Bound exploration depth
- Prioritize flows (heuristics)
- Merge similar flows aggressively (e.g., merge all TCP flows if they have same action)

=== Variable Ordering

BDD size depends critically on the ordering of match variables.

Strategies:
- Allocate variables in chain order
- Group related fields (IPs together, Ports together)
- Use heuristics based on protocol hierarchy

=== Performance

Symbolic execution is inherently expensive.

Optimization tips:
- Cache BDD operations (built-in)
- Prune infeasible paths early
- Use abstract domains to eliminate paths (e.g., if range analysis proves `port > 1024`, don't explore `port == 80` branch)

== Real-World Applications

Symbolic execution sees widespread use in network verification.

Tools like *Batfish* and *Hassel* (Header Space Analysis) use symbolic techniques to verify network configurations before deployment.
They can detect reachability holes, routing loops, and ACL shadowing.
*Veriflow* checks network invariants in real-time as rules change.
*P4* program verification often uses symbolic execution to ensure packet processing logic is correct.

== Summary

The chapter built a simple symbolic firewall checker:
- Match and Rule language
- Symbolic state with BDD path conditions
- Chain Walker exploring all flows
- Basic conflict detection

Key takeaways:
- BDDs compactly represent path conditions
- Symbolic values track header modifications
- Branching creates multiple states
- Real systems integrate abstract domains and SMT solvers

@part-i covered abstract interpretation, BDDs, and their combination.

#info-box(title: "Flow Exploration Strategies")[
  The path explosion problem is fundamental.
  Different exploration strategies offer different trade-offs.
  See #inline-example("symbolic_execution", "path_exploration.rs", "path_exploration") for comparisons of DFS, BFS, and bounded depth strategies.
]

@part-ii dives deeper into mathematical foundations and advanced techniques.

#chapter-summary[
  - *Symbolic execution simulates packet flows with symbolic headers.*
    Maintains path conditions and symbolic environments.

  - *Match language models firewall rules.*
    Fields, values, exact matches, ranges.

  - *Symbolic state: path condition (BDD) + header environment.*
    BDD tracks which packets are feasible, environment maps fields to values.

  - *Branching allocates BDD variable and splits state.*
    True branch: path ∧ match. False branch: path ∧ ¬match.

  - *Chain Walker executes rules, exploring all flows.*
    Modifications update environment, matches split states.

  - *Conflict detection checks for unreachable rules.*
    Find paths where rules are shadowed.

  - *Enhancements for real systems:*
    Header Space Analysis, abstract domain integration, SMT solvers, routing loops.

  - *Practical challenges: path explosion, variable ordering, performance.*
    Mitigate with bounded exploration, heuristics, pruning.

  - *Hybrid approach combines symbolic execution and abstract interpretation.*
    BDDs for control, abstract domains for data.

  - *Main insight:*
    BDD-based symbolic execution provides practical path-sensitive analysis by compactly representing path conditions while exploring feasible packet flows.
]
