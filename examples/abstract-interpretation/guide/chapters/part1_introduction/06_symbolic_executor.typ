#import "../../theme.typ": *

= A Complete Example: Symbolic Execution Engine <ch-symbolic-executor>

Theory and fragments are valuable, but nothing beats a complete working example.
This chapter implements a simple symbolic execution engine for IMP programs using BDDs, analyzing real programs, tracking execution flows symbolically, and detecting bugs like unreachable code.

== What is Symbolic Execution?

Symbolic execution runs programs with _symbolic_ inputs instead of concrete values.

Traditional execution:

```rust
fn check(x: i32) -> Status {
    if x > 0 { Safe } else { Error }
}
```

Symbolic execution:

```rust
// Symbolic: x is symbol α
// Path 1: α > 0 → Safe
// Path 2: α <= 0 → Error
```

Symbolic execution generates path conditions (Boolean formulas) and symbolic states.

#definition(title: "Symbolic Program Execution")[
  Symbolic execution simulates program flows with symbolic variables, maintaining:
  + *Path condition*: Boolean formula describing constraints on inputs to reach this point.
  + *Symbolic state*: Maps each variable to a symbolic expression or value set.
  + *Flow exploration*: Fork at branches to explore both true and false paths.
]

This implementation takes a hybrid approach: path conditions are represented compactly as BDDs instead of explicit formulas or constraint solvers.
Symbolic values remain as expressions, but path feasibility is tracked through BDD operations.
This combines symbolic execution precision with BDD-based path representation efficiency.

== Architecture Overview

+ *Condition Language:* Represent program conditions
+ *Symbolic State:* Path condition (BDD) + variable environment
+ *Program Walker:* Execute statements, update state
+ *Path Explorer:* Manage multiple paths, detect conflicts

This brings together everything we've learned --- abstract domains, BDDs, control flow, and path-sensitive analysis.
Study this implementation to see all the pieces working in harmony:

#example-reference(
  "symbolic_execution",
  "executor.rs",
  "symbolic_executor",
  [
    Complete symbolic execution engine implementation with statement evaluation, path branching, conflict checking, and bug detection.
    This is the culmination of all concepts from previous chapters working together in a production-ready system.
  ],
)

#figure(
  caption: [Symbolic executor architecture. The path explorer manages a worklist of symbolic states, each containing a BDD path condition and symbolic variable environment. The program walker processes statements, forking states at branches. Conflict detectors check for unreachable code by querying path feasibility.],

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
    draw-component((0, 3.2), 2.5, 0.8, [Path Explorer], colors.primary)
    draw-component((3.5, 3.2), 2.5, 0.8, [Program Walker], colors.accent)
    draw-component((6.5, 3.2), 2, 0.8, [Conflict Detector], colors.error)

    // Worklist of states
    content((1.25, 2.5), text(size: 0.75em, fill: colors.text-light)[Worklist:], anchor: "north")
    draw-data-box((0.2, 1.5), 2.1, 0.8, [Path 1])
    draw-data-box((0.2, 0.5), 2.1, 0.8, [Path 2])
    content((1.25, -0.1), text(size: 0.7em, fill: colors.text-light)[...], anchor: "north")

    // Symbolic state details
    content((4.75, 2.5), text(size: 0.75em, fill: colors.text-light)[Symbolic State:], anchor: "north")
    draw-data-box((3.5, 1.8), 2.5, 0.5, [Path: BDD])
    draw-data-box((3.5, 1.1), 2.5, 0.5, [Env: Var $->$ Val])

    // Connections
    draw-connection((1.25, 3.2), (4.75, 3.2))
    draw-connection((4.75, 3.2), (7.5, 3.2))
    draw-connection((2.3, 2.0), (3.5, 2.0))

    // Labels on connections
    content((2.5, 3.4), text(size: 0.65em, fill: colors.text-light)[pop path], anchor: "south")
    content((5.75, 3.4), text(size: 0.65em, fill: colors.text-light)[check], anchor: "south")
    content((2.5, 2.2), text(size: 0.65em, fill: colors.text-light)[current], anchor: "south")
  }),
) <fig:symbolic-executor-architecture>

== Condition Language

We use the AST defined in @ch-abstraction.

```rust
// Recall from Chapter 1:
// pub enum Var { X, Y, ... }
// pub struct Condition { var: Var, op: Op, val: i32 }
```

Example:

```rust
// x > 0
let c = Condition { var: Var::X, op: Op::Gt, val: 0 };
```

== Symbolic State

We reuse the `AnalysisManager` we built in @ch-combining-domains to manage our BDD variables.
This ensures that if we encounter `x > 0` in different parts of the program, they map to the same BDD variable.

```rust
use bdd_rs::{Bdd, Ref};
use std::rc::Rc;
use std::cell::RefCell;
use std::collections::HashMap;

// Recall AnalysisManager from Chapter 5
struct SymbolicState {
    ctx: Rc<RefCell<AnalysisManager>>,
    path: Ref,                           // Path condition (BDD)
    env: HashMap<Var, i32>,              // Var → Symbolic Value (simplified)
}

impl SymbolicState {
    fn new(ctx: Rc<RefCell<AnalysisManager>>) -> Self {
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

Evaluate modifications symbolically (e.g., assignments):

```rust
impl SymbolicState {
    fn assign(&mut self, var: Var, value: i32) {
        // In a real symbolic executor, value would be an expression
        self.env.insert(var, value);
    }
}
```

Example:

```rust
let mut state = SymbolicState::new(Rc::new(Bdd::default()));

// x = 10
state.assign(Var::X, 10);
```

== Branching

When encountering an `If` statement, we split execution.
We first evaluate the condition to its symbolic form, then check if we've seen it before.

```rust
impl SymbolicState {
    fn branch(&mut self, c: &Condition) -> SymbolicState {
        // 1. Get canonical BDD from manager
        // The manager ensures that identical conditions map to the same BDD node
        let cond_bdd = self.ctx.borrow_mut().get_bdd(c);
        let bdd = &self.ctx.borrow().bdd;

        // True path: path ∧ cond
        let true_path = bdd.apply_and(self.path, cond_bdd);
        let mut true_state = self.clone();
        true_state.path = true_path;

        // False path: path ∧ ¬cond
        let false_path = bdd.apply_and(self.path, bdd.apply_not(cond_bdd));
        let mut false_state = self.clone();
        false_state.path = false_path;

        // Update self to true branch, return false branch
        *self = true_state;
        false_state
    }
}
```

By using `AnalysisManager`, we ensure identical conditions map to the same BDD variable.
This lets the BDD deduce that a repeated check (e.g., `if x > 0` twice) is redundant.

#figure(
  caption: [Flow forking at branches. Starting from an initial state, each `Condition` allocates a fresh BDD variable and splits into two states. The true branch updates the path with $(p and c)$, the false branch with $(p and not c)$ where $p$ is the current path condition. Both branches inherit the symbolic environment.],

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
    draw-exec-state((0, 3), [Path: $top$], [x: $alpha$])
    content((-1.5, 3), text(size: 0.7em, fill: colors.text-light)[Initial], anchor: "east")

    // First condition
    draw-condition((0, 1.8), $c_1$)
    line((0, 2.5), (0, 2.1), stroke: colors.primary + 1pt, mark: (end: ">"))

    // First fork
    draw-exec-state((-2.5, 0.5), [Path: $c_1$], [x: $alpha$])
    draw-exec-state((2.5, 0.5), [Path: $not c_1$], [x: $alpha$])

    draw-fork-edge((0, 1.5), (-2.5, 1.0), is-true: true)
    draw-fork-edge((0, 1.5), (2.5, 1.0), is-true: false)

    content((-1, 1.2), text(size: 0.6em, fill: colors.success)[true], anchor: "south")
    content((1, 1.2), text(size: 0.6em, fill: colors.error)[false], anchor: "south")

    // Second conditions on branches
    draw-condition((-2.5, -0.7), $c_2$)
    line((-2.5, 0), (-2.5, -0.4), stroke: colors.primary + 1pt, mark: (end: ">"))

    draw-condition((2.5, -0.7), $c_3$)
    line((2.5, 0), (2.5, -0.4), stroke: colors.primary + 1pt, mark: (end: ">"))

    // Final states
    draw-exec-state((-4, -2), [Path: $c_1 and c_2$], [x: $alpha$])
    draw-exec-state((-1, -2), [Path: $c_1 and not c_2$], [x: $alpha$])
    draw-exec-state((1.5, -2), [Path: $not c_1 and c_3$], [x: $alpha$])
    draw-exec-state((4, -2), [Path: $not c_1 and not c_3$], [x: $alpha$])

    // Fork edges to final states
    draw-fork-edge((-2.5, -1.0), (-4, -1.5), is-true: true)
    draw-fork-edge((-2.5, -1.0), (-1, -1.5), is-true: false)
    draw-fork-edge((2.5, -1.0), (1.5, -1.5), is-true: true)
    draw-fork-edge((2.5, -1.0), (4, -1.5), is-true: false)

    // Annotation
    content(
      (0, -2.8),
      text(size: 0.7em, fill: colors.text-light, style: "italic")[4 paths explored],
      anchor: "north",
    )
  }),
) <fig:path-forking>

== Program Representation

We use the `Stmt` enum from @ch-abstraction.

```rust
// Recall from Chapter 1:
// pub enum Stmt {
//     If(Condition, Box<Stmt>, Box<Stmt>), // if cond then ... else ...
//     Assign(Var, i32),
//     Seq(Box<Stmt>, Box<Stmt>),
//     ...
// }
```

== Program Walker

Execute statements, tracking symbolic state:

```rust
struct ProgramWalker {
    ctx: Rc<RefCell<AnalysisManager>>,
}

impl ProgramWalker {
    fn new() -> Self {
        Self {
            ctx: Rc::new(RefCell::new(AnalysisManager::new())),
        }
    }

    fn execute(&self, stmt: &Stmt) -> Vec<SymbolicState> {
        let initial = SymbolicState::new(self.ctx.clone());
        self.execute_stmt(stmt, initial)
    }

    fn execute_stmt(&self, stmt: &Stmt, mut state: SymbolicState) -> Vec<SymbolicState> {
        if !state.is_feasible() {
            return vec![];  // Dead path
        }

        match stmt {
            Stmt::Assign(var, val) => {
                state.assign(*var, *val);
                vec![state]
            }

            Stmt::Seq(s1, s2) => {
                let states = self.execute_stmt(s1, state);
                states.into_iter()
                    .flat_map(|s| self.execute_stmt(s2, s))
                    .collect()
            }

            Stmt::If(c, then_branch, else_branch) => {
                let false_state = state.branch(c);

                // Execute both branches
                let mut then_states = self.execute_stmt(then_branch, state);
                let mut else_states = self.execute_stmt(else_branch, false_state);

                then_states.append(&mut else_states);
                then_states
            }
        }
    }
}
```

== Conflict Detection

To detect bugs, we check for *Unreachable Code*.
If a statement is unreachable (its path condition is False), it is dead code.

```rust
impl ProgramWalker {
    // In a real implementation, this would be part of execute_stmt
    fn check_reachability(&self, state: &SymbolicState) -> Option<String> {
        if !state.is_feasible() {
             Some("Code is unreachable (Dead Code)".to_string())
        } else {
            None
        }
    }
}
```

#example-box(number: "6.1", title: "Dead Code Detection")[
  ```rust
  // Buggy program: Second check is redundant/dead
  let buggy_prog = Stmt::Seq(
      Box::new(Stmt::If(
          Condition { var: Var::X, op: Op::Gt, val: 0 }, // x > 0
          Box::new(Stmt::Skip),
          Box::new(Stmt::Skip),
      )),
      Box::new(Stmt::If(
          Condition { var: Var::X, op: Op::Gt, val: 0 }, // x > 0 again!
          Box::new(Stmt::Error), // Unreachable in else branch of first check!
          Box::new(Stmt::Skip),
      )),
  );

  // The walker would find that the path to the second check's branches is constrained by the first check.
  ```
]

== Complete Example: Simple Program

Analyze a simple program end-to-end:

```rust
fn program_example() {
    // Program:
    // if x > 0 {
    //     y = 1;
    // } else {
    //     y = 2;
    // }

    let prog = Stmt::If(
        Condition { var: Var::X, op: Op::Gt, val: 0 },
        Box::new(Stmt::Assign(Var::Y, 1)),
        Box::new(Stmt::Assign(Var::Y, 2)),
    );

    let walker = ProgramWalker::new();
    let final_states = walker.execute(&prog);

    println!("Number of final paths: {}", final_states.len());

    for (i, state) in final_states.iter().enumerate() {
        println!("\nPath {}:", i);
        println!("  Condition: {:?}", state.path);
        println!("  Variables:");
        for (var, val) in &state.env {
            println!("    {:?} = {}", var, val);
        }
    }
}
```

Output:

```
Number of final paths: 2

Path 0:
  Condition: [BDD node representing x > 0]
  Variables: {Y: 1}

Path 1:
  Condition: [BDD node representing x <= 0]
  Variables: {Y: 2}
```

Two paths, both feasible, covering the entire input space.

== Enhancements for Real Systems

This toy executor lacks features needed for production.
*Interval Analysis* handles ranges efficiently.
*Abstract domain integration* uses intervals or signs to refine paths.
*SMT solver integration* checks complex arithmetic constraints (e.g., `x + y > 10`).
*Loop handling* requires fixpoint iteration.
*Function calls* demand inter-procedural analysis.

For production:

```rust
// Integration with abstract domain
struct RefinedState<D: AbstractDomain> {
    path: Ref,
    symbolic_env: HashMap<Var, Expr>,
    abstract_env: HashMap<Var, D>,
}
```

#example-reference(
  "symbolic_execution",
  "verifier.rs",
  "verifier",
  [
    A complete verifier implementation that integrates the Interval abstract domain with BDD-based path sensitivity.
    This example demonstrates how to prove numeric properties (like bounds and safety) that the basic symbolic executor cannot handle.
  ],
)

#info-box(title: "Symbolic Execution vs Abstract Interpretation")[

  *Symbolic Execution*
  - Explores paths explicitly (or with BDDs)
  - Maintains precise symbolic variables
  - Uses SMT solvers for feasibility
  - Goal: Find specific input that crashes program

  *Abstract Interpretation*
  - Over-approximates all paths
  - Uses abstract domains (Intervals, Signs)
  - Guaranteed termination
  - Goal: Prove program correctness for *all* inputs

  *Hybrid approach*
  - BDDs for control flow
  - Abstract domains for data
  - Best of both worlds
]

== Practical Considerations

=== Path Explosion

Even with BDDs, deeply nested branches create explosion.
Mitigation strategies:
- Bound exploration depth
- Prioritize paths (heuristics)
- Merge similar paths aggressively (e.g., merge all error paths)

=== Variable Ordering

BDD size depends critically on the ordering of condition variables.

Strategies:
- Allocate variables in execution order
- Group related variables
- Use heuristics based on dependency graph

=== Performance

Symbolic execution is inherently expensive.

Optimization tips:
- Cache BDD operations (built-in)
- Prune infeasible paths early
- Use abstract domains to eliminate paths (e.g., if range analysis proves `x > 10`, don't explore `x < 5` branch)

== Real-World Applications

Symbolic execution sees widespread use in software verification.

Tools like *KLEE* and *Angr* use symbolic techniques to verify C/C++ binaries.
They can detect buffer overflows, null pointer dereferences, and dead code.
*Infer* uses abstract interpretation to find bugs in Java/C++ codebases at scale.

== Summary

Built a simple symbolic execution engine:
- Condition and Statement language
- Symbolic state with BDD path conditions
- Program Walker exploring all paths
- Basic conflict detection

Key takeaways:
- BDDs compactly represent path conditions
- Symbolic values track variable modifications
- Branching creates multiple states
- Real systems integrate abstract domains and SMT solvers

@part-i covered abstract interpretation, BDDs, and their combination.

#info-box(title: "Path Exploration Strategies")[
  The path explosion problem is fundamental.
  Different exploration strategies offer different trade-offs.
  See #inline-example("symbolic_execution", "path_exploration.rs", "path_exploration") for comparisons of DFS, BFS, and bounded depth strategies.
]

@part-ii dives deeper into mathematical foundations and advanced techniques.

#chapter-summary[
  - *Symbolic execution simulates program flows with symbolic variables.*
    Maintains path conditions and symbolic environments.

  - *Condition language models program logic.*
    Variables, operators, values.

  - *Symbolic state: path condition (BDD) + variable environment.*
    BDD tracks which inputs are feasible, environment maps variables to values.

  - *Branching allocates BDD variable and splits state.*
    True branch: path ∧ cond. False branch: path ∧ ¬cond.

  - *Program Walker executes statements, exploring all paths.*
    Assignments update environment, branches split states.

  - *Conflict detection checks for unreachable code.*
    Find paths where statements are dead.

  - *Enhancements for real systems:*
    Interval Analysis, abstract domain integration, SMT solvers, loops.

  - *Practical challenges: path explosion, variable ordering, performance.*
    Mitigate with bounded exploration, heuristics, pruning.

  - *Hybrid approach combines symbolic execution and abstract interpretation.*
    BDDs for control, abstract domains for data.

  - *Main insight:*
    BDD-based symbolic execution provides practical path-sensitive analysis by compactly representing path conditions while exploring feasible execution traces.
]
