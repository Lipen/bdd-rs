#import "../../theme.typ": *

= A Complete Example: Symbolic Executor <ch-symbolic-executor>

Theory and fragments are valuable, but nothing beats a complete working example.
This chapter implements a simple symbolic executor using BDDs and abstract interpretation.

This chapter will analyze real Rust functions, track path conditions symbolically, and detect bugs.

== What is Symbolic Execution?

Symbolic execution runs programs with _symbolic_ inputs instead of concrete values.

Traditional execution:

```rust
fn abs(x: i32) -> i32 {
    if x < 0 { -x } else { x }
}

// Concrete: abs(-5) = 5
```

Symbolic execution:

```rust
// Symbolic: x is symbol α
// Path 1: α < 0 → result = -α
// Path 2: α ≥ 0 → result = α
```

Symbolic execution generates path conditions (Boolean formulas) and symbolic expressions for outputs.

#definition(title: "Symbolic Execution")[
  Symbolic execution runs a program with symbolic inputs while maintaining three key elements.
  + The *path condition* is a Boolean formula describing the current execution path.
  + The *symbolic state* maps each variable to a symbolic expression.
  + During *path exploration*, we fork at branches to explore both possibilities.
]

This implementation takes a hybrid approach.
Rather than using explicit formulas or constraint solvers for path conditions, it represents them compactly as BDDs.
The symbolic values themselves remain as expressions, but the feasibility of paths is tracked through BDD operations.
This combines the precision of symbolic execution with the efficiency of BDD-based path representation explored in earlier chapters.

== Architecture Overview

Components:

+ *Expression language:* Represent program expressions
+ *Symbolic state:* Path condition (BDD) + symbolic environment
+ *Interpreter:* Execute statements, update state
+ *Path explorer:* Manage multiple paths, detect bugs

#figure(
  caption: [Symbolic executor architecture. The path explorer manages a worklist of symbolic states, each containing a BDD path condition and symbolic environment. The interpreter processes statements, forking states at branches. Bug detectors check for violations by querying path feasibility.],

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
    draw-component((3.5, 3.2), 2.5, 0.8, [Interpreter], colors.accent)
    draw-component((6.5, 3.2), 2, 0.8, [Bug Detector], colors.error)

    // Worklist of states
    content((1.25, 2.5), text(size: 0.75em, fill: colors.text-light)[Worklist:], anchor: "north")
    draw-data-box((0.2, 1.5), 2.1, 0.8, [State 1])
    draw-data-box((0.2, 0.5), 2.1, 0.8, [State 2])
    content((1.25, -0.1), text(size: 0.7em, fill: colors.text-light)[...], anchor: "north")

    // Symbolic state details
    content((4.75, 2.5), text(size: 0.75em, fill: colors.text-light)[Symbolic State:], anchor: "north")
    draw-data-box((3.5, 1.8), 2.5, 0.5, [Path: BDD])
    draw-data-box((3.5, 1.1), 2.5, 0.5, [Env: Var $->$ Expr])

    // Connections
    draw-connection((1.25, 3.2), (4.75, 3.2))
    draw-connection((4.75, 3.2), (7.5, 3.2))
    draw-connection((2.3, 2.0), (3.5, 2.0))

    // Labels on connections
    content((2.5, 3.4), text(size: 0.65em, fill: colors.text-light)[pop state], anchor: "south")
    content((5.75, 3.4), text(size: 0.65em, fill: colors.text-light)[check], anchor: "south")
    content((2.5, 2.2), text(size: 0.65em, fill: colors.text-light)[current], anchor: "south")
  }),
) <fig:symbolic-executor-architecture>

== Expression Language

We use the IMP language AST defined in @ch-abstraction.

```rust
// Recall from Chapter 1:
// pub enum Expr {
//     Var(String),
//     Const(i32),
//     Add(Box<Expr>, Box<Expr>),
//     ...
// }
//
// pub enum Cond {
//     Lt(Expr, Expr),
//     ...
// }
```

Example:

```rust
// x + (-y)
let expr = Expr::Add(
    Box::new(Expr::Var("x".into())),
    Box::new(Expr::Sub(Box::new(Expr::Const(0)), Box::new(Expr::Var("y".into())))), // -y as 0-y
);
```

== Symbolic State

We reuse the `ConditionManager` we built in @ch-combining-domains to manage our BDD variables.
This ensures that if we encounter `x > 0` in different parts of the execution, they map to the same BDD variable.

```rust
use bdd_rs::{Bdd, Ref};
use std::rc::Rc;
use std::cell::RefCell;
use std::collections::HashMap;

// Recall ConditionManager from Chapter 5
struct SymbolicState {
    ctx: Rc<RefCell<ConditionManager>>,
    path: Ref,                           // Path condition (BDD)
    env: HashMap<String, Expr>,          // Variable → symbolic expression
}

impl SymbolicState {
    fn new(ctx: Rc<RefCell<ConditionManager>>) -> Self {
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

== Assignments and Expressions

Evaluate expressions symbolically:

```rust
impl SymbolicState {
    fn eval(&self, expr: &Expr) -> Expr {
        match expr {
            Expr::Const(_) => expr.clone(),
            Expr::Var(name) => {
                self.env.get(name).cloned().unwrap_or_else(|| Expr::var(name))
            }
            Expr::Add(lhs, rhs) => {
                Expr::add(self.eval(lhs), self.eval(rhs))
            }
            Expr::Sub(lhs, rhs) => {
                Expr::sub(self.eval(lhs), self.eval(rhs))
            }
            Expr::Neg(e) => {
                Expr::neg(self.eval(e))
            }
        }
    }

    fn assign(&mut self, var: &str, expr: Expr) {
        let value = self.eval(&expr);
        self.env.insert(var.to_string(), value);
    }
}
```

Example:

```rust
let mut state = SymbolicState::new(Rc::new(Bdd::default()));

// x = 5
state.assign("x", Expr::Const(5));

// y = x + 3
state.assign("y", Expr::add(Expr::var("x"), Expr::Const(3)));

// y is now bound to (5 + 3)
println!("{:?}", state.env.get("y"));  // Add(Const(5), Const(3))
```

For a real system, simplify expressions (constant folding, etc.).

== Branching

When encountering an `if`, we must split execution.
Crucially, we first *evaluate* the condition to its symbolic form, then check if we've seen it before.

```rust
impl SymbolicState {
    fn branch(&mut self, condition: &Cond) -> SymbolicState {
        // 1. Evaluate condition to symbolic form (e.g., "x < 0" becomes "α < 0")
        let sym_cond = self.eval_cond(condition);

        // 2. Get canonical BDD from manager
        // The manager ensures that identical symbolic conditions map to the same BDD node
        let cond_bdd = self.ctx.borrow_mut().get_bdd(&sym_cond);
        let bdd = &self.ctx.borrow().bdd;

        // True path: path ∧ condition
        let true_path = bdd.apply_and(self.path, cond_bdd);
        let mut true_state = self.clone();
        true_state.path = true_path;

        // False path: path ∧ ¬condition
        let false_path = bdd.apply_and(self.path, bdd.apply_not(cond_bdd));
        let mut false_state = self.clone();
        false_state.path = false_path;

        // Update self to true branch, return false branch
        *self = true_state;
        false_state
    }
}
```

By using the `ConditionManager`, we ensure that if the program checks `if x > 0` twice (and `x` hasn't changed), we use the same BDD variable. This allows the BDD to automatically deduce that the second check is redundant!

#figure(
  caption: [Path forking at conditional branches. Starting from an initial state, each `if` condition allocates a fresh BDD variable and splits into two states. The true branch updates the path with $(p and c)$, the false branch with $(p and not c)$ where $p$ is the current path condition. Both branches inherit the symbolic environment, which may be refined based on the learned condition.],

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
    draw-exec-state((0, 3), [Path: $top$], [`x`: $alpha$])
    content((-1.5, 3), text(size: 0.7em, fill: colors.text-light)[Initial], anchor: "east")

    // First condition
    draw-condition((0, 1.8), $c_1$)
    line((0, 2.5), (0, 2.1), stroke: colors.primary + 1pt, mark: (end: ">"))

    // First fork
    draw-exec-state((-2.5, 0.5), [Path: $c_1$], [`x`: $alpha$])
    draw-exec-state((2.5, 0.5), [Path: $not c_1$], [`x`: $alpha$])

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
    draw-exec-state((-4, -2), [Path: $c_1 and c_2$], [`x`: $alpha$])
    draw-exec-state((-1, -2), [Path: $c_1 and not c_2$], [`x`: $alpha$])
    draw-exec-state((1.5, -2), [Path: $not c_1 and c_3$], [`x`: $alpha$])
    draw-exec-state((4, -2), [Path: $not c_1 and not c_3$], [`x`: $alpha$])

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
//     Assign(String, Expr),
//     Seq(Box<Stmt>, Box<Stmt>),
//     If(Cond, Box<Stmt>, Box<Stmt>),
//     Assert(Cond),
//     ...
// }
```

Example:

```rust
// fn test(x: i32) -> i32 {
//     let mut result = 0;
//     if x < 0 {
//         result = -x;
//     } else {
//         result = x;
//     }
//     assert!(result >= 0);
//     result
// }

let program = Stmt::Seq(
    Box::new(Stmt::Assign("result".into(), Expr::Const(0))),
    Box::new(Stmt::Seq(
        Box::new(Stmt::If(
            Cond::Lt(Expr::Var("x".into()), Expr::Const(0)),
            Box::new(Stmt::Assign("result".into(), Expr::Sub(Box::new(Expr::Const(0)), Box::new(Expr::Var("x".into()))))),
            Box::new(Stmt::Assign("result".into(), Expr::Var("x".into()))),
        )),
        Box::new(Stmt::Assert(
            Cond::Le(Expr::Const(0), Expr::Var("result".into())),
        )),
    )),
);
```

== Interpreter

Execute statements, tracking symbolic state:

```rust
struct Interpreter {
    ctx: Rc<RefCell<ConditionManager>>,
}

impl Interpreter {
    fn new() -> Self {
        Self {
            ctx: Rc::new(RefCell::new(ConditionManager::new())),
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
            Stmt::Assign(var, expr) => {
                state.assign(var, expr.clone());
                vec![state]
            }

            Stmt::Seq(s1, s2) => {
                let states = self.execute_stmt(s1, state);
                states.into_iter()
                    .flat_map(|s| self.execute_stmt(s2, s))
                    .collect()
            }

            Stmt::If(cond, then_branch, else_branch) => {
                let false_state = state.branch(cond);

                // Execute both branches
                let mut then_states = self.execute_stmt(then_branch, state);
                let mut else_states = self.execute_stmt(else_branch, false_state);

                then_states.append(&mut else_states);
                then_states
            }

            Stmt::Assert(cond) => {
                // Check if assertion could fail
                // For now, just continue (bug detection below)
                vec![state]
            }

            Stmt::Skip => vec![state],

            Stmt::While(_, _) => {
                // Loop handling is complex (requires fixpoint or unrolling).
                // For this simple executor, we treat it as a no-op or error.
                vec![state]
            }
        }
    }
}
```

== Bug Detection

To detect bugs, we check assertions during execution.
When the interpreter encounters `Stmt::Assert(cond)`, it should verify that `cond` holds for all current paths.

```rust
impl Interpreter {
    // In a real implementation, this would be part of execute_stmt
    fn check_assertion(&self, state: &SymbolicState, cond: &Cond) -> Option<String> {
        // 1. Evaluate condition in current state
        // 2. Check if !cond is feasible (satisfiable)
        // If feasible, we have a bug!

        if state.is_feasible() {
             // Simplified check
             Some("Assertion might fail".to_string())
        } else {
            None
        }
    }
}
```

For a complete implementation, evaluate condition and check satisfiability.

#example-box(number: "6.1", title: "Simple Bug Detection")[
  ```rust
  // Buggy function: forgets to handle x=0
  let buggy_program = Stmt::Seq(
      Box::new(Stmt::If(
          Cond::Lt(Expr::Var("x".into()), Expr::Const(0)),
          Box::new(Stmt::Assign("result".into(), Expr::Const(-1))),
          Box::new(Stmt::Assign("result".into(), Expr::Const(1))),
      )),
      Box::new(Stmt::Assert(Cond::Eq(Expr::Var("result".into()), Expr::Const(0)))),
  );

  // Running the interpreter would flag the assertion failure on the x=0 path.
  ```
]

== Complete Example: Absolute Value

Let's analyze the absolute value function end-to-end.

```rust
fn abs_example() {
    // Program:
    // if x < 0 {
    //     result = -x;
    // } else {
    //     result = x;
    // }
    // assert!(result >= 0);

    let program = Stmt::Seq(
        Box::new(Stmt::If(
            Cond::Lt(Expr::Var("x".into()), Expr::Const(0)),
            Box::new(Stmt::Assign("result".into(), Expr::Neg(Box::new(Expr::Var("x".into()))))),
            Box::new(Stmt::Assign("result".into(), Expr::Var("x".into()))),
        )),
        Box::new(Stmt::Assert(
            Cond::Le(Expr::Const(0), Expr::Var("result".into())),
        )),
    );

    let interp = Interpreter::new();
    let final_states = interp.execute(&program);

    println!("Number of final states: {}", final_states.len());

    for (i, state) in final_states.iter().enumerate() {
        println!("\nState {}:", i);
        println!("  Path: {:?}", state.path);
        println!("  Environment:");
        for (var, expr) in &state.env {
            println!("    {} = {:?}", var, expr);
        }
    }
}
```

Output:

```
Number of final states: 2

State 0:
  Path: [BDD node representing x < 0]
  Environment:
    result = Neg(Var("x"))

State 1:
  Path: [BDD node representing x ≥ 0]
  Environment:
    result = Var("x")
```

Two paths, both feasible, both satisfy assertion (if checked properly).

== Enhancements for Real Systems

This toy executor lacks several features needed for production use.
It needs *expression simplification* through constant folding and algebraic simplification.
*Abstract domain integration* would let us use intervals or signs to refine paths.
*SMT solver integration* is essential for checking path feasibility and assertion violations.
*Loop handling* requires either bounded unrolling or fixpoint iteration.
*Function calls* demand inlining or summary-based analysis.
Finally, a proper *memory model* must handle pointers and heap allocation.

For production:

```rust
// Integration with abstract domain
struct RefinedState<D: AbstractDomain> {
    path: Ref,
    symbolic_env: HashMap<String, Expr>,
    abstract_env: HashMap<String, D>,
}

// Integration with SMT solver
fn check_sat(bdd: Ref, cond: &Cond) -> bool {
    // Convert BDD + cond to SMT formula
    // Query solver
    true  // Placeholder
}
```

#info-box(title: "Symbolic Execution vs Abstract Interpretation")[
  *Symbolic Execution:*
  - Explores paths explicitly (or with BDDs)
  - Maintains precise symbolic expressions
  - Uses SMT solvers for feasibility
  - Goal: Find bugs, generate tests

  *Abstract Interpretation:*
  - Over-approximates all behaviors
  - Uses abstract domains (signs, intervals)
  - Guaranteed termination (with widening)
  - Goal: Prove properties, verify correctness

  *Hybrid approach:*
  - BDDs for path conditions (from SE)
  - Abstract domains for data (from AI)
  - Best of both worlds
]

== Practical Considerations

=== Path Explosion

Even with BDDs, deeply nested branches create explosion.

Mitigation strategies:
- Bound exploration depth
- Prioritize paths (heuristics)
- Merge similar paths aggressively

=== Variable Ordering

BDD size depends critically on the ordering of condition variables.

Strategies:
- Allocate variables in program order
- Group related conditions
- Use heuristics based on control flow structure

=== Performance

Symbolic execution is inherently expensive.

Optimization tips:
- Cache BDD operations (built-in)
- Prune infeasible paths early
- Use abstract domains to eliminate paths (e.g., if sign analysis proves x > 0, don't explore x < 0 branch)

== Real-World Applications

Symbolic execution sees widespread use across several domains.

For bug finding, tools like KLEE, S2E, and Mayhem automatically find crashes and security vulnerabilities while generating test cases.
In verification, systems like Why3 and Frama-C prove program correctness, often combining symbolic execution with abstract interpretation.
Concolic testing tools such as SAGE and DART provide hybrid concrete and symbolic execution, using symbolic constraints to guide concrete execution.
For smart contract verification, analyzers like Mythril and Manticore examine Ethereum smart contracts to detect vulnerabilities like reentrancy and integer overflow.

== Summary

The chapter built a simple symbolic executor:
- Expression and statement language
- Symbolic state with BDD path conditions
- Interpreter exploring all paths
- Basic assertion checking

Key takeaways:
- BDDs compactly represent path conditions
- Symbolic values track expressions (not just abstract properties)
- Branching creates multiple states
- Real systems integrate abstract domains and SMT solvers

This completes @part-i: Foundations.
@part-i covered abstract interpretation, BDDs, and their combination.

@part-ii dives deeper into mathematical foundations and advanced techniques.

#chapter-summary(
  [
    *Symbolic execution runs programs with symbolic inputs.*
    Maintains path conditions and symbolic expressions for variables.
  ],
  [
    *Expression language models program syntax.*
    Variables, constants, arithmetic operations, conditions.
  ],
  [
    *Symbolic state: path condition (BDD) + symbolic environment.*
    BDD tracks which paths are feasible, environment maps variables to expressions.
  ],
  [
    *Branching allocates BDD variable and splits state.*
    True branch: path ∧ condition. False branch: path ∧ ¬condition.
  ],
  [
    *Interpreter executes statements, exploring all paths.*
    Assignments update environment, branches split states, assertions checked.
  ],
  [
    *Bug detection checks assertion violations.*
    Find paths where assertions could fail.
  ],
  [
    *Enhancements for real systems:*
    Expression simplification, abstract domain integration, SMT solvers, loops, functions.
  ],
  [
    *Practical challenges: path explosion, variable ordering, performance.*
    Mitigate with bounded exploration, heuristics, pruning.
  ],
  [
    *Hybrid approach combines symbolic execution and abstract interpretation.*
    BDDs for control, abstract domains for data. Best of both worlds.
  ],
  [
    *Main insight:*
    BDD-based symbolic execution provides practical path-sensitive analysis by compactly representing path conditions while exploring feasible program paths.
  ],
)

#pagebreak()

// Part I Complete!
// Part II would start here with more advanced topics
