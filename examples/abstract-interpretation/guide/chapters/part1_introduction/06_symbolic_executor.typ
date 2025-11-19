#import "../../theme.typ": *

= A Complete Example: Symbolic Executor <symbolic-executor-example>

Theory and fragments are valuable, but nothing beats a complete working example.
This chapter implements a simple symbolic executor using BDDs and abstract interpretation.

We'll analyze real Rust functions, track path conditions symbolically, and detect bugs.

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

We generate path conditions (Boolean formulas) and symbolic expressions for outputs.

#definition(title: "Symbolic Execution")[
  Execute a program with symbolic inputs, maintaining:
  - *Path condition:* Boolean formula describing current path
  - *Symbolic state:* Mapping variables to symbolic expressions
  - *Path exploration:* Fork at branches, explore both paths
]

Our twist: use BDDs for path conditions and abstract domains for symbolic values.

== Architecture Overview

Components:

1. *Expression language:* Represent program expressions
2. *Symbolic state:* Path condition (BDD) + symbolic environment
3. *Interpreter:* Execute statements, update state
4. *Path explorer:* Manage multiple paths, detect bugs

[Architecture diagram would go here]

== Expression Language

Model simple expressions:

```rust
#[derive(Debug, Clone, PartialEq, Eq)]
enum Expr {
    Const(i32),
    Var(String),
    Add(Box<Expr>, Box<Expr>),
    Sub(Box<Expr>, Box<Expr>),
    Neg(Box<Expr>),
}

impl Expr {
    fn var(name: &str) -> Self {
        Expr::Var(name.to_string())
    }

    fn add(lhs: Expr, rhs: Expr) -> Self {
        Expr::Add(Box::new(lhs), Box::new(rhs))
    }

    fn sub(lhs: Expr, rhs: Expr) -> Self {
        Expr::Sub(Box::new(lhs), Box::new(rhs))
    }

    fn neg(e: Expr) -> Self {
        Expr::Neg(Box::new(e))
    }
}
```

Example:

```rust
// x + (-y)
let expr = Expr::add(
    Expr::var("x"),
    Expr::neg(Expr::var("y")),
);
```

Conditions:

```rust
#[derive(Debug, Clone, PartialEq, Eq)]
enum Cond {
    Lt(Expr, Expr),      // <
    Le(Expr, Expr),      // ≤
    Eq(Expr, Expr),      // =
    And(Box<Cond>, Box<Cond>),
    Or(Box<Cond>, Box<Cond>),
    Not(Box<Cond>),
}
```

Example:

```rust
// x < 0 ∧ y > 5
let cond = Cond::And(
    Box::new(Cond::Lt(Expr::var("x"), Expr::Const(0))),
    Box::new(Cond::Lt(Expr::Const(5), Expr::var("y"))),
);
```

== Symbolic State

State = path condition + symbolic bindings.

```rust
use bdd_rs::{Bdd, Ref};
use std::rc::Rc;
use std::collections::HashMap;

struct SymbolicState {
    bdd: Rc<Bdd>,
    path: Ref,                           // Path condition (BDD)
    env: HashMap<String, Expr>,          // Variable → symbolic expression
    next_cond_var: u32,                  // Next BDD variable ID
}

impl SymbolicState {
    fn new(bdd: Rc<Bdd>) -> Self {
        Self {
            bdd: bdd.clone(),
            path: bdd.mk_true(),
            env: HashMap::new(),
            next_cond_var: 1,
        }
    }

    fn is_feasible(&self) -> bool {
        self.path != self.bdd.mk_false()
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

When encountering an `if`, allocate a BDD variable and split paths:

```rust
impl SymbolicState {
    fn branch(&mut self, condition: &Cond) -> SymbolicState {
        // Allocate fresh BDD variable for this condition
        let cond_var = self.next_cond_var;
        self.next_cond_var += 1;

        let cond_bdd = self.bdd.mk_var(cond_var);

        // True path: path ∧ condition
        let true_path = self.bdd.apply_and(self.path, cond_bdd);
        let mut true_state = SymbolicState {
            bdd: self.bdd.clone(),
            path: true_path,
            env: self.env.clone(),
            next_cond_var: self.next_cond_var,
        };

        // False path: path ∧ ¬condition
        let false_path = self.bdd.apply_and(self.path, self.bdd.apply_not(cond_bdd));
        let mut false_state = SymbolicState {
            bdd: self.bdd.clone(),
            path: false_path,
            env: self.env.clone(),
            next_cond_var: self.next_cond_var,
        };

        // Refine states based on condition
        // (In real system: update env based on learned facts)
        // For now, just symbolic tracking

        // Update self to true branch, return false branch
        *self = true_state;
        false_state
    }
}
```

This is simplified; real symbolic execution would:
- Simplify expressions based on learned conditions
- Update abstract domains (e.g., if `x < 0`, mark x as negative)
- Prune infeasible paths

== Program Representation

Model simple imperative programs:

```rust
#[derive(Debug, Clone)]
enum Stmt {
    Assign(String, Expr),
    If(Cond, Vec<Stmt>, Vec<Stmt>),  // if-then-else
    Assert(Cond),
}

type Program = Vec<Stmt>;
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

let program = vec![
    Stmt::Assign("result".into(), Expr::Const(0)),
    Stmt::If(
        Cond::Lt(Expr::var("x"), Expr::Const(0)),
        vec![
            Stmt::Assign("result".into(), Expr::neg(Expr::var("x"))),
        ],
        vec![
            Stmt::Assign("result".into(), Expr::var("x")),
        ],
    ),
    Stmt::Assert(
        Cond::Le(Expr::Const(0), Expr::var("result")),
    ),
];
```

== Interpreter

Execute statements, tracking symbolic state:

```rust
struct Interpreter {
    bdd: Rc<Bdd>,
}

impl Interpreter {
    fn new() -> Self {
        Self {
            bdd: Rc::new(Bdd::default()),
        }
    }

    fn execute(&self, program: &[Stmt]) -> Vec<SymbolicState> {
        let initial = SymbolicState::new(self.bdd.clone());
        self.execute_on_state(program, initial)
    }

    fn execute_on_state(&self, program: &[Stmt], mut state: SymbolicState) -> Vec<SymbolicState> {
        if !state.is_feasible() {
            return vec![];  // Dead path
        }

        let mut current_states = vec![state];

        for stmt in program {
            current_states = current_states.into_iter()
                .flat_map(|s| self.execute_stmt(stmt, s))
                .collect();
        }

        current_states
    }

    fn execute_stmt(&self, stmt: &Stmt, mut state: SymbolicState) -> Vec<SymbolicState> {
        match stmt {
            Stmt::Assign(var, expr) => {
                state.assign(var, expr.clone());
                vec![state]
            }

            Stmt::If(cond, then_branch, else_branch) => {
                let false_state = state.branch(cond);

                // Execute both branches
                let mut then_states = self.execute_on_state(then_branch, state);
                let mut else_states = self.execute_on_state(else_branch, false_state);

                then_states.append(&mut else_states);
                then_states
            }

            Stmt::Assert(cond) => {
                // Check if assertion could fail
                // For now, just continue (bug detection below)
                vec![state]
            }
        }
    }
}
```

== Bug Detection

Check assertions:

```rust
impl Interpreter {
    fn check_assertions(&self, program: &[Stmt]) -> Vec<(String, SymbolicState)> {
        let states = self.execute(program);
        let mut bugs = Vec::new();

        for (idx, stmt) in program.iter().enumerate() {
            if let Stmt::Assert(cond) = stmt {
                for state in &states {
                    // Check if assertion could fail on this path
                    // (Simplified: real version would check if ¬cond is satisfiable)
                    if state.is_feasible() {
                        // Potentially buggy path
                        bugs.push((
                            format!("Assertion at statement {} might fail", idx),
                            state.clone(),
                        ));
                    }
                }
            }
        }

        bugs
    }
}
```

For a complete implementation, evaluate condition and check satisfiability.

#example-box(number: "6.1", title: "Simple Bug Detection")[
  ```rust
  // Buggy function: forgets to handle x=0
  let buggy_program = vec![
      Stmt::If(
          Cond::Lt(Expr::var("x"), Expr::Const(0)),
          vec![Stmt::Assign("result".into(), Expr::Const(-1))],
          vec![Stmt::Assign("result".into(), Expr::Const(1))],
      ),
      Stmt::Assert(Cond::Eq(Expr::var("result"), Expr::Const(0))),
  ];

  let interp = Interpreter::new();
  let bugs = interp.check_assertions(&buggy_program);

  println!("Found {} potential bugs", bugs.len());
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

    let program = vec![
        Stmt::If(
            Cond::Lt(Expr::var("x"), Expr::Const(0)),
            vec![
                Stmt::Assign("result".into(), Expr::neg(Expr::var("x"))),
            ],
            vec![
                Stmt::Assign("result".into(), Expr::var("x")),
            ],
        ),
        Stmt::Assert(
            Cond::Le(Expr::Const(0), Expr::var("result")),
        ),
    ];

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

Our toy executor lacks:

1. *Expression simplification:* Constant folding, algebraic simplification
2. *Abstract domain integration:* Use intervals/signs to refine paths
3. *SMT solver integration:* Check path feasibility and assertion violations
4. *Loop handling:* Bounded unrolling or fixpoint iteration
5. *Function calls:* Inlining or summary-based analysis
6. *Memory model:* Pointers, heap allocation

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

Even with BDDs, deeply nested branches explode.

Mitigation:
- Bound exploration depth
- Prioritize paths (heuristics)
- Merge similar paths aggressively

=== Variable Ordering

BDD size depends on ordering of condition variables.

Strategy:
- Allocate variables in program order
- Group related conditions
- Use heuristics based on control flow structure

=== Performance

Symbolic execution is expensive.

Tips:
- Cache BDD operations (built-in)
- Prune infeasible paths early
- Use abstract domains to eliminate paths (e.g., if sign analysis proves x > 0, don't explore x < 0 branch)

== Real-World Applications

Symbolic execution is used in:

*Bug finding:* KLEE, S2E, Mayhem
- Automatically find crashes, security vulnerabilities
- Generate test cases

*Verification:* Why3, Frama-C
- Prove program correctness
- Often combined with abstract interpretation

*Concolic testing:* SAGE, DART
- Hybrid concrete + symbolic execution
- Guide concrete execution with symbolic constraints

*Smart contract verification:* Mythril, Manticore
- Analyze Ethereum smart contracts
- Detect vulnerabilities (reentrancy, overflow)

== Summary

We built a simple symbolic executor:
- Expression and statement language
- Symbolic state with BDD path conditions
- Interpreter exploring all paths
- Basic assertion checking

Key takeaways:
- BDDs compactly represent path conditions
- Symbolic values track expressions (not just abstract properties)
- Branching creates multiple states
- Real systems integrate abstract domains and SMT solvers

This completes Part I: Foundations.
We've covered abstract interpretation, BDDs, and their combination.

Part II dives deeper into practical analysis techniques.

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
    *Main Insight:*
    BDD-based symbolic execution provides practical path-sensitive analysis by compactly representing path conditions while exploring feasible program paths.
  ],
)

#pagebreak()

// Part I Complete!
// Part II would start here with more advanced topics
