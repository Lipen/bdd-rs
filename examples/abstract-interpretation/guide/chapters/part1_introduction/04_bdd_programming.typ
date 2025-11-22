#import "../../theme.typ": *

= Implementing the Engine: The `ConditionManager` <ch-bdd-programming>

We have the theory: BDDs represent sets of paths.
Now we build the engine.

Our first task is to implement the *`ConditionManager`*.
This component translates the language of our program (strings like "x > 0") into the language of BDDs (variables like 1, 2, 3).

== Setting Up the Project

First, let's create a new Rust project for our MiniVerifier.

```bash
cargo new miniverifier
cd miniverifier
cargo add bdd-rs
```

We will use `bdd-rs` for all Boolean manipulation.

== The `bdd-rs` Crash Course

Before we build the manager, let's understand the tools we have.
The `bdd-rs` library has a *manager-centric* design.

```rust
use bdd_rs::{Bdd, Ref};

fn main() {
    let mut bdd = Bdd::new();

    // 1. Create variables (must be 1-indexed!)
    let var1 = bdd.mk_var(1);
    let var2 = bdd.mk_var(2);

    // 2. Combine them
    let both = bdd.apply_and(var1, var2); // var1 AND var2
    let either = bdd.apply_or(var1, var2); // var1 OR var2

    // 3. Check results
    println!("Both: {:?}", both);
}
```

#warning-box[
  *Important Invariant:*
  You never operate on `Ref` directly (e.g., `x.and(y)` is wrong).
  You always ask the manager to do it: `bdd.apply_and(x, y)`.
  The manager owns the nodes and ensures uniqueness.
]

Understanding why this manager-centric design is essential requires looking at the internal mechanisms of hash consing and computed caches.
The following example provides a deep dive into the manager's architecture:

#example-reference(
  "bdd_fundamentals",
  "manager_demo.rs",
  "bdd_manager",
  [
    Deep dive into BDD manager architecture: hash consing, computed cache, and why all operations must go through the manager.
    Essential for understanding the performance characteristics of BDDs.
  ],
)

== Designing the `ConditionManager`

We need a struct that holds:
+ The `Bdd` manager itself.
+ A mapping from `Cond` (our AST node) to BDD variable IDs.
+ A counter to assign new IDs.

```rust
use std::collections::HashMap;
use bdd_rs::{Bdd, Ref};
// Assuming Cond is defined as in Chapter 1
use crate::ast::Cond;

pub struct ConditionManager {
    bdd: Bdd,
    mapping: HashMap<Cond, usize>,
    next_var_id: usize,
}

impl ConditionManager {
    pub fn new() -> Self {
        Self {
            bdd: Bdd::new(),
            mapping: HashMap::new(),
            next_var_id: 1, // Start at 1! 0 is reserved.
        }
    }
}
```

== Allocating Conditions

The core method is `get_condition`.
It takes a `Cond` and returns a BDD `Ref`.

If we've seen this condition before, return the existing variable.
If not, create a new one.

```rust
impl ConditionManager {
    pub fn get_condition(&mut self, cond: &Cond) -> Ref {
        if let Some(&id) = self.mapping.get(cond) {
            // We've seen this condition before.
            // Return the BDD variable for it.
            return self.bdd.mk_var(id);
        }

        // New condition!
        let id = self.next_var_id;
        self.next_var_id += 1;

        self.mapping.insert(cond.clone(), id);
        self.bdd.mk_var(id)
    }
}
```

This simple logic guarantees that `x > 0` always maps to the same BDD variable, ensuring consistency across the entire analysis.

== Exposing BDD Operations

We also need to expose the BDD operations (AND, OR, NOT) so the rest of the engine can use them without touching the raw `Bdd` field directly.

```rust
impl ConditionManager {
    pub fn and(&mut self, a: Ref, b: Ref) -> Ref {
        self.bdd.apply_and(a, b)
    }

    pub fn or(&mut self, a: Ref, b: Ref) -> Ref {
        self.bdd.apply_or(a, b)
    }

    pub fn not(&mut self, a: Ref) -> Ref {
        self.bdd.apply_not(a)
    }

    pub fn true_ref(&self) -> Ref {
        self.bdd.mk_true()
    }

    pub fn false_ref(&self) -> Ref {
        self.bdd.mk_false()
    }
}
```

== Putting It Together

Let's test our manager with a simple scenario.

```rust
fn main() {
    let mut mgr = ConditionManager::new();

    // Encounter "x > 0"
    let x_gt_0 = Cond::Lt(Expr::Const(0), Expr::Var("x".into())); // 0 < x
    let c1 = mgr.get_condition(&x_gt_0);

    // Encounter "y < 5"
    let y_lt_5 = Cond::Lt(Expr::Var("y".into()), Expr::Const(5));
    let c2 = mgr.get_condition(&y_lt_5);

    // Path: x > 0 AND y < 5
    let path = mgr.and(c1, c2);

    // Encounter "x > 0" again!
    let c3 = mgr.get_condition(&x_gt_0);

    // Should be the same variable
    assert_eq!(c1, c3);
}
```

This `ConditionManager` is the foundation of our symbolic execution engine.
In the next chapter, we will use it to "execute" our Control Flow Graph.

#info-box(title: "Advanced BDD Topics")[
  For production BDD engines, two advanced topics are critical:

  - *Quantification* (∃, ∀): Projecting out variables
    - See #inline-example("bdd_advanced", "quantification.rs", "bdd_quantification")
  - *Variable Ordering*: The #1 factor affecting BDD size
    - See #inline-example("bdd_advanced", "variable_ordering.rs", "bdd_variable_ordering")

  Variable ordering can make the difference between tractable (linear nodes) and intractable (exponential nodes) for the same formula!
]

== Summary

- We set up a Rust project with `bdd-rs`.
- We implemented `ConditionManager` to map `Cond` AST nodes to BDD variables.
- We ensured that identical conditions map to identical variables (canonicalization).
- We exposed basic Boolean operations.

Next: *Symbolic Execution*. We will write the code that walks the CFG and builds these BDDs automatically.
