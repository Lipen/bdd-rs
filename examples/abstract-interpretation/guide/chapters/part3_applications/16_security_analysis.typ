#import "../../theme.typ": *

= Security Analysis <ch-security>

#reading-path(path: "essential")

Security analysis is one of the most impactful applications of abstract interpretation.
By tracking the flow of information through a program, we can detect vulnerabilities like SQL injection, cross-site scripting (XSS), and information leaks.

== Taint Analysis

The core concept in security analysis is *taint tracking*.
Data coming from untrusted sources (user input, network) is marked as "tainted".
Data that is safe to use (constants, sanitized input) is "clean".

#definition(title: "Taint Domain")[
  The taint domain is a simple two-point lattice:
  $ D = \{ lbot, "Clean", "Tainted", ltop \} $
  where $"Clean" < "Tainted"$.
  - Sources (e.g., `read_input()`) return $"Tainted"$.
  - Sinks (e.g., `exec_sql()`) require $"Clean"$ arguments.
  - Sanitizers (e.g., `escape_sql()`) convert $"Tainted"$ to $"Clean"$.
]

== BDD-Guided Taint Analysis

Standard taint analysis is often path-insensitive, leading to false positives.
It might flag code as unsafe because it merges paths where data is sanitized with paths where it isn't.
BDDs allow us to track *under what conditions* a variable is tainted.

#example-box(title: "Conditional Sanitization")[
  Consider a common pattern where data is sanitized only if it looks dangerous:

  ```rust
  let x = read_user_input(); // x is Tainted
  if is_safe(x) {
      // On this path, x is Clean
      exec_sql(x); // Safe!
  } else {
      // On this path, x is still Tainted
      // exec_sql(x); // Would be an error
  }
  ```

  A path-insensitive analysis would merge the branches at the end (or even before the sink if the control flow is complex), concluding that `x` is potentially tainted.
]

In our BDD-based framework, the abstract state is not just a mapping `Var -> Taint`.
Instead, it is a mapping `Var -> (Bdd -> Taint)`.
Effectively, for each variable, we track the *path condition* under which it is tainted.

=== Sanitization as Refinement

When the analyzer encounters a check like `if is_safe(x)`, it performs a *refinement* on the abstract state.

+ *Branching:* The analysis splits into two paths.
  - True branch: Path condition $b_"true" = b and "is_safe"(x)$.
  - False branch: Path condition $b_"false" = b and not "is_safe"(x)$.

+ *Refinement:* In the true branch, we update the state of `x`.
  - `state.update("x", Clean)`

+ *Verification:* When `exec_sql(x)` is called, we check:
  - Is `x` tainted on any feasible path reaching this statement?
  - Since we are in the true branch, `x` is marked `Clean`.
    The check passes.

#insight-box[
  BDDs allow us to prove safety properties that depend on control flow.
  We don't just know *that* `x` is clean; we know *why* (because we passed the `is_safe` check).
]

== Implicit Flows

Beyond direct data flow, BDDs can help detect *implicit flows* --- information leaks through control flow.

```rust
let secret = get_secret_bit();
let mut public = 0;
if secret == 1 {
    public = 1;
}
// public now contains the secret!
```

Standard taint analysis might miss this if it only tracks data assignments.
With BDDs, the value of `public` depends on the path condition, which depends on `secret`.
If we track "tainted path conditions", we can flag `public` as tainted because its value correlates with a tainted decision.

== Implementation Strategy

To implement this in `bdd-rs`:

+ *Domain:* Implement `AbstractDomain` for `Taint` (Clean/Tainted).
+ *State:* Use `PartitionedState<Taint>`.
+ *Sources:* `assign("x", Tainted)` introduces taint.
+ *Sinks:* `check("x")` asserts that `x` is `Clean` on all feasible paths.
+ *Sanitizers:* `assume(is_safe(x))` refines `x` to `Clean` in the current partition.

See `examples/security_and_normalization.rs` for a complete implementation.

