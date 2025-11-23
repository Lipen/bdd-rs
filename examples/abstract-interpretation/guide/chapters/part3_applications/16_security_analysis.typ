#import "../../theme.typ": *

= Security Analysis <ch-security>

#reading-path(path: "essential")

Security analysis is one of the most impactful applications of abstract interpretation.
We track the flow of "tainted" (potentially malicious) data from untrusted sources to sensitive sinks, detecting vulnerabilities like unauthorized access, data exfiltration, and bypass of security controls.

== Input Taint Analysis

The core concept is *taint tracking*.
- *Sources*: Data from untrusted sources (e.g., user input) are "Tainted".
- *Sinks*: Writing to sensitive sinks (e.g., database) requires "Clean" data.
- *Sanitizers*: Input Validation or sanitization functions marks data as "Clean".

#definition(title: "Taint Domain")[
  The taint domain is a simple two-point lattice:
  $ D = { bot, "Clean", "Tainted", top } $
  where $"Clean" < "Tainted"$.
]

== BDD-Guided Taint Analysis

Taint analysis is often path-insensitive, leading to false positives: flagging validation logic as unsafe because it merges paths where inputs are validated with paths where they aren't.
BDDs let us track *under what conditions* an input is tainted.

#example-box(title: "Conditional Sanitization")[
  Consider a validation logic that only processes data after a check:

  ```rust
  let data = read_input(); // data is Tainted
  if validate_input(data) {
      // On this path, data is Clean
      write_to_db(data); // Safe!
  } else {
      // On this path, data is still Tainted
      // write_to_db(data); // Would be an error
      log_error(data);
  }
  ```

  A path-insensitive analysis would merge the branches, concluding that `data` might be tainted at the writing step.
]

#figure(
  caption: [Path-sensitive taint analysis],

  cetz.canvas({
    import cetz: draw

    // Nodes
    draw.circle((0, 4), radius: 0.5, name: "start", stroke: colors.primary + 1pt)
    draw.content("start", [Start])
    draw.content((0, 4.6), text(size: 9pt)[data: Tainted])

    draw.rect((-2, 2), (-1, 3), name: "valid", stroke: colors.success + 1pt)
    draw.content("valid", [Valid])
    draw.content("valid.west", text(size: 9pt, fill: colors.success)[data: Clean], anchor: "east", padding: 0.2)

    draw.rect((1, 2), (2, 3), name: "invalid", stroke: colors.error + 1pt)
    draw.content("invalid", [Invalid])
    draw.content("invalid.east", text(size: 9pt, fill: colors.error)[data: Tainted], anchor: "west", padding: 0.2)

    draw.circle((-1.5, 0), radius: 0.5, name: "sink", stroke: colors.primary + 1pt)
    draw.content("sink", [Sink])

    draw.circle((1.5, 0), radius: 0.5, name: "log", stroke: colors.primary + 1pt)
    draw.content("log", [Log])

    // Edges
    draw.line("start", "valid.north", stroke: colors.text-light + 0.8pt, mark: (end: ">"), name: "start-valid")
    draw.content("start-valid", [check ok], anchor: "south-east", padding: 0.1)

    draw.line("start", "invalid.north", stroke: colors.text-light + 0.8pt, mark: (end: ">"), name: "start-invalid")
    draw.content("start-invalid", [check fail], anchor: "south-west", padding: 0.1)

    draw.line("valid", "sink", stroke: colors.success + 1pt, mark: (end: ">"), name: "valid-sink")
    draw.content("valid-sink", text(fill: colors.success)[Safe], anchor: "east", padding: 0.2)

    draw.line("invalid", "log", stroke: colors.text-light + 0.8pt, mark: (end: ">"), name: "invalid-log")
    draw.content("invalid-log", [log tainted], anchor: "west", padding: 0.2)
  }),
)

In our BDD-based framework, the abstract state maps `Var -> (Bdd -> Taint)`.
Effectively, we track the *path condition* under which the variable is tainted.

=== Sanitization as Refinement

When the analyzer encounters `if validate_input(data)`, it performs a *refinement*:

+ *Branching:* The analysis splits into two paths.
  - True branch: Path condition $b_"true" = b and "is_valid"("data")$.
  - False branch: Path condition $b_"false" = b and not "is_valid"("data")$.

+ *Refinement:* In the true branch, we update the state of `data`.
  - `state.update("data", Clean)`

+ *Verification:* When `write_to_db(data)` is called, we check:
  - Is `data` tainted on any feasible path reaching this statement?
  - Since we are in the true branch, `data` is marked `Clean`.
    The check passes.

#insight-box[
  BDDs allow us to prove safety properties that depend on control flow.
  We don't just know *that* the data is clean; we know *why* (because it passed the validation check).
]

== Implicit Flows and Side Channels

Beyond direct data flow, BDDs can help detect *implicit flows* --- information leaks through control flow decisions.

```rust
let secret_key = get_private_key_bit();
let mut response_delay = 0;
if secret_key == 1 {
    response_delay = 100; // Timing leak!
}
// response_delay now correlates with the secret!
```

If we track "tainted path conditions", we can flag `response_delay` as tainted because its value depends on a decision made using `secret_key`.

== Implementation Strategy

To implement this in `bdd-rs`:

+ *Domain:* Implement `AbstractDomain` for `Taint` (Clean/Tainted).
+ *State:* Use `PartitionedState<Taint>`.
+ *Sources:* `assign("data", Tainted)` introduces taint.
+ *Sinks:* `check("data")` asserts that `data` is `Clean` on all feasible paths.
+ *Sanitizers:* `assume(is_valid(data))` refines `data` to `Clean` in the current partition.

See `examples/security_analysis.rs` for a complete implementation.

