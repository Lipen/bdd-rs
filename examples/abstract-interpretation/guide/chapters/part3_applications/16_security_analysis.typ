#import "../../theme.typ": *

= Network Security Analysis <ch-security>

#reading-path(path: "essential")

Security analysis is one of the most impactful applications of abstract interpretation.
In the context of network verification, we track the flow of "tainted" (potentially malicious) data from the public internet to protected internal services.
This allows us to detect vulnerabilities like unauthorized access, data exfiltration, and bypass of security controls.

== Packet Taint Analysis

The core concept is *taint tracking*.
- *Sources*: Packets arriving on public interfaces (e.g., `eth0`) are "Tainted".
- *Sinks*: Forwarding to sensitive internal subnets (e.g., `10.0.0.0/8`) requires "Clean" packets.
- *Sanitizers*: Deep Packet Inspection (DPI) or strict protocol validation marks a packet as "Clean".

#definition(title: "Taint Domain")[
  The taint domain is a simple two-point lattice:
  $ D = \{ lbot, "Clean", "Tainted", ltop \} $
  where $"Clean" < "Tainted"$.
]

== BDD-Guided Taint Analysis

Standard taint analysis is often path-insensitive, leading to false positives.
It might flag a firewall rule as unsafe because it merges paths where packets are validated with paths where they aren't.
BDDs allow us to track *under what conditions* a packet is tainted.

#example-box(title: "Conditional Sanitization")[
  Consider a firewall rule that only forwards packets after a signature check:

  ```rust
  let pkt = recv_packet(); // pkt is Tainted
  if check_signature(pkt) {
      // On this path, pkt is Clean
      forward_to_backend(pkt); // Safe!
  } else {
      // On this path, pkt is still Tainted
      // forward_to_backend(pkt); // Would be an error
      drop(pkt);
  }
  ```

  A path-insensitive analysis would merge the branches, concluding that `pkt` might be tainted at the forwarding step.
]

In our BDD-based framework, the abstract state maps `PacketVar -> (Bdd -> Taint)`.
Effectively, we track the *path condition* under which the packet is tainted.

=== Sanitization as Refinement

When the analyzer encounters `if check_signature(pkt)`, it performs a *refinement*:

+ *Branching:* The analysis splits into two paths.
  - True branch: Path condition $b_"true" = b and "valid_sig"("pkt")$.
  - False branch: Path condition $b_"false" = b and not "valid_sig"("pkt")$.

+ *Refinement:* In the true branch, we update the state of `pkt`.
  - `state.update("pkt", Clean)`

+ *Verification:* When `forward_to_backend(pkt)` is called, we check:
  - Is `pkt` tainted on any feasible path reaching this statement?
  - Since we are in the true branch, `pkt` is marked `Clean`.
    The check passes.

#insight-box[
  BDDs allow us to prove safety properties that depend on control flow.
  We don't just know *that* the packet is clean; we know *why* (because it passed the signature check).
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
+ *Sources:* `assign("pkt", Tainted)` introduces taint.
+ *Sinks:* `check("pkt")` asserts that `pkt` is `Clean` on all feasible paths.
+ *Sanitizers:* `assume(valid_sig(pkt))` refines `pkt` to `Clean` in the current partition.

See `examples/security_and_normalization.rs` for a complete implementation.

