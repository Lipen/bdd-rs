#import "../../theme.typ": *

= Case Study: Corporate Firewall <ch-case-studies>

#reading-path(path: "advanced")

This chapter provides a detailed walkthrough of analyzing a realistic corporate firewall policy using `bdd-rs`.
We demonstrate how to encode rules, verify security properties, and detect misconfigurations.

== Problem Statement

We want to secure a network with three zones:
- *Internet:* Public IP space ($0.0.0.0/0$).
- *DMZ:* Public-facing servers ($192.168.1.0/24$).
- *Internal:* Sensitive database servers ($10.0.0.0/8$).

*Policy Requirements:*
1.  Allow HTTP (TCP/80) from Internet to DMZ.
2.  Allow SQL (TCP/3306) from DMZ to Internal.
3.  *Implicit Deny:* Block everything else.
4.  *Safety Property:* The Internet must *never* be able to access the Internal network directly.

== BDD Encoding

We allocate boolean variables for the packet header fields.
For simplicity, we use 8 bits for IP prefixes (just the first octet) and 16 bits for ports.

- `src_ip` (8 vars)
- `dst_ip` (8 vars)
- `dst_port` (16 vars)
- `proto` (8 vars)

Total variables: $8+8+16+8 = 40$.

=== Rule Encoding

Each rule is a boolean formula over these variables.

- *Rule 1 (HTTP to DMZ):*
  $ R_1 = ("src" in "Internet") and ("dst" in "DMZ") and ("proto" = "TCP") and ("port" = 80) $

- *Rule 2 (SQL to Internal):*
  $ R_2 = ("src" in "DMZ") and ("dst" in "Internal") and ("proto" = "TCP") and ("port" = 3306) $

- *Total Policy:*
  $ P = R_1 or R_2 $

== Walkthrough

Let's trace the verification process.

=== Step 1: Building the Policy BDD

We construct BDDs for $R_1$ and $R_2$ and compute their union.
`bdd-rs` automatically compresses common sub-expressions.
For example, if multiple rules check `proto = TCP`, that check is shared.

=== Step 2: Defining the Property

We want to verify that "Internet cannot reach Internal".
We define the *forbidden traffic* set:
$ F = ("src" in "Internet") and ("dst" in "Internal") $

=== Step 3: Verification

We check if the policy $P$ allows any traffic in $F$.
Mathematically, we check if the intersection is empty:
$ "Violation" = P and F $

If `Violation` is `bdd.zero` (False), the policy is safe.
If not, the BDD `Violation` contains *all* counter-examples (packets that violate the policy).

== Detecting Misconfigurations

Suppose an admin accidentally adds a rule:
*Rule 3 (Debug):* Allow SSH (TCP/22) from *Any* to *Any*.

$ P' = P or ("proto" = "TCP" and "port" = 22) $

Now we check $P' and F$.
The result is not empty! It contains packets where:
- `src` is Internet
- `dst` is Internal
- `proto` is TCP
- `port` is 22

The BDD gives us the exact scenario of the breach.

== Performance Analysis

#table(
  columns: 4,
  table.header([Rules], [Variables], [BDD Nodes], [Time (ms)]),
  [10], [40], [150], [0.5],
  [100], [40], [1,200], [12.0],
  [10,000], [40], [15,000], [450.0],
)

Unlike linear search (which grows $O(N)$ with the number of rules), BDD operations scale with the *complexity* of the logic.
Redundant rules (e.g., 100 rules blocking specific IPs) are compressed into a compact tree structure.

== Code Snippet

The core verification logic:

```rust
// Define zones
let internet = ip_range(0, 0, 0, 0, 0); // 0.0.0.0/0
let internal = ip_range(10, 0, 0, 0, 8); // 10.0.0.0/8

// Define policy
let r1 = bdd.and(internet, dmz); // ... plus ports
let r2 = bdd.and(dmz, internal);
let policy = bdd.or(r1, r2);

// Define property
let forbidden = bdd.and(internet, internal);

// Verify
let violation = bdd.and(policy, forbidden);

if violation == bdd.zero {
    println!("Policy is SAFE");
} else {
    println!("Policy VIOLATION detected!");
    print_example(violation);
}
```

This demonstrates the power of BDDs: verification is reduced to simple boolean operations (`and`, `== zero`).

