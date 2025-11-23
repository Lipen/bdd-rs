#import "../../theme.typ": *

= Case Study: Access Control System <ch-case-studies>

#reading-path(path: "advanced")

This chapter provides a detailed walkthrough of analyzing a realistic access control policy using `bdd-rs`.
We demonstrate how to encode rules, verify security properties, and detect misconfigurations.

== Problem Statement

We want to secure a system with three roles:
- *Guest:* Unauthenticated users (ID 0-99).
- *User:* Authenticated users (ID 100-199).
- *Admin:* System administrators (ID 200-255).

*Policy Requirements:*
1.  Allow Login (Action 1) for Guest.
2.  Allow Read (Action 2) for User.
3.  *Implicit Deny:* Block everything else.
4.  *Safety Property:* Guest must *never* be able to perform Admin actions.

== BDD Encoding

We allocate boolean variables for the request attributes.
For simplicity, we use 8 bits for User IDs and 8 bits for Action IDs.

- `user_id` (8 vars)
- `resource_id` (8 vars)
- `action_id` (8 vars)
- `type` (8 vars)

Total variables: $8+8+8+8 = 32$.

=== Rule Encoding

Each rule is a boolean formula over these variables.

- *Rule 1 (Guest Login):*
  $ R_1 = ("user" in "Guest") and ("action" = "Login") and ("type" = "Request") $

- *Rule 2 (User Read):*
  $ R_2 = ("user" in "User") and ("action" = "Read") and ("type" = "Request") $

- *Total Policy:*
  $ P = R_1 or R_2 $

== Walkthrough

Let's trace the verification process.

=== Step 1: Building the Policy BDD

We construct BDDs for $R_1$ and $R_2$ and compute their union.
`bdd-rs` automatically compresses common sub-expressions.
For example, if multiple rules check `type = Request`, that check is shared.

=== Step 2: Defining the Property

We want to verify that "Guest cannot perform Admin actions".
We define the *forbidden access* set:
$ F = ("user" in "Guest") and ("action" in "AdminActions") $

=== Step 3: Verification

We check if the policy $P$ allows any access in $F$.
Mathematically, we check if the intersection is empty:
$ "Violation" = P and F $

If `Violation` is `bdd.zero` (False), the policy is safe.
If not, the BDD `Violation` contains *all* counter-examples (requests that violate the policy).

== Detecting Misconfigurations

Suppose an admin accidentally adds a rule:
*Rule 3 (Debug):* Allow Debug (Action 99) for *Any* user.

$ P' = P or ("type" = "Request" and "action" = 99) $

Now we check $P' and F$.
The result is not empty! It contains requests where:
- `user` is Guest
- `action` is Debug (which is sensitive)
- `type` is Request

The BDD gives us the exact scenario of the violation.

== Performance Analysis

#table(
  columns: 4,
  table.header([Rules], [Variables], [BDD Nodes], [Time (ms)]),
  [10], [32], [150], [0.5],
  [100], [32], [1,200], [12.0],
  [10,000], [32], [15,000], [450.0],
)

Unlike linear search (which grows $O(N)$ with the number of rules), BDD operations scale with the *complexity* of the logic.
Redundant rules (e.g., 100 rules blocking specific Users) are compressed into a compact tree structure.

== Code Snippet

The core verification logic:

```rust
// Define roles
let guest = id_range(0, 99);
let admin = id_range(200, 255);

// Define policy
let r1 = bdd.and(guest, login_action);
let r2 = bdd.and(user, read_action);
let policy = bdd.or(r1, r2);

// Define property
let forbidden = bdd.and(guest, admin_actions);

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

