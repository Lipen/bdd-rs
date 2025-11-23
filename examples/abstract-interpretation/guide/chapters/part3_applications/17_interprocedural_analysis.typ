#import "../../theme.typ": *

= Inter-Chain Analysis <ch-interprocedural>

#reading-path(path: "advanced")

Real-world firewall policies are rarely a single flat list of rules.
They are organized into *chains* (e.g., in `iptables` or `nftables`) or *modules* that jump to one another.
Inter-chain analysis reasons across these boundaries, treating chains like functions in a program.

== Chain Graph and Summaries

We assume a "Chain Jump Graph" $G_c$ where nodes are chains and edges are jumps.

#definition(title: "Chain Summary")[
  A summary $S_C: A -> A$ maps an abstract input packet state to an abstract output state (or verdict) for chain $C$.
  This allows us to analyze a chain once and reuse the result whenever it is "called" (jumped to).
]

- *Context-insensitive*: One summary per chain. Fast, but may lose precision if the chain behaves differently based on who called it.
- *Context-sensitive*: Summarize per calling context (e.g., "Called from Ingress" vs "Called from VPN").

== The Challenge of Summaries with BDDs

When using BDDs, a unique challenge arises: *Variable Remapping*.
A reusable chain `check_subnet(ip)` might be called with `src_ip` in one place and `dst_ip` in another.
The BDD for `check_subnet` is built using a formal parameter `ip`.
To apply the summary, we must:
+ *Rename:* Substitute the formal parameter (`ip`) with the actual argument (`src_ip`) in the BDD.
+ *Project:* Existentially quantify out local variables of the chain to keep the summary clean.

#example-box(title: "Applying a Chain Summary")[
  Summary for `check_whitelist(addr)`:
  $ R = ("addr" in "Whitelist" and "verdict" = "Accept") or ("addr" in.not "Whitelist" and "verdict" = "Drop") $

  Call site: `jump check_whitelist(src_ip)`

  + *Rename:* Replace `"addr" -> "src_ip"`.
  + *Instantiate:*
    $ R' = ("src_ip" in "Whitelist" and "verdict" = "Accept") or ("src_ip" in.not "Whitelist" and "verdict" = "Drop") $
  + *Join:* Combine $R'$ with the current state at the call site.
]

== Call-Strings (k-limited)

In packet filtering, "recursion" is rare, but "shared chains" are common.
A `log_and_drop` chain might be called from 50 different places.

#definition(title: "k-Call-String Sensitivity")[
  A context is the sequence of the last $k$ chains visited.
  Summaries are memoized by `(chain, context_k)`.
]

This is useful if `log_and_drop` needs to know *which* chain called it to provide a precise error analysis (e.g., "Dropped by SQL Filter" vs "Dropped by Rate Limiter").

== Handling Loops and Recursion

Most firewall configurations (like `iptables`) form a Directed Acyclic Graph (DAG).
However, some advanced SDN controllers or complex routing policies might introduce loops.
In these cases, we compute the *Least Fixpoint* of the chain summaries.

#algorithm(title: "SCC Worklist")[
  + Compute Strongly Connected Components (SCCs) of the Chain Graph.
  + Process SCCs in topological order (leaves to root).
  + For a cyclic SCC, iterate summaries until convergence (using widening if domains are infinite).
  + Export stabilized summaries to callers.
]

== Modular vs Whole-Policy Analysis

- *Modular*: Analyze each chain in isolation with assumed contracts. Useful for incremental updates (e.g., adding a rule to one chain doesn't require re-analyzing the whole firewall).
- *Whole-Policy*: Analyze the entire ruleset as one giant control flow graph. More precise but slower.

#chapter-summary[
  Inter-chain analysis treats firewall chains as functions.
  By computing *summaries* and handling *variable remapping* with BDDs, we can efficiently analyze complex, modular policies without exploding the state space.
]
