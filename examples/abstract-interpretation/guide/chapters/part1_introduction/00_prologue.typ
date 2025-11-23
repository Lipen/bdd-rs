#import "../../theme.typ": *

#counter(heading).update(0)

#heading(numbering: none)[Prologue: The Case for Network Verification]

#reading-path(path: "essential") #h(0.5em) #reading-path(path: "beginner")

_July 2019._
_A Major Financial Institution._

A hacker gains access to over 100 million customer records.
Social Security numbers, bank account details, and credit scores are exfiltrated.
The breach costs the company hundreds of millions of dollars in fines and settlements.

The cause?
A *Server-Side Request Forgery (SSRF)* vulnerability combined with a *Firewall Misconfiguration*.
The Web Application Firewall (WAF) had permissions to access the backend metadata service.
A specific rule allowed traffic from the WAF to the metadata server, which contained the credentials for the entire cloud environment.

This was not a zero-day exploit in the kernel.
It was a failure of *policy verification*.
A static analysis tool capable of analyzing network reachability could have proven that the WAF was allowed to initiate connections to the sensitive metadata IP address.

But this story is not unique.
History is littered with expensive and deadly failures where the system behaved exactly as configured, but the configuration was wrong.

=== The High Cost of Misconfiguration

*Facebook BGP Outage (2021):*
A routine configuration change to the backbone routers disconnected Facebook's data centers from the internet.
The BGP routes were withdrawn, making Facebook.com (and WhatsApp, Instagram) disappear from the global routing table.
*Cost: \$60 million in revenue, 6 hours of global downtime.*

*Ariane 5 (1996):*
Thirty-seven seconds after launch, the rocket disintegrated due to an integer overflow.
While not a network failure, it illustrates the same principle: unverified assumptions about data ranges.
*Cost: \$370 million.*

These disasters share a common thread:
The configurations passed standard syntax checks.
They worked in the test lab.
But the *state space* --- the combination of all possible packets, routes, and failures --- was not fully explored.

#v(1em)

== The Illusion of Testing

We have built a civilization that runs on networks.
Yet, our primary method for ensuring reliability --- testing (ping, traceroute, penetration testing) --- is fundamentally incapable of guaranteeing it.

Testing is the process of checking specific points in the input space.
If we test packets $p_1, p_2, ..., p_n$, we know the network handles those $n$ packets correctly.
We know *nothing* about packet $p_(n+1)$.

#figure(
  caption: [Testing vs. Verification. Testing checks individual packets (green dots). Verification proves properties about the entire header space (blue region).],
  cetz.canvas({
    import cetz.draw: *

    let style-space = (fill: colors.bg-subtle, stroke: colors.text-light + 1pt)
    let style-test = (fill: colors.success, stroke: none, radius: 0.08)
    let style-verify = (fill: colors.primary.lighten(80%), stroke: colors.primary + 1pt)

    // Input Space
    rect((0, 0), (6, 4), ..style-space, name: "space")
    content((3, 4.3), text(weight: "bold")[Header Space ($2^104$ bits)])

    // Testing (Scattered points)
    for i in range(15) {
      let x = calc.rem(i * 7 + 3, 55) / 10.0 + 0.2
      let y = calc.rem(i * 3 + 2, 35) / 10.0 + 0.2
      circle((x, y), ..style-test)
    }
    content((1, 0.5), text(size: 0.8em, fill: colors.success)[Tests])

    // Verification (Covered region)
    rect((3.5, 1.5), (5.5, 3.5), ..style-verify)
    content((4.5, 2.5), align(center, text(size: 0.8em, fill: colors.primary)[Verified \ Region]))

    // Bug (Uncovered)
    circle((5.2, 0.8), radius: 0.1, fill: colors.error, stroke: none)
    content((5.2, 0.4), text(size: 0.8em, fill: colors.error)[Bug])

    // Arrow from verified to bug (showing it missed? No, verification covers regions)
    // Let's show that testing missed the bug
  }),
)

Consider a simple firewall rule checking IPv4 source, destination, and port:

```rust
fn check_packet(src: u32, dst: u32, port: u16) -> Action { ... }
```

The input space size is $2^32 times 2^32 times 2^16 = 2^80$.
If we include IPv6 ($2^128$), the space is astronomically larger.
We cannot test our way to security.

== What is Verification?

If testing is "checking some packets," then *verification* is "proving properties about *all* packets."

In networking, we use logic and mathematics to prove statements like:
- "The Database subnet is *never* reachable from the Public Internet."
- "All traffic from VPN users *must* pass through the Intrusion Detection System."
- "No two rules in this firewall chain are *redundant*."

=== The Spectrum of Assurance

We can view network assurance as a spectrum:

+ *Ping/Traceroute:* Checks connectivity for one packet at one time.
+ *Penetration Testing:* Checks for known vulnerabilities using random or heuristic attacks.
+ *Config Analysis:* Checks for syntax errors and bad practices (linting).
+ *Formal Verification:* Mathematically proves that the network policy satisfies a specification for *all* possible packets.

This guide focuses on a sweet spot in this spectrum: *Abstract Interpretation*.

== The Formal Alternative: Abstract Interpretation

Abstract Interpretation is a technique that allows us to reason about infinite state spaces using finite representations.
We do not send packets; we *analyze* the policy.

Instead of tracking the exact value of a header field (which could be anything), we track its *abstract property*.
For example, instead of knowing `src_ip = 192.168.1.55`, we might know `src_ip in 192.168.1.0/24`.

If we know `src_ip` is Internal and `dst_ip` is External, we can determine the firewall action without knowing the exact IP addresses.

== The Challenge: Combinatorial Explosion

However, abstract interpretation faces a massive hurdle: *Rule Complexity*.
Every firewall rule splits the packet space.
Every jump to a sub-chain multiplies the number of paths.
A complex policy with thousands of rules can have an explosion of possible packet flows.

Naive analysis either:
1. *Explodes*: Tries to track every single IP address and runs out of memory.
2. *Gives Up*: Merges all flows together, losing precision (e.g., concluding "Access might be allowed").

== Enter the BDD

This guide focuses on a specific, powerful synergy:
*Abstract Interpretation* combined with *Binary Decision Diagrams (BDDs)*.

*BDDs* are the secret weapon against combinatorial explosion.
They allow us to represent and manipulate *sets of packets* implicitly.
Instead of listing billions of IP addresses, a BDD might represent a complex ACL with a graph of just a few hundred nodes.

Together, they enable *Path-Sensitive Analysis*: verification that understands how packet headers match rules, yet scales to real-world networks.

== The Journey Ahead

This is not just a theoretical textbook.
It is a practical guide to building verification tools in Rust.
We chose Rust because it is the language of modern systems programming, and its type system aligns beautifully with the goals of verification.

We will start from first principles:
+ *Abstraction:* How to trade precision for speed (CIDR blocks).
+ *Control Flow:* Why rule chains are the enemy of analysis.
+ *Symbolic Logic:* How BDDs crush combinatorial complexity.

Then, we will build a complete *Symbolic Firewall Checker* capable of proving security properties that testing would miss.

The Facebook and Capital One incidents demonstrated the fragility of our digital infrastructure.
It is our responsibility as engineers to build networks that are not just "probably" secure, but *provably* robust.

Let us begin.
