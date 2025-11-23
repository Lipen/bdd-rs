// Chapter 1: The World of Abstract Interpretation

#import "../../theme.typ": *

= The Art of Header Space Analysis <ch-abstraction>

#reading-path(path: "essential") #h(0.5em) #reading-path(path: "beginner")

In the Prologue, we established that exact verification is impossible for general networks.
We must approximate.
But how do we approximate in a way that is useful for networks?
How do we ensure we don't "approximate away" the security holes we are trying to find?

This chapter introduces the core concept of Abstract Interpretation applied to networks:
*Header Space Analysis*.

== The Geometric Analogy

Imagine a complex 3D object, such as a cylinder, floating in space.
Describing its exact position and shape requires precise coordinates for every point on its surface.
This is like the *concrete state* of a packet: complex, detailed (payload, timing, fragmentation), and hard to manipulate.

Now, imagine shining a light on the object to cast a shadow on the wall.
- From the top, the shadow is a *circle*.
- From the side, the shadow is a *rectangle*.

#intuition-box[
  Neither shadow captures the full object.
  However, both shadows provide *sound constraints*.
  - If the circular shadow has a diameter of 10cm, we know for a fact that the object fits within a 10cm width.
  - If the rectangular shadow has a height of 20cm, we know the object is no taller than 20cm.
]

Abstract Interpretation is the art of choosing the right "projection" (abstraction) for the property we want to prove.
- If we want to prove a packet is HTTP, we project it to its *Dst Port* field.
- If we want to prove a packet is TCP, we project it to its *Protocol* field.
- If we want to prove a packet comes from a private network, we project its IP to a *CIDR Block*.

== Formalizing Abstraction

To make this rigorous, we define two functions connecting the concrete world (actual packets) and the abstract world (properties).

#definition(title: "Concretization Function ($gamma$)")[
  The concretization function $gamma$ maps an abstract value to the set of concrete packets it represents.
  For example, in the Protocol domain:
  - $gamma("TCP") = {"All TCP packets"}$
  - $gamma("UDP") = {"All UDP packets"}$
  - $gamma(top) = {"All IP packets"}$
]

An analysis is *sound* if the abstract result always covers the concrete result.
If we compute `packet.proto` in the abstract, the result must include the actual protocol of the concrete packet.

== Interactive Reasoning

Before we write code, let's build intuition by playing a game.
I have two hidden packets, $A$ and $B$.
I won't tell you their full headers, but I will tell you their *properties*.

*Round 1:*
- Fact: $A$ is a TCP packet.
- Fact: $B$ is a TCP packet.
- Question: If I pick one at random, what is its protocol?

*Answer:* TCP.
Reasoning: The union of TCP and TCP is still TCP.
We didn't need to know the payloads to know the protocol.

*Round 2:*
- Fact: $A$ is a TCP packet.
- Fact: $B$ is a UDP packet.
- Question: If I pick one at random, what is its protocol?

*Answer:* Unknown ($top$).
Reasoning:
- It could be TCP.
- It could be UDP.

Because the result depends on *which packet* I picked, we cannot give a precise single protocol.
We must return $top$ ("Any Protocol") to remain sound.

== The PFL Language

To make this concrete, we will build a *FirewallChecker* throughout this guide.
We will analyze a simple toy language called *PFL* (Packet Filter Language).

PFL is a minimal language with header matches (IP, Port, Proto), conditionals, and actions (drop/accept).
It is simple enough to understand fully, yet complex enough to exhibit the challenges of verification.

=== Syntax

PFL policies consist of checks and actions.
Here is a simple example that drops traffic to a specific port:

```rust
// Example PFL policy
if dst_port == 80 {
    accept;
} else {
    drop;
}
```

(We will define the full Rust AST in later chapters when we start implementing the parser.)

== The Protocol Domain

Let's formalize our "TCP/UDP" game.
We define a set of abstract values $D$:
$ D = {bot, "TCP", "UDP", "ICMP", top} $

- $bot$ (Bottom): Impossible / No packet.
- "TCP": Strictly TCP packets.
- "UDP": Strictly UDP packets.
- "ICMP": Strictly ICMP packets.
- $top$ (Top): Unknown / Any protocol.

We can implement this in Rust:

#example-reference(
  "domains",
  "protocol.rs",
  "protocol_domain",
  [
    Complete implementation of the protocol domain with lattice operations.
    Shows how abstraction trades precision for tractability.
  ],
)

=== Abstract Semantics

We define *abstract transfer functions* to execute code in this domain.
For merging two paths:

```rust
impl AbstractDomain for Protocol {
    fn join(&self, other: &Self) -> Self {
        match (self, other) {
            (Protocol::TCP, Protocol::TCP) => Protocol::TCP,
            (Protocol::UDP, Protocol::UDP) => Protocol::UDP,
            (Protocol::Bot, x) => x.clone(),
            (x, Protocol::Bot) => x.clone(),
            // ... merging different protocols returns Top
            _ => Protocol::Top,
        }
    }
}
```

== The Challenge of Control Flow

Straight-line code is easy.
Branches are hard.

```rust
if src_ip == 10.0.0.1 {
    proto = TCP;
} else {
    proto = UDP;
}
// At this point, what is proto?
```

At the merge point, `proto` could be TCP OR UDP.
In the Protocol domain, we must find a single value that covers *both* possibilities.
The smallest value covering both TCP and UDP is $top$.

#figure(
  caption: [The Merge Problem. Merging two precise paths often results in information loss ($top$).],
  cetz.canvas({
    import cetz.draw: *

    let style-state = (fill: colors.bg-code, stroke: colors.primary + 1pt, radius: 0.2)

    // Branch
    rect((-2, 2), (-0.5, 3), ..style-state, name: "s1")
    content("s1", [proto = TCP])

    rect((0.5, 2), (2, 3), ..style-state, name: "s2")
    content("s2", [proto = UDP])

    // Merge
    rect((-0.75, 0), (0.75, 1), ..style-state, name: "merge")
    content("merge", [proto = ? \ ($top$)])

    // Edges
    line("s1.south", "merge.north", mark: (end: ">"))
    line("s2.south", "merge.north", mark: (end: ">"))

    content((2.5, 0.5), text(size: 0.8em, fill: colors.error)[Precision Loss!], anchor: "west")
  }),
)

We lost the information that `proto` is either TCP or UDP (and definitely not ICMP)!
We know it's one of the two, but our abstraction forces us to say "It could be anything."

This is where *BDDs* will come in.
Instead of merging everything into a single abstract value (and getting $top$), we can use BDDs to track *which path* leads to which value.

- Path 1 (`src_ip == 10.0.0.1`): `proto = TCP`
- Path 2 (`src_ip != 10.0.0.1`): `proto = UDP`

This is called *Path Sensitivity*, and it is the main focus of this guide.

#chapter-summary[
  - *Abstraction is Projection.*
    Like a shadow of a 3D object, an abstract domain captures some properties while ignoring others.

  - *Soundness is Key.*
    If the abstraction says "Safe", the concrete packet must be safe.
    If the abstraction says "Unknown", the packet might be safe or unsafe.

  - *Precision vs. Speed.*
    More complex domains (CIDR vs. Single IP) give better answers but cost more to compute.

  - *The Merge Problem.*
    Control flow merges force us to combine conflicting information, often leading to precision loss ($top$).
]
