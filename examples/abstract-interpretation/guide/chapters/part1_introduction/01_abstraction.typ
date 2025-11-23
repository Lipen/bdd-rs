// Chapter 1: The World of Abstract Interpretation

#import "../../theme.typ": *

= Foundations of Abstraction <ch-abstraction>

#reading-path(path: "essential") #h(0.5em) #reading-path(path: "beginner")

In the Prologue, we established that we cannot test every possible input.
We must reason about *sets* of inputs (abstract properties) rather than individual values.
But how do we actually do this?
How do we ensure we don't "approximate away" the bugs we are trying to find?

This chapter introduces the core mechanism of Abstract Interpretation:
*Abstract Domains*.

== The Geometric Analogy

Imagine a complex 3D object, such as a cylinder, floating in space.
Describing its exact position and shape requires precise coordinates for every point on its surface.
This is like the *concrete state* of a program: complex, detailed (all variable values, memory, heap), and hard to manipulate.

Now, imagine shining a light on the object to cast a shadow on the wall.
- From the top, the shadow is a *circle*.
- From the side, the shadow is a *rectangle*.

#intuition-box[
  Neither shadow captures the full object.
  However, both shadows provide *sound constraints*.
  - If the circular shadow has a diameter of 10cm, we know for a fact that the object fits within a 10cm width.
  - If the rectangular shadow has a height of 20cm, we know the object is no taller than 20cm.
]

#figure(
  caption: [Abstraction as Projection. The concrete object (cylinder) is complex. Its shadows (circle, rectangle) are simple abstractions. Each shadow captures some truth but loses other details.],
  cetz.canvas({
    import cetz.draw: *

    // --- Constants & Styles ---
    let c-pos = (0, 0)
    let p1-pos = (-4, 0)
    let p2-pos = (4, 0)
    let r-cyl = (1, 0.3) // radius x, y
    let h-cyl = 2

    let style-concrete = (stroke: colors.primary + 1pt)
    let style-abstract-1 = (fill: colors.secondary.lighten(80%), stroke: colors.secondary + 1pt)
    let style-abstract-2 = (fill: colors.accent.lighten(80%), stroke: colors.accent + 1pt)
    let style-proj = (dash: "dotted", paint: colors.text-light)

    // --- Concrete Object (Cylinder) ---
    let (cx, cy) = c-pos
    let (rx, ry) = r-cyl
    let h = h-cyl / 2

    // Top
    circle((cx, cy + h), radius: r-cyl, fill: colors.primary.lighten(60%), ..style-concrete, name: "c_top")
    // Body lines
    line((cx - rx, cy + h), (cx - rx, cy - h), ..style-concrete, name: "c_left")
    line((cx + rx, cy + h), (cx + rx, cy - h), ..style-concrete, name: "c_right")
    // Bottom
    arc((cx - rx, cy - h), start: 180deg, stop: 360deg, radius: r-cyl, mode: "OPEN", ..style-concrete, name: "c_bot")

    content((cx, cy - h - 1), text(weight: "bold")[Concrete Object])

    // --- Projection 1: Circle (Top View) ---
    let (p1x, p1y) = p1-pos
    circle(p1-pos, radius: rx, ..style-abstract-1, name: "p1")
    content((p1x, p1y - 2), [Abstract 1: \ Shape (Circle)])

    // --- Projection 2: Rectangle (Side View) ---
    let (p2x, p2y) = p2-pos
    rect((p2x - rx, p2y - h), (p2x + rx, p2y + h), ..style-abstract-2, name: "p2")
    content((p2x, p2y - 2), [Abstract 2: \ Height (Rect)])

    // --- Projection Lines ---
    // Connect from near the cylinder to the projections
    line((cx - rx - 0.2, cy), "p1.east", ..style-proj)
    line((cx + rx + 0.2, cy), "p2.west", ..style-proj)
  }),
)

Abstract Interpretation is the art of choosing the right "projection" (abstraction) for the property we want to prove.
- If we want to prove a variable is positive, we project it to its *Sign*.
- If we want to prove a packet is TCP, we project it to its *Protocol*.
- If we want to prove a pointer is safe, we project it to its *Nullability*.

== Formalizing Abstraction

To make this rigorous, we define two functions connecting the concrete world (actual execution) and the abstract world (properties).

#definition(title: "Concretization Function")[
  The concretization function $gamma$ maps an abstract value to the set of concrete states it represents.
  For example, in the Protocol domain:
  - $gamma("TCP") = {"All TCP packets"}$
  - $gamma("UDP") = {"All UDP packets"}$
  - $gamma(top) = {"All IP packets"}$
]

An analysis is *sound* if the abstract result always covers the concrete result.
If we compute `packet.proto` in the abstract, the result must include the actual protocol of the concrete packet.

== Interactive Reasoning

Before we write code, let's build intuition by playing a game.
I have two hidden program states, $A$ and $B$.
I won't tell you their full memory, but I will tell you their *properties*.

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

Because the result depends on *which path* we took, we cannot give a precise single protocol.
We must return $top$ ("Any Protocol") to remain sound.

== The Subject of Analysis: PFL

To make this concrete, we will build a *Static Analyzer* throughout this guide.
We will analyze a simple toy language called *PFL* (Packet Filter Language).

PFL is a minimal language with header matches (IP, Port, Proto), conditionals, and actions (drop/accept).
It is simple enough to understand fully, yet complex enough to exhibit the challenges of verification (branching, state merging).

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

== Designing an Abstract Domain

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
    let style-arrow = (mark: (end: ">"), stroke: colors.text-light + 0.8pt)

    let draw-state(pos, name, body, width: 2.5, height: 1) = {
      let (x, y) = pos
      let w = width / 2
      let h = height / 2
      rect((x - w, y - h), (x + w, y + h), name: name, ..style-state)
      content(pos, body)
    }

    // Layout
    let y-branch = 2.5
    let y-merge = 0.5
    let x-sep = 2

    // Nodes
    draw-state((-x-sep, y-branch), "s1", [proto = TCP])
    draw-state((x-sep, y-branch), "s2", [proto = UDP])
    draw-state((0, y-merge), "merge", [proto = ? ($top$)])

    // Edges
    line("s1", "merge", ..style-arrow)
    line("s2", "merge", ..style-arrow)

    content((2, y-merge), text(size: 0.8em, fill: colors.error)[Precision Loss!], anchor: "west")
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
