#import "../../theme.typ": *

= Foundations of Abstraction <ch-abstraction>

#reading-path(path: "essential") #h(0.5em) #reading-path(path: "beginner")

The Prologue showed we cannot test every possible input.
We must reason about *sets* of inputs (abstract properties) rather than individual values.
But how do we actually do this?
How do we ensure approximation doesn't hide the bugs we seek?

This chapter introduces the core mechanism: *Abstract Domains*.

== The Geometric Analogy

Imagine a cylinder floating in space.
Describing its exact position and shape requires precise coordinates for every surface point.
This is like a program's *concrete state*: complex, detailed (all variable values, memory, heap), hard to manipulate.

Now imagine shining light to cast shadows on walls.
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

Abstract Interpretation is choosing the right "projection" (abstraction) for the property we want to prove.
- To prove a variable is positive, project to its *Sign*.
- To prove a variable is even, project to its *Parity*.
- To prove a variable is within a range, project to an *Interval*.

== The Subject of Analysis: IMP

We need a concrete subject to analyze.
Throughout this guide, we build a *Static Analyzer* for a toy language called *IMP* (Minimal Imperative Language).

IMP is standard in verification textbooks.
It supports:
- *Variables*: Integers (`x`, `y`, `z`).
- *Arithmetic*: `+`, `-`, `*`, `/`.
- *Control Flow*: `if-else`, `while`.
- *Assertions*: `assert(condition)`.

Here is a simple IMP program:

```rust
// Example IMP program
x = input();
if x > 0 {
    y = x + 1;
} else {
    y = 0;
}
assert(y > 0);
```

Our goal: verify properties like "Is the assertion always true?" or "Can `y` ever be negative?".

== Designing an Abstract Domain

We cannot simulate every possible integer input.
Instead, we design an *Abstract Domain* capturing the properties we care about.

Focus on variable *sign*.
Concrete variables hold specific integers (e.g., `5`, `-42`, `0`).
For analysis, we often only care if a number is positive, negative, or zero.

We define a set of abstract values $D$:
$ D = {bot, "Neg", "Zero", "Pos", top} $

- $bot$ (Bottom): Represents the *empty set* (impossible / dead code).
- `Neg`: Represents the set of all negative integers.
- `Zero`: Represents the singleton set ${0}$.
- `Pos`: Represents the set of all positive integers.
- $top$ (Top): Represents the *universal set* (unknown / any integer).

We can implement this in Rust:

#example-reference(
  "domains",
  "sign.rs",
  "sign_domain",
  [
    Complete implementation of the Sign domain with lattice operations.
    Shows how abstraction trades precision for tractability.
  ],
)

== Formalizing Abstraction

With a domain defined, we can be rigorous.
We define two functions connecting the concrete world (actual execution) and abstract world (properties).

#definition(title: "Concretization Function")[
  The concretization function $gamma: D -> cal(P)(ZZ)$ maps an abstract value to a set of concrete integers $ZZ$.
  For our Sign domain:
  $
     gamma("Pos") & = {z in ZZ mid(|) z > 0} \
     gamma("Neg") & = {z in ZZ mid(|) z < 0} \
    gamma("Zero") & = {0} \
       gamma(bot) & = emptyset \
       gamma(top) & = ZZ
  $
]

Analysis is *sound* if abstract results always cover concrete results.
If a variable is actually `5`, analysis must return either `Pos` or $top$, never `Neg`.

== Interactive Reasoning

Let's build intuition by playing a game using this domain.
I have two hidden program states (variables), $A$ and $B$.
I won't tell you their exact values, but I will tell you their *abstract signs*.

=== First Scenario: Both Positive

Suppose:
- $A$ has sign `Pos`
- $B$ has sign `Pos`

Question: If I pick one variable at random, what is its sign?

The answer is `Pos`.
Reasoning: The union of two positive value sets is still positive.
Both possibilities lead to positive values, so we can be certain.

=== Second Scenario: Mixed Signs

Now suppose:
- $A$ has sign `Pos`
- $B$ has sign `Neg`

Question: If I pick one variable at random, what is its sign?

The answer is $top$ (Unknown).
Here's why:
- Could be positive or negative.
- Domain $D$ lacks a "Non-Zero" value.
- Smallest value covering both is $top$.

Since the result depends on *which path* was taken, we cannot give a precise single sign.
We return $top$ to remain sound.

=== Abstract Semantics

We define *abstract transfer functions* to execute code in this domain.
For merging two paths:

```rust
impl AbstractDomain for Sign {
    fn join(&self, other: &Self) -> Self {
        match (self, other) {
            (Sign::Pos, Sign::Pos) => Sign::Pos,
            (Sign::Neg, Sign::Neg) => Sign::Neg,
            (Sign::Zero, Sign::Zero) => Sign::Zero,
            (Sign::Bot, x) => x.clone(),
            (x, Sign::Bot) => x.clone(),
            // ... merging different signs returns Top
            _ => Sign::Top,
        }
    }
}
```

== The Challenge of Control Flow

Straight-line code is easy.
Branches are hard.

```rust
if input > 0 {
    x = 1;  // x is "Pos"
} else {
    x = -1; // x is "Neg"
}
// At this point, what is x?
```

At the merge point, `x` could be `1` OR `-1`.
In the Sign domain, we must find one value covering *both* possibilities.
The smallest value covering both `Pos` and `Neg` is $top$.

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
    draw-state((-x-sep, y-branch), "s1", [$x = 1$ (`Pos`)])
    draw-state((x-sep, y-branch), "s2", [$x = -1$ (`Neg`)])
    draw-state((0, y-merge), "merge", [$x = ?$ ($top$)])

    // Edges
    line("s1", "merge", ..style-arrow)
    line("s2", "merge", ..style-arrow)

    content((2, y-merge), text(size: 0.8em, fill: colors.error)[Precision Loss!], anchor: "west")
  }),
)

We lost the information that `x` is non-zero!
We know it's one of the two, but abstraction forces us to say "could be anything."

This is where *BDDs* enter.
Instead of merging everything into one abstract value (getting $top$), BDDs track *which path* leads to which value.

- Path 1 (`input > 0`): `x` is `Pos`
- Path 2 (`input <= 0`): `x` is `Neg`

This is called *Path Sensitivity*, and it is the main focus of this guide.

#chapter-summary[
  - *Abstraction is Projection.*
    Like a shadow of a 3D object, an abstract domain captures some properties while ignoring others.

  - *Soundness is Key.*
    If the abstraction says "Safe", the concrete program must be safe.
    If the abstraction says "Unknown", the program might be safe or unsafe.

  - *Precision vs. Speed.*
    More complex domains (Interval vs. Sign) give better answers but cost more to compute.

  - *The Merge Problem.*
    Control flow merges force us to combine conflicting information, often leading to precision loss ($top$).
]
