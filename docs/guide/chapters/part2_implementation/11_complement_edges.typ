#import "../../theme.typ": *

= Complement Edges <ch-complement-edges>

What if negating a BDD took zero time?
Not "fast" --- literally *zero*.
Just flip one bit, and $f$ becomes $not f$.

This is what *complement edges* achieve.
They are one of the most elegant optimizations in BDD technology: negation becomes $O(1)$, memory usage drops (since $f$ and $not f$ share all structure), and the `Apply` algorithm gets powerful new terminal cases.

The tradeoff? Careful bookkeeping to maintain canonicity.
This chapter explains the concept, the implementation, and the subtle invariants.

== The Problem: Redundant Negations

In standard BDDs, $f$ and $not f$ are completely separate structures.

#figure(
  cetz.canvas(length: 1cm, {
    import cetz.draw: *

    // Left: BDD for x
    let x1-pos = (2, 3)
    let zero1 = (1.2, 1)
    let one1 = (2.8, 1)

    bdd-terminal-node(zero1, 0)
    bdd-terminal-node(one1, 1)
    bdd-decision-node(x1-pos, "x")
    bdd-low-edge((x1-pos.at(0) - 0.3, x1-pos.at(1) - 0.4), (zero1.at(0) + 0.15, zero1.at(1) + 0.35))
    bdd-high-edge((x1-pos.at(0) + 0.3, x1-pos.at(1) - 0.4), (one1.at(0) - 0.15, one1.at(1) + 0.35))

    content((2, 4), text(weight: "bold", fill: colors.primary)[$x$])

    // Right: BDD for ¬x
    let x2-pos = (7, 3)
    let zero2 = (6.2, 1)
    let one2 = (7.8, 1)

    bdd-terminal-node(zero2, 0)
    bdd-terminal-node(one2, 1)
    bdd-decision-node(x2-pos, "x")
    bdd-low-edge((x2-pos.at(0) - 0.3, x2-pos.at(1) - 0.4), (one2.at(0) - 0.15, one2.at(1) + 0.35))
    bdd-high-edge((x2-pos.at(0) + 0.3, x2-pos.at(1) - 0.4), (zero2.at(0) + 0.15, zero2.at(1) + 0.35))

    content((7, 4), text(weight: "bold", fill: colors.primary)[$not x$])

    // Arrow between them
    content((4.5, 2.5), text(size: 1em)[Different nodes!])
  }),
  caption: [Without complement edges: $x$ and $not x$ require separate nodes with swapped children.],
)

This is wasteful.
If your formula uses both $g$ and $not g$ for some complex subformula $g$, you store the entire $g$ structure twice.
Negation takes $O(|g|)$ time to rebuild everything.

== The Solution: Annotated Edges

The insight: instead of negating the *nodes*, negate the *edge*.

#figure(
  cetz.canvas(length: 1cm, {
    import cetz.draw: *

    // Single node structure
    let x-pos = (4.5, 3)
    let zero = (3.7, 1)
    let one = (5.3, 1)

    bdd-terminal-node(zero, 0)
    bdd-terminal-node(one, 1)
    bdd-decision-node(x-pos, "x")
    bdd-low-edge((x-pos.at(0) - 0.3, x-pos.at(1) - 0.4), (zero.at(0) + 0.15, zero.at(1) + 0.35))
    bdd-high-edge((x-pos.at(0) + 0.3, x-pos.at(1) - 0.4), (one.at(0) - 0.15, one.at(1) + 0.35))

    // Two incoming edges
    // f (positive)
    line((2, 4.5), (x-pos.at(0) - 0.3, x-pos.at(1) + 0.4), stroke: 2pt + colors.success, mark: (
      end: ">",
      fill: colors.success,
    ))
    content((1.5, 4.7), text(weight: "bold", fill: colors.success)[$f$])

    // ¬f (complemented)
    line((7, 4.5), (x-pos.at(0) + 0.3, x-pos.at(1) + 0.4), stroke: 2pt + colors.error, mark: (
      end: ">",
      fill: colors.error,
    ))
    circle((6.2, 4.1), radius: 0.12, fill: white, stroke: 2pt + colors.error)
    content((7.5, 4.7), text(weight: "bold", fill: colors.error)[$not f$])

    // Legend
    content((4.5, -0.3), align(center)[
      #set text(size: 0.8em)
      Same node, different edge annotations.\
      The circle marks a *complement edge*.
    ])
  }),
  caption: [With complement edges: $f$ and $not f$ share the same node. The small circle indicates negation.],
)

#definition(title: "Complement Edge")[
  A *complement edge* is an edge annotated with a negation flag.
  Following a complemented edge *inverts* the semantics of the subgraph.
  This allows $f$ and $not f$ to share the same underlying structure.
]

== The Benefits

=== Space Reduction

Every function $f$ in the BDD implicitly provides $not f$ for free.
In practice, this can reduce node count by 30--50%.

Consider a formula like $(a and b) xor (c and d)$.
XOR involves negation: $p xor q = (p and not q) or (not p and q)$.
Without complement edges, we'd duplicate the $(a and b)$ and $(c and d)$ subgraphs.
With them, we just mark edges as complemented.

=== $O(1)$ Negation

This is the killer feature.
Negating a BDD becomes a single bit operation:

```rust
impl Neg for Ref {
    fn neg(self) -> Self {
        Self(self.0 ^ 1)  // XOR flips the lowest bit
    }
}
```

In Rust, you just write `-f` and get the negated BDD instantly.
No traversal.
No new nodes.
No allocation.

#insight-box[
  The $O(1)$ negation ripples through the entire library.
  XOR, equivalence, and implication all involve negation internally.
  They all become faster because negation is free.
]

== Implementation in bdd-rs

The complement bit is packed into the `Ref` type itself:

#figure(
  cetz.canvas(length: 1cm, {
    import cetz.draw: *

    // Bit layout visualization
    let total = 10
    let index-width = 9
    let comp-width = 1

    // Index portion
    rect((0, 0), (index-width, 0.8), fill: colors.box-definition, stroke: 1pt + colors.primary, name: "index")
    content((index-width / 2, 0.4), text(size: 0.8em, weight: "semibold")[Node Index (bits 1--31)])

    // Complement bit
    rect((index-width, 0), (total, 0.8), fill: colors.box-warning, stroke: 1pt + colors.warning, name: "comp")
    content((index-width + comp-width / 2, 0.4), text(size: 0.8em, weight: "bold")[C])

    // Labels
    content((index-width / 2, -0.4), text(size: 0.7em, fill: colors.text-muted)[Which node in storage])
    content((index-width + comp-width / 2, -0.4), text(size: 0.7em, fill: colors.text-muted)[Neg?])

    // Bit numbers
    content((0.3, 1.2), text(size: 0.7em, fill: colors.text-muted)[31], anchor: "south")
    content((index-width - 0.3, 1.2), text(size: 0.7em, fill: colors.text-muted)[1], anchor: "south")
    content((index-width + comp-width / 2, 1.2), text(size: 0.7em, fill: colors.text-muted)[0], anchor: "south")
  }),
  caption: [Bit layout of `Ref`: the complement flag occupies the lowest bit.],
)

This encoding means:

- `Ref(0)` = node 0, positive = *TRUE* (terminal)
- `Ref(1)` = node 0, negated = *FALSE*
- `Ref(4)` = node 2, positive
- `Ref(5)` = node 2, negated

The API is straightforward:

```rust
impl Ref {
    pub fn id(self) -> NodeId {
        NodeId::from_raw(self.0 >> 1)  // Shift right to get index
    }

    pub fn is_negated(self) -> bool {
        (self.0 & 1) != 0  // Check lowest bit
    }
}
```

== The Canonicity Challenge

Complement edges create an ambiguity.
Consider a node for variable $x$:

#figure(
  cetz.canvas(length: 1cm, {
    import cetz.draw: *

    // Left representation
    let x1 = (2.5, 3)
    bdd-decision-node(x1, "x")
    content((1.5, 2), text(size: 0.8em)[$ell$], anchor: "east")
    content((3.5, 2), text(size: 0.8em)[$h$], anchor: "west")
    line((x1.at(0) - 0.3, x1.at(1) - 0.4), (1.8, 2.2), stroke: (paint: colors.edge-low, dash: "dashed"))
    line((x1.at(0) + 0.3, x1.at(1) - 0.4), (3.2, 2.2), stroke: colors.edge-high)

    content((2.5, 4), text(weight: "bold")[(A)])

    // Middle arrow
    content((5, 2.5), text(size: 1em)[$equiv$])

    // Right representation (negated)
    let x2 = (7.5, 3)
    bdd-decision-node(x2, "x")
    content((6.5, 2), text(size: 0.8em)[$not ell$], anchor: "east")
    content((8.5, 2), text(size: 0.8em)[$not h$], anchor: "west")
    line((x2.at(0) - 0.3, x2.at(1) - 0.4), (6.8, 2.2), stroke: (paint: colors.edge-low, dash: "dashed"))
    circle((7.1, 2.5), radius: 0.08, fill: white, stroke: 1pt + colors.edge-low)
    line((x2.at(0) + 0.3, x2.at(1) - 0.4), (8.2, 2.2), stroke: colors.edge-high)
    circle((7.9, 2.5), radius: 0.08, fill: white, stroke: 1pt + colors.edge-high)

    content((7.5, 4), text(weight: "bold")[(B) with $not$ at root])

    // Explanation
    content((5, 0.5), align(center)[
      #set text(size: 0.8em)
      These represent the *same* function!\
      We need a rule to pick one.
    ])
  }),
  caption: [Ambiguity: `mk(x, l, h)` and `¬mk(x, ¬l, ¬h)` represent the same function.],
)

Without a normalization rule, canonicity breaks --- two different structures for the same function.

=== The Solution: High Edge Convention

`bdd-rs` enforces: *high edges are never complemented*.

When `mk_node` would create a node with a complemented high edge, it flips everything:

```rust
pub fn mk_node(&self, v: Var, low: Ref, high: Ref) -> Ref {
    // Canonicity rule: high edge must be positive
    if high.is_negated() {
        // Flip: ¬mk(v, ¬low, ¬high) = mk(v, low, high)
        return -self.mk_node(v, -low, -high);
    }
    // ... proceed with normal node creation
}
```

#warning-box(title: "The Rule Must Be Consistent")[
  The choice of "high never complemented" vs "low never complemented" is arbitrary.
  What matters is *consistency*.
  CUDD uses low-never-complemented.
  `bdd-rs` uses high-never-complemented.
  Pick one and stick to it.
]

== Traversal with Complements

When traversing a BDD, complement flags must propagate correctly:

```rust
pub fn low_node(&self, node_ref: Ref) -> Ref {
    let low = self.low(node_ref.id());
    if node_ref.is_negated() {
        -low  // Propagate the complement
    } else {
        low
    }
}

pub fn high_node(&self, node_ref: Ref) -> Ref {
    let high = self.high(node_ref.id());
    if node_ref.is_negated() {
        -high  // Propagate the complement
    } else {
        high
    }
}
```

If you're at a complemented reference, both children become complemented.
This propagation continues to the terminals, flipping the final result.

#info-box(title: "Evaluation Rule")[
  A path evaluates to TRUE if it reaches the TRUE terminal through an *even* number of complement edges.
  An odd number of complements flips the result to FALSE.
]

== Terminal Handling

With complements, there's one physical terminal but two logical constants:

Complement edges introduce an ambiguity: $f$ and $not f$ have the same underlying graph.
To maintain canonicity, we need a *normalization rule*.

=== The Problem

Consider a node with children `low` and `high`:
- `mk(x, low, high)` represents $(not x and "low") or (x and "high")$
- `mk(x, -low, -high)` represents $(not x and not "low") or (x and not "high")$

These are negations of each other!
Without normalization, we'd have two representations for the same function.

=== The Solution: High Edge Convention

`bdd-rs` uses the convention: *high edges are never complemented*.

If we try to create a node where `high.is_negated()`, we flip everything:

```rust
pub fn mk_node(&self, v: Var, low: Ref, high: Ref) -> Ref {
    // Canonicity: high edge must be positive
    if high.is_negated() {
        return -self.mk_node(v, -low, -high);
    }
    // ... rest of mk_node
}
```

#warning-box(title: "Normalization Required")[
  With complement edges, we must enforce a normalization rule to maintain canonicity.
  In `bdd-rs`, the convention is: *high edges are never complemented*.
  If a high edge would be complemented, we complement the entire node instead.
]

=== Why High Edge?

The choice of "high edge never complemented" vs "low edge never complemented" is arbitrary but must be consistent.
The high-edge convention is common in the literature and has some advantages:
- Terminal 1 is the "natural" positive terminal
- Following the high edge often represents the "true" case

=== Alternative: Low Edge Convention

Some libraries use the opposite: *low edges are never complemented*.
CUDD, for example, uses this convention.
The important thing is consistency, not the specific choice.

== Impact on Traversal

When traversing a BDD with complement edges, we must propagate the complement flag:

```rust
pub fn low_node(&self, node_ref: Ref) -> Ref {
    let low = self.low(node_ref.id());
    if node_ref.is_negated() {
        -low  // Propagate complement
    } else {
        low
    }
}

pub fn high_node(&self, node_ref: Ref) -> Ref {
    let high = self.high(node_ref.id());
    if node_ref.is_negated() {
        -high  // Propagate complement
    } else {
        high
    }
}
```

If we're at a negated reference, both children become negated.
This maintains the semantic invariant: following a complemented edge negates everything below.

#info-box(title: "Propagation Rule")[
  When traversing through a complemented reference:
  - The children are also complemented
  - This propagates down to the terminals

  A path to terminal 1 through an odd number of complemented edges evaluates to 0.
]

== Impact on Terminal Detection

With complement edges, we have one physical terminal node but two logical constants:

```rust
// Physical: one terminal node at index 0
// Logical: one = @0, zero = ~@0

impl Bdd {
    pub fn is_one(&self, r: Ref) -> bool {
        r.raw() == self.one.raw()  // Non-negated terminal
    }

    pub fn is_zero(&self, r: Ref) -> bool {
        r.raw() == self.zero.raw()  // Negated terminal
    }

    pub fn is_terminal(&self, r: Ref) -> bool {
        r.id().raw() == 0  // Either constant
    }
}
```

The distinction:
- `is_terminal(r)`: Is this a constant (either 0 or 1)?
- `is_one(r)` / `is_zero(r)`: Which specific constant?

== Impact on Operations

=== ITE Normalization

The Apply/ITE algorithm must normalize its arguments for cache efficiency:

```rust
pub fn apply_ite(&self, f: Ref, g: Ref, h: Ref) -> Ref {
    // ...

    // Normalize: f should not be negated
    // ite(¬f, g, h) = ite(f, h, g)
    let (mut f, mut g, mut h) = (f, g, h);
    if f.is_negated() {
        f = -f;
        std::mem::swap(&mut g, &mut h);
    }

    // Normalize: g should not be negated
    // ite(f, ¬g, h) = ¬ite(f, g, ¬h)
    let mut negate_result = false;
    if g.is_negated() {
        negate_result = true;
        g = -g;
        h = -h;
    }

    // ... compute result ...

    if negate_result { -result } else { result }
}
```

This normalization ensures that equivalent computations hit the same cache entry:
- `ite(f, g, h)` and `ite(-f, h, g)` → same cache key
- `ite(f, g, h)` and `ite(f, -g, -h)` → same cache key (result negated)

=== XOR Simplification

XOR has a special relationship with complement edges:

$ f xor g = not (f xor not g) $

This means many XOR computations reduce to existing results with a complement:

```rust
pub fn apply_xor(&self, f: Ref, g: Ref) -> Ref {
    // f ⊕ 1 = ¬f (just flip the bit!)
    if self.is_one(g) {
        return -f;
    }
    // f ⊕ ¬f = 1
    if f == -g {
        return self.one;
    }
    // General case: ite(f, ¬g, g)
    self.apply_ite(f, -g, g)
}
```

=== Equivalence Testing

Equivalence becomes truly $O(1)$:

```rust
// f ≡ g iff they're the same Ref (including complement bit)
f == g  // Direct comparison

// f ≡ ¬g iff f == -g
f == -g
```

No traversal needed --- just compare the 32-bit values.

== Trade-offs

=== Advantages

+ *Space*: Up to 50% fewer nodes
+ *Negation*: $O(1)$ instead of $O(|f|)$
+ *XOR/Equivalence*: Significant speedups
+ *Equality*: $O(1)$ for both $f = g$ and $f = not g$

=== Disadvantages

+ *Complexity*: Every algorithm must handle complements correctly
+ *Bugs*: Easy to forget complement propagation
+ *Cache keys*: Must normalize to avoid redundant entries
+ *Debugging*: Output is harder to interpret

#comparison-table(
  [*Aspect*],
  [*Without Complement Edges*],
  [*With Complement Edges*],
  [Negation],
  [$O(|f|)$],
  [$O(1)$],
  [Node count],
  [Higher],
  [Up to 50% less],
  [Equality check],
  [$O(1)$],
  [$O(1)$],
  [Algorithm complexity],
  [Simpler],
  [More complex],
  [Debugging],
  [Easier],
  [Harder],
)

=== When Complement Edges Hurt

In rare cases, complement edges can slightly hurt cache performance.
The normalization in ITE can cause cache thrashing if the working set has many complementary pairs.
However, this is unusual --- the space and negation benefits almost always dominate.

== Visualization Considerations

When outputting BDDs (e.g., to DOT format), complement edges require special handling:

```rust
// In DOT output:
if edge.is_negated() {
    // Show as dashed line or with "~" label
    println!("  {} -> {} [style=dashed];", from, to);
} else {
    println!("  {} -> {};", from, to);
}
```

Without this, the output would be confusing --- two identical-looking graphs could represent different functions.

== Summary

Complement edges are a powerful optimization:

+ *Representation*: Encode negation in the low bit of `Ref`
+ *Canonicity*: Enforce "high edge never complemented" rule
+ *Traversal*: Propagate complement flag through children
+ *Operations*: Normalize arguments for cache efficiency
+ *Benefits*: $O(1)$ negation, space reduction, faster XOR

The added complexity is well worth the performance gains.
Nearly all production BDD libraries use complement edges.
