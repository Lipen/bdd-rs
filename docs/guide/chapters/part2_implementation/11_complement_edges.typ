#import "../../theme.typ": *

= Complement Edges <ch-complement-edges>

*Complement edges* are an optimization that reduces BDD size and enables $O(1)$ negation.
Instead of creating separate nodes for $f$ and $not f$, we annotate edges with a negation flag.
This chapter explains the concept, its implementation in `bdd-rs`, and the subtleties of maintaining canonicity.

== The Idea

In standard BDDs, $f$ and $not f$ require different nodes.
For example, the BDD for $x$ has a node pointing to 1 (high) and 0 (low).
The BDD for $not x$ needs a different node pointing to 0 (high) and 1 (low).

#example-box(title: "Standard BDDs: f vs. ¬f")[
  BDD for $x$:
  ```
      x
     / \
    0   1
  ```

  BDD for $not x$:
  ```
      x
     / \
    1   0
  ```

  Two separate nodes, even though $not x$ is trivially related to $x$.
]

With complement edges, we mark the *edge* as negated rather than creating a new node:

#example-box(title: "Complement Edges: f and ¬f Share Structure")[
  ```
  f  →  [x]        ¬f  →̃  [x]
        / \              / \
       0   1            0   1
  ```

  The tilde on the edge ($arrow.tilde$) indicates negation.
  Following a complemented edge inverts the semantics.
]

#definition(title: "Complement Edge")[
  A *complement edge* is an edge annotated with a negation flag.
  Following a complemented edge negates the value of the subgraph reached.
  This allows representing $f$ and $not f$ with the same subgraph.
]

== Benefits

=== Space Reduction

Complement edges can reduce node count by up to 50%.
Every function $f$ that appears in a BDD implicitly provides $not f$ for free.

Consider a complex function $g$ appearing multiple times:
- Without complement edges: Need separate nodes for $g$ and $not g$
- With complement edges: Share the $g$ subgraph, mark some edges as complemented

=== $O(1)$ Negation

The most dramatic benefit: negation becomes a *bit flip*:

```rust
impl Neg for Ref {
    fn neg(self) -> Self {
        Ref(self.0 ^ 1)  // XOR with 1 flips the low bit
    }
}
```

Without complement edges, negation requires $O(|f|)$ time to traverse and rebuild the entire BDD.
With complement edges, it's instantaneous.

#insight-box[
  The $O(1)$ negation from complement edges propagates through algorithms.
  XOR, equivalence, and implication all benefit because they involve negation internally.
]

== Representation in bdd-rs

The `Ref` type packs the complement bit into the reference itself:

```rust
#[repr(transparent)]
pub struct Ref(u32);

// Bit layout: [31-bit node index][1-bit complement]
//
// Example:
// - Ref(4) = node 2, not negated (4 = 2<<1 | 0)
// - Ref(5) = node 2, negated     (5 = 2<<1 | 1)
```

=== Creating References

```rust
impl Ref {
    /// Create with explicit negation flag
    pub fn new(id: NodeId, negated: bool) -> Self {
        Self((id.raw() << 1) | (negated as u32))
    }

    /// Positive (non-negated) reference
    pub fn positive(id: NodeId) -> Self {
        Self::new(id, false)
    }

    /// Negative (negated) reference
    pub fn negative(id: NodeId) -> Self {
        Self::new(id, true)
    }
}
```

=== Querying References

```rust
impl Ref {
    /// Extract the node index
    pub fn id(self) -> NodeId {
        NodeId::from_raw(self.0 >> 1)
    }

    /// Check if this reference is negated
    pub fn is_negated(self) -> bool {
        (self.0 & 1) != 0
    }
}
```

=== Negation

```rust
impl Neg for Ref {
    type Output = Self;

    fn neg(self) -> Self {
        Self(self.0 ^ 1)  // Flip the complement bit
    }
}
```

This is the magic: `-x` in Rust negates a BDD in $O(1)$ time.

== Canonical Form with Complements

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
  [*Aspect*], [*Without Complement Edges*], [*With Complement Edges*],
  [Negation], [$O(|f|)$], [$O(1)$],
  [Node count], [Higher], [Up to 50% less],
  [Equality check], [$O(1)$], [$O(1)$],
  [Algorithm complexity], [Simpler], [More complex],
  [Debugging], [Easier], [Harder],
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
