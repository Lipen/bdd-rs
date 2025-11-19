#import "../../theme.typ": *

= Programming with BDDs: The `bdd-rs` Library <programming-with-bdds>

Theory is elegant, but programs need implementations.
The `bdd-rs` library provides a practical, efficient BDD implementation in Rust.

This chapter introduces the API through examples.
We build intuition for how BDD operations work and learn the library's design principles.

== Getting Started

Add `bdd-rs` to your project:

```toml
[dependencies]
bdd-rs = "0.1"
```

Basic imports:

```rust
use bdd_rs::{Bdd, Ref};
```

Two core types:
- `Bdd`: The BDD manager (owns all nodes)
- `Ref`: A lightweight handle to a BDD node

#figure(
  caption: [Manager-centric architecture. The `Bdd` manager owns all nodes in a hash table, maintaining canonicity. `Ref` values are lightweight handles (just node IDs) that point into the manager's storage.],

  cetz.canvas({
    import cetz.draw: *

    // Helper functions
    let draw-manager-box(pos, width, height) = {
      rect(
        pos,
        (pos.at(0) + width, pos.at(1) + height),
        fill: colors.bg-code,
        stroke: colors.primary + 2pt,
        radius: 0.15,
      )
    }

    let draw-hash-entry(pos, var-label, size: 0.8) = {
      let w = 1.2
      let h = 0.5
      rect(pos, (pos.at(0) + w, pos.at(1) + h), fill: white, stroke: colors.secondary + 1pt, radius: 0.05)
      content((pos.at(0) + w / 2, pos.at(1) + h / 2), text(size: size * 1em, fill: colors.secondary)[#var-label])
    }

    let draw-ref-handle(pos, label) = {
      circle(pos, radius: 0.25, fill: colors.success, stroke: colors.success + 1.5pt)
      content(pos, text(fill: white, size: 0.7em, weight: "bold")[#label])
    }

    let draw-pointer(from-pos, to-pos) = {
      line(from-pos, to-pos, stroke: colors.success + 1.5pt, mark: (end: ">"))
    }

    // Manager box
    draw-manager-box((0, 0), 5, 3.5)
    content((2.5, 3.2), text(fill: colors.primary, weight: "bold", size: 0.9em)[`Bdd` Manager], anchor: "north")

    // Hash table visualization
    content((0.3, 2.8), text(fill: colors.text-light, size: 0.75em)[Hash Table:], anchor: "west")

    draw-hash-entry((0.5, 2.2), "Node 1: $(x_1)$", size: 0.7)
    draw-hash-entry((0.5, 1.6), "Node 2: $(x_2)$", size: 0.7)
    draw-hash-entry((0.5, 1.0), "Node 3: $(x_1 and x_2)$", size: 0.7)
    draw-hash-entry((0.5, 0.4), "...", size: 0.7)

    // Cache visualization
    content((2.5, 2.8), text(fill: colors.text-light, size: 0.75em)[Operation Cache:], anchor: "west")
    rect((2.5, 0.4), (4.7, 2.6), fill: white, stroke: colors.accent + 1pt, radius: 0.05)
    content((3.6, 2.2), text(size: 0.65em)[AND(1,2) $->$ 3])
    content((3.6, 1.8), text(size: 0.65em)[OR(1,2) $->$ 4])
    content((3.6, 1.4), text(size: 0.65em)[NOT(1) $->$ 5])
    content((3.6, 0.8), text(size: 0.65em)[...])

    // Ref handles outside manager
    draw-ref-handle((6, 2.5), "x")
    draw-ref-handle((6, 1.5), "y")
    draw-ref-handle((6, 0.5), "f")

    content((6.8, 2.5), text(size: 0.75em)[`Ref` (id=1)], anchor: "west")
    content((6.8, 1.5), text(size: 0.75em)[`Ref` (id=2)], anchor: "west")
    content((6.8, 0.5), text(size: 0.75em)[`Ref` (id=3)], anchor: "west")

    // Pointers from refs to manager
    draw-pointer((5.75, 2.5), (1.7, 2.45))
    draw-pointer((5.75, 1.5), (1.7, 1.85))
    draw-pointer((5.75, 0.5), (1.7, 1.25))

    // Labels
    content(
      (6, 3.5),
      text(fill: colors.text-light, size: 0.75em, style: "italic")[Lightweight handles],
      anchor: "west",
    )
    content(
      (0.5, -0.3),
      text(fill: colors.text-light, size: 0.75em, style: "italic")[Centralized storage],
      anchor: "west",
    )
  }),
) <fig:manager-architecture>

#info-box(title: "Manager-Centric Design")[
  *Critical invariant:* All BDD operations go through the manager.

  Think of `Ref` as just a handle --- like a pointer to a node.
  The manager owns the actual nodes and maintains canonicity through hash consing.
  You should never call methods directly on `Ref`; instead, use manager methods for all operations.
]== Creating Variables

Variables are the building blocks.

```rust
let bdd = Bdd::default();

let x = bdd.mk_var(1);  // Variable x (id=1)
let y = bdd.mk_var(2);  // Variable y (id=2)
let z = bdd.mk_var(3);  // Variable z (id=3)
```

#warning-box[
  *Variables are 1-indexed.*

  Variable 0 is reserved internally.
  Always use IDs starting from 1.

  ```rust
  let bad = bdd.mk_var(0);  // ✗ Error! Don't use 0
  let good = bdd.mk_var(1); // ✓ Correct
  ```
]

Variable ordering is implicit: variables with lower IDs come first.

```rust
// Ordering: x₁ < x₂ < x₃ < ...
let x1 = bdd.mk_var(1);
let x2 = bdd.mk_var(2);
let x3 = bdd.mk_var(3);
```

Once you create a variable, you can't change the ordering.
Choose wisely based on your problem structure.

== Boolean Operations

Combine BDDs with standard Boolean operators.

=== AND, OR, NOT

```rust
let bdd = Bdd::default();
let x = bdd.mk_var(1);
let y = bdd.mk_var(2);

// Conjunction: x ∧ y
let and_xy = bdd.apply_and(x, y);

// Disjunction: x ∨ y
let or_xy = bdd.apply_or(x, y);

// Negation: ¬x
let not_x = bdd.apply_not(x);

// Compound: (x ∧ y) ∨ ¬z
let z = bdd.mk_var(3);
let expr = bdd.apply_or(
    bdd.apply_and(x, y),
    bdd.apply_not(z),
);
```

#info-box(title: "Functional Style")[
  Operations return _new_ `Ref` values.
  Original BDDs are unchanged (immutable).

  ```rust
  let f = bdd.apply_and(x, y);
  let g = bdd.apply_or(f, z);
  // f still represents (x ∧ y)
  // g represents ((x ∧ y) ∨ z)
  ```
]

=== XOR and Equivalence

```rust
// XOR: x ⊕ y = (x ∧ ¬y) ∨ (¬x ∧ y)
let xor_xy = bdd.apply_xor(x, y);

// Equivalence: x ↔ y = (x ∧ y) ∨ (¬x ∧ ¬y)
let iff_xy = bdd.apply_iff(x, y);
```

=== Implication

```rust
// Implication: x → y = ¬x ∨ y
let implies = bdd.apply_or(
    bdd.apply_not(x),
    y,
);

// Or use direct method if available
// let implies = bdd.apply_implies(x, y);
```

== Constants

Special BDDs representing true and false.

```rust
let tru = bdd.mk_true();   // Always 1
let fals = bdd.mk_false(); // Always 0

// Identities
let id1 = bdd.apply_or(x, tru);     // = true
let id2 = bdd.apply_and(x, fals);   // = false
let id3 = bdd.apply_and(x, tru);    // = x
let id4 = bdd.apply_or(x, fals);    // = x
```

These are useful for building complex formulas incrementally.

== Equality and Satisfiability

Thanks to canonicity, equality is trivial.

```rust
let f = bdd.apply_and(x, y);
let g = bdd.apply_and(x, y);

// Pointer equality (O(1))
assert!(f == g);  // Same BDD node!

let h = bdd.apply_or(x, y);
assert!(f != h);  // Different functions
```

Check satisfiability:

```rust
let f = bdd.apply_and(x, bdd.apply_not(x));  // x ∧ ¬x

// Check if satisfiable
if f == bdd.mk_false() {
    println!("Unsatisfiable");
} else {
    println!("Satisfiable");
}
```

#example-box(number: "4.1", title: "Tautology Checking")[
  A formula is a tautology if it equals true.

  ```rust
  // Law of excluded middle: x ∨ ¬x
  let lem = bdd.apply_or(x, bdd.apply_not(x));

  assert!(lem == bdd.mk_true());  // Tautology!
  ```
]

== Building Complex Formulas

Real applications involve complex expressions.

#example-box(number: "4.2", title: "Majority Function")[
  Majority of three inputs: at least two are true.

  $"majority"(x, y, z) = (x and y) or (x and z) or (y and z)$

  ```rust
  let bdd = Bdd::default();
  let x = bdd.mk_var(1);
  let y = bdd.mk_var(2);
  let z = bdd.mk_var(3);

  let xy = bdd.apply_and(x, y);
  let xz = bdd.apply_and(x, z);
  let yz = bdd.apply_and(y, z);

  let majority = bdd.apply_or(xy, bdd.apply_or(xz, yz));

  // Verify it's not always true
  assert!(majority != bdd.mk_true());

  // Verify it's satisfiable
  assert!(majority != bdd.mk_false());
  ```
]

#example-box(number: "4.3", title: "Full Adder")[
  A 1-bit full adder:

  `sum = a ⊕ b ⊕ carry_in`, `carry_out = (a ∧ b) ∨ (carry_in ∧ (a ⊕ b))`

  ```rust
  let a = bdd.mk_var(1);
  let b = bdd.mk_var(2);
  let cin = bdd.mk_var(3);

  // Sum: a ⊕ b ⊕ cin
  let sum = bdd.apply_xor(
      bdd.apply_xor(a, b),
      cin,
  );

  // Carry out: (a ∧ b) ∨ (cin ∧ (a ⊕ b))
  let ab = bdd.apply_and(a, b);
  let xor_ab = bdd.apply_xor(a, b);
  let cin_xor = bdd.apply_and(cin, xor_ab);
  let cout = bdd.apply_or(ab, cin_xor);

  println!("Full adder constructed");
  ```
]

== Quantification

Eliminate variables via existential or universal quantification.

=== Existential Quantification

$exists x . f$ asks: "Is there _any_ value of $x$ making $f$ true?"

```rust
let f = bdd.apply_and(x, y);  // x ∧ y

// ∃x. (x ∧ y) = y
let exists_x = bdd.exists(f, 1);  // Quantify out variable 1 (x)

assert!(exists_x == y);
```

Intuition: OR over both possible values of x.

$exists x . f = f[x <- 0] or f[x <- 1]$

=== Universal Quantification

$forall x . f$ asks: "Does $f$ hold for _all_ values of $x$?"

```rust
let f = bdd.apply_or(x, y);  // x ∨ y

// ∀x. (x ∨ y) = y
let forall_x = bdd.forall(f, 1);

assert!(forall_x == y);
```

Intuition: AND over both possible values of x.

$forall x . f = f[x <- 0] and f[x <- 1]$

#example-box(number: "4.4", title: "Quantification in Action")[
  Consider: $f(x, y, z) = (x and y) or z$

  ```rust
  let f = bdd.apply_or(
      bdd.apply_and(x, y),
      z,
  );

  // ∃x. f = (false ∧ y) ∨ z ∨ (true ∧ y) ∨ z = y ∨ z
  let ex = bdd.exists(f, 1);
  let expected = bdd.apply_or(y, z);
  assert!(ex == expected);

  // ∀y. f = (x ∧ false) ∨ z ∧ (x ∧ true) ∨ z
  //       = z ∧ (x ∨ z) = z
  let ay = bdd.forall(f, 2);
  assert!(ay == z);
  ```
]

== Cofactors: Restricting Variables

Cofactor: BDD with one variable fixed to a value.

- *Positive cofactor:* $f[x <- 1]$ (assume $x = 1$)
- *Negative cofactor:* $f[x <- 0]$ (assume $x = 0$)

```rust
let f = bdd.apply_and(
    bdd.apply_or(x, y),
    z,
);  // (x ∨ y) ∧ z

// Restrict x to true: (true ∨ y) ∧ z = z
let f_x1 = bdd.restrict(f, 1, true);
assert!(f_x1 == z);

// Restrict x to false: (false ∨ y) ∧ z = y ∧ z
let f_x0 = bdd.restrict(f, 1, false);
let expected = bdd.apply_and(y, z);
assert!(f_x0 == expected);
```

Cofactors are the foundation of many BDD algorithms.

Shannon expansion:
$f = (x and f[x <- 1]) or (not x and f[x <- 0])$

#figure(
  caption: [Shannon expansion decomposes a BDD at variable $x$ into two cofactors. The BDD for $f$ has high edge pointing to $f[x <- 1]$ and low edge to $f[x <- 0]$. This recursive decomposition is the foundation of the BDD data structure.],

  cetz.canvas({
    import cetz.draw: *

    // Helper functions
    let draw-function-box(pos, label, color: colors.secondary) = {
      rect(
        (pos.at(0) - 0.8, pos.at(1) - 0.4),
        (pos.at(0) + 0.8, pos.at(1) + 0.4),
        fill: colors.bg-code,
        stroke: color + 1.5pt,
        radius: 0.1,
      )
      content(pos, text(fill: color, size: 0.8em)[#label])
    }

    let draw-var-node(pos, var-label) = {
      circle(pos, radius: 0.35, fill: white, stroke: colors.primary + 1.5pt)
      content(pos, text(fill: colors.primary, size: 0.8em)[#var-label])
    }

    let draw-edge(from-pos, to-pos, dashed: false, label: none) = {
      let stroke-style = if dashed { (paint: colors.error, dash: "dashed", thickness: 1.5pt) } else {
        colors.success + 1.5pt
      }
      line(from-pos, to-pos, stroke: stroke-style, mark: (end: ">"))
      if label != none {
        let mid-x = (from-pos.at(0) + to-pos.at(0)) / 2
        let mid-y = (from-pos.at(1) + to-pos.at(1)) / 2
        content((mid-x, mid-y), text(size: 0.65em, fill: colors.text-light)[#label], anchor: "south")
      }
    }

    // Original function
    draw-function-box((0, 3), $f(x, y, z)$, color: colors.primary)

    // Equals sign
    content((0, 2), text(size: 1.2em)[$=$])

    // Shannon expansion formula
    content((0, 1), text(size: 0.85em)[$(x and f[x <- 1]) or (not x and f[x <- 0])$])

    // Visual representation
    content((0, -0.3),text(fill: colors.text-light, size: 0.75em)[Visual structure:], anchor: "north")

    draw-var-node((0, -1.2), $x$)

    draw-function-box((-2, -2.8), $f[x <- 1]$)
    draw-function-box((2, -2.8), $f[x <- 0]$)

    draw-edge((0, -1.55), (-2, -2.4), label: "high")
    draw-edge((0, -1.55), (2, -2.4), dashed: true, label: "low")

    // Annotations
    content((-3.5, -2.8), text(size: 0.7em, fill: colors.success)[assume $x = 1$], anchor: "east")
    content((3.5, -2.8), text(size: 0.7em, fill: colors.error)[assume $x = 0$], anchor: "west")
  }),
) <fig:shannon-expansion>

#info-box(title: "Cofactors vs Quantification")[
  - *Cofactor:* Fixes variable to specific value
  - *Quantification:* Eliminates variable (OR or AND over both values)

  Relation:
  - $exists x . f = f[x <- 0] or f[x <- 1]$
  - $forall x . f = f[x <- 0] and f[x <- 1]$
]

== Counting Solutions

How many assignments satisfy a BDD?

```rust
let f = bdd.apply_or(x, y);  // x ∨ y

// How many of the 4 possible assignments (x,y) satisfy f?
// Satisfying: (0,1), (1,0), (1,1) → 3 solutions
let count = bdd.count_solutions(f, 2);  // 2 variables
assert_eq!(count, 3);
```

For large BDDs, use logarithmic counting to avoid overflow.

```rust
// Returns log₂(solution count)
let log_count = bdd.log_count_solutions(f, 2);
```

== Path Enumeration

Extract satisfying assignments explicitly.

```rust
let f = bdd.apply_and(x, y);  // x ∧ y

// Get all satisfying paths
let paths = bdd.all_paths(f);

// Paths are Vec<i32>: positive=true, negative=false
// For x ∧ y, we get: [1, 2] meaning x=true, y=true
for path in paths {
    println!("Solution: {:?}", path);
}
```

Path format:
- Positive integer: variable is true (e.g., `1` means x₁=true)
- Negative integer: variable is false (e.g., `-2` means x₂=false)

#example-box(number: "4.5", title: "Path Enumeration")[
  ```rust
  let f = bdd.apply_or(
      bdd.apply_and(x, bdd.apply_not(y)),
      bdd.apply_and(bdd.apply_not(x), y),
  );  // (x ∧ ¬y) ∨ (¬x ∧ y) = x ⊕ y

  let paths = bdd.all_paths(f);

  // Two solutions:
  // [1, -2]: x=true, y=false
  // [-1, 2]: x=false, y=true
  assert_eq!(paths.len(), 2);
  ```
]

#warning-box[
  *Exponential enumeration.*

  If BDD has many solutions, `all_paths` returns exponentially many.
  Use with caution.
  Prefer `count_solutions` if you only need the count.
]

== Visualization with DOT

BDDs are graphs; visualize them!

```rust
let f = bdd.apply_and(x, bdd.apply_or(y, z));  // x ∧ (y ∨ z)

// Generate DOT format
let dot = bdd.to_dot(f);

// Save to file
std::fs::write("bdd.dot", dot).unwrap();
```

Then render with Graphviz:

```bash
dot -Tpng bdd.dot -o bdd.png
```

The visualization shows:
- Nodes labeled with variable IDs
- Dashed edges for low (variable=0)
- Solid edges for high (variable=1)
- Terminal nodes (0 and 1)

This is invaluable for debugging and understanding BDD structure.

== Performance Considerations

=== Caching and Memoization

The manager automatically caches operation results.

```rust
// These are both cheap: result cached after first call
let f1 = bdd.apply_and(x, y);
let f2 = bdd.apply_and(x, y);  // Cache hit!
```

Cache grows over time.
For long-running analyses, consider:
- Clearing cache periodically
- Limiting cache size (if supported)

=== Variable Ordering

Remember: variable ordering is critical.

#figure(
  caption: [Variable ordering impact on BDD size. Both BDDs represent $(x_1 and y_1) or (x_2 and y_2)$. Left: good ordering groups related variables $(x_1, y_1, x_2, y_2)$ resulting in 6 nodes. Right: bad ordering interleaves them $(x_1, x_2, y_1, y_2)$ resulting in 8 nodes. For this simple example the difference is small, but for larger problems bad ordering causes exponential blowup.],

  cetz.canvas({
    import cetz.draw: *

    // Helper functions
    let draw-bdd-node(pos, label) = {
      circle(pos, radius: 0.3, fill: white, stroke: colors.primary + 1.5pt)
      content(pos, text(fill: colors.primary, size: 0.75em)[#label])
    }

    let draw-terminal(pos, value) = {
      let color-choice = if value == "1" { colors.success } else { colors.error }
      rect(
        (pos.at(0) - 0.25, pos.at(1) - 0.25),
        (pos.at(0) + 0.25, pos.at(1) + 0.25),
        fill: color-choice,
        stroke: color-choice + 1.5pt,
        radius: 0.05,
      )
      content(pos, text(fill: white, size: 0.75em, weight: "bold")[#value])
    }

    let draw-bdd-edge(from-pos, to-pos, is-low: false) = {
      let stroke-style = if is-low { (paint: colors.error, dash: "dashed", thickness: 1pt) } else {
        colors.success + 1pt
      }
      line(from-pos, to-pos, stroke: stroke-style, mark: (end: ">"))
    }

    // Good ordering
    content((-3, 3.5), text(fill: colors.success, weight: "bold", size: 0.9em)[Good: $(x_1, y_1, x_2, y_2)$])
    content((-3, 3), text(fill: colors.text-light, size: 0.75em)[6 nodes])

    draw-bdd-node((-3, 2.2), $x_1$)
    draw-bdd-node((-4, 1.2), $y_1$)
    draw-bdd-node((-2, 1.2), $x_2$)
    draw-bdd-node((-2.5, 0.2), $y_2$)
    draw-terminal((-4, 0.2), "1")
    draw-terminal((-1.5, 0.2), "0")

    // Good ordering edges
    draw-bdd-edge((-3, 1.9), (-4, 1.5))
    draw-bdd-edge((-3, 1.9), (-2, 1.5), is-low: true)
    draw-bdd-edge((-4, 0.9), (-4, 0.45))
    draw-bdd-edge((-4, 0.9), (-1.5, 0.45), is-low: true)
    draw-bdd-edge((-2, 0.9), (-2.5, 0.5))
    draw-bdd-edge((-2, 0.9), (-1.5, 0.45), is-low: true)
    draw-bdd-edge((-2.5, -0.1), (-4, 0.0))
    draw-bdd-edge((-2.5, -0.1), (-1.5, 0.0), is-low: true)

    // Bad ordering
    content((3, 3.5), text(fill: colors.error, weight: "bold", size: 0.9em)[Bad: $(x_1, x_2, y_1, y_2)$])
    content((3, 3), text(fill: colors.text-light, size: 0.75em)[8 nodes])

    draw-bdd-node((3, 2.2), $x_1$)
    draw-bdd-node((2, 1.4), $x_2$)
    draw-bdd-node((4, 1.4), $x_2$)
    draw-bdd-node((1.5, 0.6), $y_1$)
    draw-bdd-node((2.5, 0.6), $y_1$)
    draw-bdd-node((3.5, 0.6), $y_1$)
    draw-terminal((2, -0.2), "1")
    draw-terminal((4, -0.2), "0")

    // Bad ordering edges (simplified to show complexity)
    draw-bdd-edge((3, 1.9), (2, 1.7))
    draw-bdd-edge((3, 1.9), (4, 1.7), is-low: true)
    draw-bdd-edge((2, 1.1), (1.5, 0.9))
    draw-bdd-edge((2, 1.1), (2.5, 0.9), is-low: true)
    draw-bdd-edge((4, 1.1), (3.5, 0.9))
    draw-bdd-edge((4, 1.1), (4, 0.05), is-low: true)
    draw-bdd-edge((1.5, 0.3), (2, 0.05))
    draw-bdd-edge((1.5, 0.3), (4, 0.05), is-low: true)
    draw-bdd-edge((2.5, 0.3), (2, 0.05))
    draw-bdd-edge((2.5, 0.3), (4, 0.05), is-low: true)
    draw-bdd-edge((3.5, 0.3), (2, 0.05))
    draw-bdd-edge((3.5, 0.3), (4, 0.05), is-low: true)
  }),
) <fig:variable-ordering-impact>

The best practice is grouping related variables together --- those from the same statement or representing the same object.
Order control variables before data variables when possible, and leverage any domain knowledge about your problem's structure.

Bad example:

```rust
// Interleaving unrelated variables
let x1 = bdd.mk_var(1);  // From statement A
let y1 = bdd.mk_var(2);  // From statement B
let x2 = bdd.mk_var(3);  // From statement A
let y2 = bdd.mk_var(4);  // From statement B
```

This interleaves variables from different statements, forcing the BDD to alternate between unrelated concerns.

Good example:

```rust
// Grouping related variables
let x1 = bdd.mk_var(1);  // From statement A
let x2 = bdd.mk_var(2);  // From statement A
let y1 = bdd.mk_var(3);  // From statement B
let y2 = bdd.mk_var(4);  // From statement B
```

Grouping variables from the same statement allows the BDD to exploit structural relationships.

=== When to Use BDDs?

BDDs excel when your problem has Boolean structure --- control flow, flags, or state machines.
They shine when many substructures are shared across different parts of the problem.
Their canonicity makes them perfect when you need efficient equality checks.

However, BDDs struggle with problems that lack inherent structure, like random formulas.
Large bit-vector arithmetic, especially multiplication, defeats BDD compression.
Some problems simply have variable orderings that are inherently bad no matter how you arrange them.

For such cases, consider alternatives like SAT solvers or SMT solvers instead.

== Common Pitfalls

=== Pitfall 1: Using Variable 0

```rust
let bad = bdd.mk_var(0);  // ✗ Reserved!
// PANIC: Variable index should not be zero
```

Always start from 1.

=== Pitfall 2: Calling Methods on Ref

```rust
let x = bdd.mk_var(1);

// ✗ Wrong: Ref has no such method
// let y = x.and(z);

// ✓ Correct: through manager
let y = bdd.apply_and(x, z);
```

All operations go through `Bdd` manager.

=== Pitfall 3: Ignoring Variable Ordering

```rust
// Bad: creates variables in random order
for id in random_ids {
    let var = bdd.mk_var(id);
}

// Good: plan ordering upfront
let ordered_vars: Vec<_> = (1..=n)
    .map(|id| bdd.mk_var(id))
    .collect();
```

=== Pitfall 4: Over-Enumeration

```rust
// ✗ May explode: millions of paths
let paths = bdd.all_paths(huge_bdd);

// ✓ Better: just count
let count = bdd.count_solutions(huge_bdd, n_vars);
```

== Summary

The `bdd-rs` library provides:
- Manager-centric API: all operations through `Bdd`
- Standard Boolean operations: AND, OR, NOT, XOR, etc.
- Quantification: existential and universal
- Cofactors: restrict variables
- Solution counting and enumeration
- DOT visualization

Key principles:
- Variables are 1-indexed
- Operations are immutable (return new `Ref`)
- Canonicity gives $O(1)$ equality
- Variable ordering matters

With these primitives, we can build sophisticated analyses.

In the next chapter, we implement a simple abstract interpreter using BDDs to track control flow.

#chapter-summary(
  [
    *Manager-centric design: all operations through `Bdd`.*
    `Ref` is a lightweight handle. The manager owns nodes and maintains canonicity.
  ],
  [
    *Variables are 1-indexed.*
    Variable 0 is reserved. Always use IDs starting from 1.
  ],
  [
    *Boolean operations: AND, OR, NOT, XOR, IFF.*
    All return new `Ref` values. Original BDDs are immutable.
  ],
  [
    *Equality is pointer comparison.*
    Thanks to canonicity, `f == g` checks if they represent the same function in $O(1)$ time.
  ],
  [
    *Quantification eliminates variables.*
    $exists x . f$ ORs over $x$ values. $forall x . f$ ANDs over $x$ values.
  ],
  [
    *Cofactors restrict variables.*
    $f[
      x <- v]$ fixes $x$ to value $v$. Foundation of BDD algorithms.
  ],
  [
    *Solution counting and enumeration.*
    `count_solutions` is efficient. `all_paths` may explode for large BDDs.
  ],
  [
    *DOT visualization for debugging.*
    Generate graphs to understand BDD structure and diagnose issues.
  ],
  [
    *Performance depends on variable ordering.*
    Group related variables. Use domain knowledge. Bad ordering = exponential blowup.
  ],
  [
    *Main insight:*
    `bdd-rs` provides practical tools for BDD manipulation, enabling implementation of symbolic analyses with straightforward API.
  ],
)

#v(2em)
