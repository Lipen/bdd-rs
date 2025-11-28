#import "../../theme.typ": *

= API Reference <appendix-api>

// PLAN: Quick reference for bdd-rs API.
// Target length: 6-8 pages

== Manager Creation

```rust
// Create with default settings
let bdd = Bdd::default();

// Create with specific capacity (2^bits nodes)
let bdd = Bdd::new(20);  // Up to ~1M nodes
```

== Variable Creation

```rust
// Create a variable (1-indexed)
let x = bdd.mk_var(1);
let y = bdd.mk_var(2);

// Variables are cached — calling again returns same Ref
assert_eq!(bdd.mk_var(1), x);
```

== Boolean Operations

```rust
// Basic operations
let not_x = bdd.apply_not(x);        // ¬x
let and_xy = bdd.apply_and(x, y);    // x ∧ y
let or_xy = bdd.apply_or(x, y);      // x ∨ y
let xor_xy = bdd.apply_xor(x, y);    // x ⊕ y

// Implication and equivalence
let imp = bdd.apply_imp(x, y);       // x → y
let iff = bdd.apply_iff(x, y);       // x ↔ y

// If-then-else
let ite = bdd.apply_ite(c, t, e);    // if c then t else e

// Negation via operator
let neg_x = -x;                       // ¬x (O(1) with complement edges)
```

== Queries

```rust
// Terminal checks
bdd.is_zero(f)     // Is f ≡ 0?
bdd.is_one(f)      // Is f ≡ 1?
bdd.is_terminal(f) // Is f a terminal node?

// Size and counting
bdd.size(f)                    // Number of nodes in subgraph
bdd.sat_count(f, num_vars)     // Number of satisfying assignments
bdd.num_nodes()                // Total allocated nodes
```

== Cofactors and Restriction

```rust
// Single variable restriction
let f_x0 = bdd.restrict(f, 1, false);  // f|_{x₁=0}
let f_x1 = bdd.restrict(f, 1, true);   // f|_{x₁=1}

// Cube restriction (multiple variables)
let result = bdd.cofactor_cube(f, [1, -2, 3]);  // f|_{x₁=1, x₂=0, x₃=1}
```

== Quantification

```rust
// Existential quantification
let exists_x = bdd.exists(f, Var(1));

// Universal quantification
let forall_x = bdd.forall(f, Var(1));

// Multiple variables
let exists_xy = bdd.exists_set(f, &[Var(1), Var(2)]);
```

== Visualization

```rust
// Generate DOT format
let dot_string = bdd.to_dot(f);

// Write to file
std::fs::write("bdd.dot", dot_string)?;
// Then: dot -Tpng bdd.dot -o bdd.png
```

== Garbage Collection

```rust
// Manually trigger GC with specified roots
bdd.collect_garbage(&[f, g, h]);
```
