#import "../../theme.typ": *

= API Reference <appendix-api>

Quick reference for the `bdd-rs` API.
For complete documentation, see the rustdoc.

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
let x = bdd.variable(1);
let y = bdd.variable(2);

// Variables are cached — calling again returns same Ref
assert_eq!(bdd.variable(1), x);
```

#warning-box(title: "Variable Indexing")[
  Variables are *1-indexed*.
  Variable 0 is reserved for internal use.
  Use `Var(1)`, `Var(2)`, etc.
]

== Boolean Operations

#comparison-table(
  [Operation], [Method], [Notes],
  [NOT], [`bdd.not(x)` or `-x`], [$O(1)$ with complement edges],
  [AND], [`bdd.and(x, y)`], [],
  [OR], [`bdd.or(x, y)`], [],
  [XOR], [`bdd.xor(x, y)`], [],
  [NAND], [`bdd.nand(x, y)`], [],
  [NOR], [`bdd.nor(x, y)`], [],
  [Implies], [`bdd.implies(x, y)`], [$x -> y$],
  [IFF], [`bdd.equiv(x, y)`], [$x <-> y$],
  [ITE], [`bdd.ite(c, t, e)`], [If c then t else e],
)

```rust
// Examples
let f = bdd.and(x, y);           // x ∧ y
let g = bdd.or(x, bdd.not(y));   // x ∨ ¬y
let h = bdd.ite(c, f, g);        // if c then f else g
```

== Queries

```rust
// Terminal checks
bdd.is_zero(f)     // Is f ≡ 0?
bdd.is_one(f)      // Is f ≡ 1?
bdd.is_const(f)    // Is f terminal?

// Satisfiability
bdd.is_sat(f)      // f ≢ 0
bdd.is_tautology(f) // f ≡ 1

// Size metrics
bdd.size(f)                    // Nodes in subgraph
bdd.sat_count(f, num_vars)     // Satisfying assignments
bdd.node_count()               // Total nodes in manager
```

== Cofactors and Restriction

```rust
// Low/high cofactors
let f_low = bdd.low(f);   // f|_{top_var=0}
let f_high = bdd.high(f); // f|_{top_var=1}

// Restriction to specific variable
let f_x0 = bdd.restrict(f, Var(1), false);  // f|_{x₁=0}
let f_x1 = bdd.restrict(f, Var(1), true);   // f|_{x₁=1}
```

== Quantification

```rust
// Existential: ∃x. f = f|_{x=0} ∨ f|_{x=1}
let exists_x = bdd.exists(f, Var(1));

// Universal: ∀x. f = f|_{x=0} ∧ f|_{x=1}
let forall_x = bdd.forall(f, Var(1));

// Over multiple variables
let cube = bdd.cube(&[Var(1), Var(2)]);
let exists_xy = bdd.exists_cube(f, cube);
```

== Composition

```rust
// Substitute g for variable x in f
let result = bdd.compose(f, Var(1), g);  // f[x₁ := g]
```

== Visualization

```rust
// Generate DOT format
let dot = bdd.to_dot(f);

// With custom options
let dot = bdd.to_dot_opts(f, DotOpts {
    show_complement: true,
    ..Default::default()
});

// Write to file, then render
std::fs::write("bdd.dot", dot)?;
// $ dot -Tpng bdd.dot -o bdd.png
```

== Garbage Collection

```rust
// Mark roots and collect
bdd.gc(&[f, g, h]);

// Statistics
let stats = bdd.stats();
println!("Nodes: {}, Peak: {}", stats.nodes, stats.peak_nodes);
```

#info-box(title: "GC Best Practices")[
  - Call `gc()` periodically during long computations
  - Always pass *all* BDDs you need to keep as roots
  - Unreachable nodes are freed, invalid `Ref`s will panic
]
