#import "../../theme.typ": *

= Points-to and Dynamic Type Domains <ch-points-types>

#reading-path(path: "advanced") #h(0.7em) #reading-path(path: "implementation")

Heap-manipulating programs require alias reasoning and heap modeling, while dynamic languages (and languages with runtime checks) require tracking runtime types.
This chapter presents a lightweight may-points-to abstraction with allocation-site sensitivity and a flow-sensitive dynamic type domain, including concretizations, transfer functions, precision tradeoffs, and soundness considerations.

== Program Model and Sensitivities

We assume a first-order, imperative core language with variables `Var`, allocation sites `Site` (identified by program points), and fields `Fld`.
Analyses may be:

- Flow-insensitive vs. flow-sensitive (this chapter prefers flow-sensitive states at program points).
- Context-insensitive vs. context-sensitive (see @ch-interprocedural for $k$-limited call-strings).
- Field-insensitive vs. field-sensitive (we recommend field-sensitive stores for precision).

== May/Must Aliasing and Allocation Sites

#definition(title: "Points-to Map and Concretization")[
  A may-points-to map is a function $"PT": "Var" -> cal(P)("Site")$.
  Its concretization $gamma_"PT" ("PT")$ is the set of concrete heaps where, for each pointer variable $p$, any concrete location referenced by $p$ belongs to $"PT"(p)$.

  Ordering: $"PT"_1 <= "PT"_2$ iff $forall p . "PT"_1(p) subset.eq "PT"_2(p)$.
  Join/meet: pointwise union/intersection.
  Widening: cap $|"PT"(p)|$ and collapse excess sites to a summary site.
]

#definition(title: "Abstract Store and Strong/Weak Updates")[
  The abstract store $hat(sigma): "Site" -> V_A$ maps allocation sites to abstract values in some domain $V_A$ (e.g., intervals, products).
  A load `x = *p` computes $ljoin.big_(s in "PT"(p)) hat(sigma)(s)$.
  A store `*p = v` performs a strong update if $"PT"(p) = \{s\}$ (singleton), otherwise a weak update (join into all $s in "PT"(p)$).
]

#example-box(title: "Allocation-Site Sensitivity")[
  Sites are identified by program points (e.g., the `new` instruction id).
  Different allocation sites of the same class remain distinct, improving precision over type-only abstraction.
  Context-sensitivity can be added by call-strings of length $k$ (@ch-interprocedural), yielding site keys like `(site, context_k)`.
]

== Dynamic Type Domain

#definition(title: "Type-Set Domain and Concretization")[
  For each variable $x$, the abstract type is a finite set $"Type"(x) subset.eq "Types"$ where $"Types"$ includes base types (Int, Str, Bool, ...) and object types $"Obj"[C]$ for class $C$.
  Concretization $gamma_T$ maps type sets to the union of concrete values inhabiting any member type.

  Ordering: pointwise subset on variables.
  Join/meet: pointwise union/intersection.
  Narrowing: remove types refuted by control-flow tests.
]

Branches refine types:

- `if is_int(x) { ... }` narrows $"Type"(x)$ to include Int in the then-branch and exclude Int in the else-branch.
- Pattern matching exhaustiveness is checked by emptiness of the residual type set.

== Sound Transfer Functions

- Allocation: `p = new C()` adds the current site $s$ to $"PT"(p)$ and sets $"Type"(p) supset.eq \{"Obj"[C]\}$.
- Copy: `q = p` yields $"PT"(q) supset.eq "PT"(p)$ and $"Type"(q) supset.eq "Type"(p)$.
- Field read: `x = p.f` loads $ljoin.big_(s in "PT"(p)) "Store"(s).f$ (use a product domain for field maps).
- Field write: `p.f = v` performs strong/weak updates across $"PT"(p)$ at field `f`.
- Cast/checks: Guards like `x is C` refine $"Type"(x)$; failed branches refute incompatible types.

#theorem(title: "Soundness of Weak Updates (Sketch)")[
  Let $llb - rrb$ be concrete semantics and $("PT", hat(sigma))$ be the abstract state.
  If a store `*p = v` is applied abstractly by joining $v$ into all sites $s in "PT"(p)$, then $gamma("PT", hat(sigma)')$ over-approximates all concrete heaps reachable by the concrete store.
]

#proof[
  Any concrete pointer value of `p` references some location in $gamma_("PT") ("PT"(p))$.
  Joining into all abstract targets yields a state that includes all possible concrete updates.
  Precision is lost compared to strong updates, but soundness holds by monotonicity of join and the definition of $gamma$.
]

== Cooperation with Numeric and Control Domains

- BDD control refines types and aliases under guards, enabling path-sensitive reasoning about `is_*` checks and nullness.
- Numeric domains constrain object fields (e.g., array length, index intervals) via reduced products.
- String and automata domains model string-typed fields; reductions trim infeasible states (see @ch-strings-automata).

#definition(title: "Reduced Product with Store Values")[
  If $V_A$ is a product (e.g., numeric × string), stores refine by mutual reduction: update, then apply a local $rho$ to propagate constraints across fields and back to aliases.
]

== Precision vs. Performance: What to Bound

- Limit $|"PT"(p)|$ per variable; introduce a summary site to capture the tail.
- Use field-sensitivity selectively (e.g., for frequently accessed fields).
- Apply k-limited context sensitivity (call-strings) at hot heap constructors only (@ch-interprocedural).
- Prefer strong updates when $"PT"(p)$ is a singleton --- design the iteration to detect and exploit this case.

#warning-box(title: "Heap Explosion and Summarization")[
  Without bounds, contexts × sites × fields can explode combinatorially.
  Summarize arrays/collections, collapse rarely-touched sites, and cap determinization in cooperating domains.
]

== Worked Micro-Example

```rust
let p = new C();      // site s1: PT(p) = {s1}, Type(p) ⊇ {Obj[C]}
let q = new C();      // site s2: PT(q) = {s2}
p.f = 3;              // strong update at s1.f
q.f = 5;              // strong update at s2.f
let r = if cond { p } else { q }; // PT(r) = {s1, s2}
let x = r.f;          // load: Store(s1).f ⊔ Store(s2).f ⇒ interval [3,5]
```

This load uses a weak join across two targets, remaining sound and flow-sensitive.
If later the analysis learns `r == p` on some path, BDD control enables a strong update/load on that path only.

== Related Sensitivities and Variants

- Object sensitivity: context key is the receiver object allocation site for methods on objects.
- Partial flow sensitivity: only some variables or fields are tracked flow-sensitively.
- Shape abstraction: track summaries for lists/trees (outside this chapter's scope); integrate via summary sites.

#chapter-summary[
  A pragmatic points-to and dynamic type analysis models aliases with a may-points-to map, performs strong updates on singletons and weak updates otherwise, and stores abstract values per allocation site.
  Flow- and context-sensitivity improve precision when bounded carefully.
  Reduced products with numeric, string, and BDD control domains provide path-sensitive, field-aware reasoning while maintaining soundness and termination.
]
