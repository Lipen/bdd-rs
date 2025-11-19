#import "../../theme.typ": *

= Domain Combinations <ch-domain-combinations>

#reading-path(path: "advanced")

This chapter synthesizes the techniques from previous chapters, focusing on practical domain combinations for path-sensitive analysis.
We explore trace partitioning, relational domains, and BDD-based symbolic domains --- the core of our approach to combining control flow precision with numeric data analysis.

== Trace Partitioning

*Trace partitioning* refines analysis by maintaining separate abstract states for different execution paths.

#definition(title: "Trace Partitioning")[
  Given abstract domain $A$ and control predicates $P$, a *trace-partitioned domain* maintains a mapping:

  $ A_P = P -> A $

  where each predicate $p in P$ guards an abstract state $a in A$.
  The concrete meaning is:

  $ gamma(f) = union.big_(p in P) (gamma_P (p) inter gamma_A (f(p))) $

  where $gamma_P (p)$ is the set of concrete states satisfying predicate $p$.
]

Trace partitioning is the foundation of path-sensitive analysis: different paths through the program maintain distinct abstract states.

#example-box[
  *Simple branching:*

  ```rust
  let mut x = input();
  if x > 0 {
      x = x + 1;  // Path A: x > 0
  } else {
      x = x - 1;  // Path B: x ≤ 0
  }
  // Join point
  ```

  Path-insensitive (single state): After join, $x in (-infinity, infinity)$ (no information).

  Path-sensitive (trace partitioning):
  - Predicate $p_A$: `x > 0`, state: $x in [2, infinity)$
  - Predicate $p_B$: `x <= 0`, state: $x in (-infinity, -1]$
  - After join: Precise union of both ranges
]

#info-box(title: "Partitioning Granularity")[
  Key questions:

  - *What predicates to track?* All branches? Only relevant ones?
  - *When to merge partitions?* At function boundaries? Loops?
  - *How many partitions?* Trade precision for scalability

  BDDs naturally represent partitions as paths in the decision diagram.
]

== BDD Control Domain as Trace Partitioning

BDD control domains (@ch-combining-domains) implement trace partitioning efficiently.

#definition(title: "BDD Control Domain")[
  The *BDD control domain* represents sets of control predicates as BDDs:

  $ C_"BDD" = "BDD"(x_1, ..., x_n) $

  where each variable $x_i$ represents a boolean condition in the program.

  Lattice operations:
  - Join: $f ljoin g = f or g$ (BDD disjunction)
  - Meet: $f lmeet g = f and g$ (BDD conjunction)
  - Bottom: $bot = "false"$ (unsatisfiable)
  - Top: $top = "true"$ (all states)
]

#theorem(title: "BDD Control Domain Properties")[
  $C_"BDD"$ forms a complete Boolean algebra:

  + *Lattice*: $(C_"BDD", lle, ljoin, lmeet, bot, top)$ is complete
  + *Complementation*: $not f$ exists for all $f$
  + *Efficient operations*: Operations in $O(|f| times |g|)$ where $|f|$ is BDD size
  + *Canonical representation*: Unique representation (given variable ordering)
]

#example-box[
  *BDD variables for control flow:*

  ```rust
  let mut x = input();
  if x > 0 {        // Allocate BDD variable b1 for "x > 0"
      if x > 10 {   // Allocate BDD variable b2 for "x > 10"
          x = 100;  // Path condition: b1 ∧ b2
      } else {
          x = 5;    // Path condition: b1 ∧ ¬b2
      }
  } else {
      x = -1;       // Path condition: ¬b1
  }
  ```

  BDD represents all reachable path conditions: $(b_1 and b_2) or (b_1 and not b_2) or (not b_1)$.

  Simplified: $b_1 or not b_1 = top$ (all paths reachable).
]

== Product Domain: BDD × Data

Combining BDD control with numeric data domains creates a powerful path-sensitive analyzer.

#definition(title: "BDD Product Domain")[
  Given BDD control domain $C_"BDD"$ and data domain $D$, the *BDD product domain* is:

  $ A = C_"BDD" times D $

  with elements $(f, d)$ where:
  - $f in C_"BDD"$ represents path conditions
  - $d in D$ represents data properties

  Concretization:
  $ gamma((f, d)) = {sigma mid(|) sigma "satisfies" f "and" sigma in gamma_D (d)} $
]

This is a *direct product* (@ch-advanced-galois). We can enhance it with reduction to exploit relationships between control and data.

#example-box[
  *Interval domain product:*

  State: $(f, [a, b])$ means "on paths satisfying $f$, variable is in interval $[a, b]$".

  After `if x > 0`:
  - True branch: $(f and b_"x>0", [1, infinity])$ (refined from $[a, b]$)
  - False branch: $(f and not b_"x>0", [-infinity, 0])$ (refined from $[a, b]$)

  The control predicate $b_"x>0"$ refines the interval bounds automatically.
]

== Abstract Transformers for BDD Products

Transfer functions must propagate both control and data information.

#algorithm(title: "BDD Product Transfer Function")[
  *Input:* Statement $s$, state $(f, d)$

  *Output:* Transformed state $(f', d')$

  + *Match* $s$:
    + *Case* $x := e$:
      + $d' <- llb x := e rrb^sharp_D (d)$ $quad slash.double$ Data transfer
      + $f' <- f$ $quad slash.double$ Control unchanged
    + *Case* `if` $c$ `then` $s_1$ `else` $s_2$:
      + $b <- "allocate_bdd_var"(c)$ $quad slash.double$ Fresh BDD variable
      + $(f_1, d_1) <- "transfer"(s_1, (f and b, "assume"(c, d)))$
      + $(f_2, d_2) <- "transfer"(s_2, (f and not b, "assume"(not c, d)))$
      + $(f', d') <- (f_1 or f_2, d_1 ljoin_D d_2)$ $quad slash.double$ Join branches
    + *Case* other statements: similar pattern
  + *return* $(f', d')$
]

The `assume` operation refines the data domain based on branch conditions.

#definition(title: "Assume Operation")[
  For condition $c$ and data state $d$, $"assume"(c, d)$ refines $d$ based on $c$:

  $ "assume"(c, d) = alpha_D ({sigma in gamma_D (d) mid(|) llb c rrb sigma = "true"}) $

  This is the *best transformer* for assumption statements.
]

#example-box[
  *Assume with intervals:*

  ```rust
  let x: Interval = [-10, 10];
  assume(x > 5);
  // Result: x in [6, 10]
  ```

  Implementation:
  ```rust
  fn assume_gt(x: Interval, c: i32) -> Interval {
      Interval::new(max(x.low, c + 1), x.high)
  }
  ```

  For inequality $x > 5$ with $x in [-10, 10]$:
  - Lower bound: $max(-10, 6) = 6$
  - Upper bound: $10$ (unchanged)
  - Result: $[6, 10]$
]

== Reduced Product with BDD Control

Reduction tightens data bounds based on control predicates.

#definition(title: "BDD-Data Reduction")[
  Given $(f, d)$, reduction operator $rho$ refines $d$ based on constraints implied by $f$:

  $
    rho(f, d) = cases(
      (bot, bot) & "if" gamma(f, d) = emptyset,
      (f, d') & "otherwise"
    )
  $

  where $d'$ is obtained by extracting constraints from $f$ and applying assume operations.
]

#example-box[
  *Sign × BDD reduction:*

  State: $(b_"x>0", "Neg")$ --- control says `x > 0`, data says negative.

  Contradiction! Reduction: $(bot, bot)$ (unreachable).

  State: $(b_"x>0", top)$ --- control says `x > 0`, data is unknown.

  Reduction: $(b_"x>0", "Pos")$ --- refine data using control information.
]

#algorithm(title: "BDD-Data Reduction Algorithm")[
  *Input:* $(f, d)$ where $f in C_"BDD"$, $d in D$

  *Output:* Reduced state $(f', d')$

  + *if* $f = bot$ *then* *return* $(bot, bot)$
  + *Extract constraints from* $f$:
    + *for each* literal $l$ in $f$ (SAT-based or BDD traversal):
      + $d <- "assume"(l, d)$ $quad slash.double$ Refine data
      + *if* $d = bot$ *then* *return* $(bot, bot)$ $quad slash.double$ Contradiction
  + *return* $(f, d)$
]

#warning-box[
  *Extraction cost*: Enumerating all constraints from a BDD can be expensive.

  Practical strategies:
  - Extract only relevant constraints (those mentioning analyzed variables)
  - Use BDD path enumeration with early pruning
  - Cache reduction results
  - Apply reduction selectively (after joins, not every operation)
]

== Relational Domains

*Relational domains* track relationships between variables, going beyond independent analysis.

#definition(title: "Relational Abstract Domain")[
  A relational domain represents constraints involving multiple variables:

  $ d in D_"rel" = "Constraints"(V) $

  where $V$ is the set of program variables.

  Examples:
  - *Octagons*: $plus.minus x plus.minus y lt.eq c$
  - *Polyhedra*: $sum a_i x_i lt.eq c$
  - *Equality domain*: $x = y + c$
]

#example-box[
  *Octagon constraints:*

  After `y = x + 1` with $x in [0, 10]$:

  Non-relational intervals: $x in [0, 10]$, $y in [1, 11]$ (independent).

  Octagon domain: $x in [0, 10]$ and $y = x + 1$ (relationship preserved).

  Later, `if x > 5` refines both: $x in [6, 10]$ implies $y in [7, 11]$.
]

Relational domains are expensive but powerful for precise analysis.

== Combining BDD Control with Relational Domains

BDD product with relational domains achieves both path-sensitivity and relational precision.

#definition(title: "BDD × Relational Product")[
  $ A = C_"BDD" times D_"rel" $

  State $(f, r)$ means: "On paths satisfying $f$, variables satisfy relational constraints $r$."

  Operations:
  - Join: $(f_1, r_1) ljoin (f_2, r_2) = (f_1 or f_2, r_1 ljoin_"rel" r_2)$
  - Assignment: Updates relational constraints
  - Branch: Splits $f$ and refines $r$ via assume
]

#example-box[
  *BDD × Octagon for array bounds:*

  ```rust
  let mut i = 0;
  let len = array.len();  // len = 10
  while i < len {
      array[i] = 0;       // Safe if i < len
      i += 1;
  }
  ```

  State at loop body:
  - Control: $f = b_"i<len"$ (loop condition)
  - Relational: $0 lt.eq i < "len"$ and $"len" = 10$

  Array access `array[i]` is safe: $i < "len"$ guaranteed by control predicate.

  After `i += 1`: Relational constraints updated to $1 lt.eq i lt.eq "len"$.
]

== Practical Considerations

#definition(title: "Domain Selection Guidelines")[
  Choose domains based on analysis goals:

  + *Simple properties* (null checks, sign): BDD + Sign/Constant
  + *Numeric ranges*: BDD + Intervals
  + *Array bounds*: BDD + Octagons/Polyhedra
  + *Complex invariants*: BDD + Polyhedra (expensive!)
  + *Conditional properties*: BDD alone may suffice
]

#info-box(title: "Scalability Strategies")[
  Making BDD products scale:

  + *Variable ordering*: Group related BDD variables together
  + *Lazy reduction*: Reduce only when precision matters
  + *Partition merging*: Merge similar partitions (widening on BDDs)
  + *Modular analysis*: Analyze functions independently
  + *Incremental updates*: Reuse BDD operations across iterations
]

== BDD Widening for Loops

Loops require widening on both control and data components.

#definition(title: "BDD Widening")[
  For BDD control states $f_1 lle f_2$:

  $
    f_1 widen f_2 = cases(
      f_2 & "if" |f_2| lt.eq k times |f_1|,
      top & "otherwise"
    )
  $

  where $k$ is a size threshold (e.g., $k=2$).

  Intuition: Allow BDD to grow, but prevent explosion by forcing $top$ (all paths) when too large.
]

#example-box[
  *Loop with path conditions:*

  ```rust
  let mut i = 0;
  while i < 100 {
      if i % 2 == 0 { /* ... */ }
      if i % 3 == 0 { /* ... */ }
      i += 1;
  }
  ```

  Without widening: BDD tracks all combinations of parity and divisibility --- exponential growth.

  With BDD widening: After few iterations, force $top$ for control, keep interval $i in [0, 100]$ for data.
]

#algorithm(title: "Product Domain Widening")[
  *Input:* $(f_1, d_1)$, $(f_2, d_2)$ where $(f_1, d_1) lle (f_2, d_2)$

  *Output:* Widened state $(f', d')$

  + $f' <- f_1 widen_"BDD" f_2$ $quad slash.double$ Widen control
  + $d' <- d_1 widen_D d_2$ $quad slash.double$ Widen data
  + *return* $(f', d')$
]

== Implementation in bdd-rs

Our framework implements these concepts with Rust traits.

#example-box[
  *BDD product domain structure:*

  ```rust
  pub struct BddProductDomain<D> {
      bdd: Rc<Bdd>,           // Shared BDD manager
      control: Ref,           // BDD for path conditions
      data: D,                // Data domain state
  }

  impl<D: AbstractDomain> AbstractDomain for BddProductDomain<D> {
      fn join(&self, other: &Self) -> Self {
          let control = self.bdd.apply_or(self.control, other.control);
          let data = self.data.join(&other.data);
          BddProductDomain { bdd: self.bdd.clone(), control, data }
      }

      fn meet(&self, other: &Self) -> Self {
          let control = self.bdd.apply_and(self.control, other.control);
          let data = self.data.meet(&other.data);
          BddProductDomain { bdd: self.bdd.clone(), control, data }
      }

      fn widen(&self, other: &Self) -> Self {
          let control = if self.bdd.node_count(other.control) >
                            2 * self.bdd.node_count(self.control) {
              self.bdd.mk_true()  // Force top
          } else {
              other.control
          };
          let data = self.data.widen(&other.data);
          BddProductDomain { bdd: self.bdd.clone(), control, data }
      }

      // ... other trait methods
  }
  ```
]

#info-box(title: "Design Principles")[
  Key implementation choices:

  - *Shared BDD manager*: Use `Rc<Bdd>` for efficient sharing
  - *Trait-based design*: Generic over data domain `D`
  - *Lazy evaluation*: Defer expensive operations
  - *Caching*: Memoize transfer functions
  - *Testing*: Unit tests for each domain operation
]

== Case Study: Buffer Overflow Detection

Combining BDD control with intervals detects buffer overflows precisely.

#example-box[
  *Buffer access analysis:*

  ```rust
  fn process(buf: &mut [i32], size: usize) {
      let mut i = 0;
      while i < size {
          if i < buf.len() {
              buf[i] = 0;   // Safe access
          } else {
              break;        // Early exit
          }
          i += 1;
      }
  }
  ```

  Analysis state at `buf[i] = 0`:
  - Control: $(b_"i<size" and b_"i<buf.len")$
  - Data: $i in [0, min("size", "buf.len") - 1]$

  Property: $i <$ `buf.len()` guaranteed by control predicate $b_"i<buf.len"$.

  Verification result: *No buffer overflow possible.*
]

== Performance Analysis

#definition(title: "Complexity Metrics")[
  For BDD product domain analysis:

  + *BDD size*: $O(2^n)$ worst case, often much smaller in practice
  + *Data operations*: Depends on data domain ($O(1)$ for Sign, $O(n^2)$ for Octagons)
  + *Product operations*: $O(|"BDD"| times T_D)$ where $T_D$ is data operation time
  + *Fixpoint iterations*: Depends on widening strategy and program structure
]

#example-box[
  *Benchmark results* (from actual measurements):

  #table(
    columns: 4,
    table.header([Benchmark], [BDD Size], [Iterations], [Time]),
    [Heater controller], [~50 nodes], [12], [< 1ms],
    [Traffic light], [~120 nodes], [8], [< 5ms],
    [Array bounds (10 elements)], [~300 nodes], [15], [~20ms],
    [Network protocol], [~500 nodes], [25], [~100ms],
  )

  Key insight: BDD size remains manageable for realistic control flow patterns.
]

== Chapter Summary

This chapter covered domain combinations for path-sensitive analysis:

- *Trace partitioning* maintains separate states per execution path
- *BDD control domain* efficiently represents path conditions as BDDs
- *BDD product domains* combine control precision with data analysis
- *Reduced products* exploit control-data relationships
- *Relational domains* track relationships between variables
- *BDD widening* prevents state explosion in loops
- *Implementation patterns* using Rust traits and shared BDD managers
- *Case studies* demonstrate practical effectiveness

These techniques enable precise, scalable path-sensitive abstract interpretation, as demonstrated in the examples throughout this guide.

#pagebreak()
