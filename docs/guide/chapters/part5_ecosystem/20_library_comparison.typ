#import "../../theme.typ": *

= Library Comparison <ch-library-comparison>

// PLAN: Survey of existing BDD libraries.
// Target length: 10-12 pages

== Landscape of BDD Libraries

// Content to cover:
// - Historical libraries: CUDD, BuDDy, CAL
// - Modern libraries: Sylvan, LibBDD, bdd-rs
// - Language ecosystems: C/C++, Java, Python, Rust
// - Choosing the right library

== CUDD (Colorado University Decision Diagram)

// Content to cover:
// - The reference implementation
// - Features: BDDs, ADDs, ZDDs
// - Dynamic reordering (sifting)
// - Memory management approach
// - Pros and cons

#comparison-table(cols: 5,
  [Feature], [CUDD], [BuDDy], [Sylvan], [bdd-rs],
  [Language], [C], [C++], [C], [Rust],
  [Reordering], [#YES], [#YES], [#YES], [#PARTIAL],
  [Complement Edges], [#YES], [#YES], [#YES], [#YES],
  [Parallel], [#NO], [#NO], [#YES], [#NO],
  [ZDD Support], [#YES], [#NO], [#YES], [#NO],
  [Memory Safety], [#NO], [#NO], [#NO], [#YES],
)

== BuDDy

// Content to cover:
// - C++ library, widely used
// - Simple API
// - Good documentation
// - Reference counting GC

== Sylvan

// Content to cover:
// - Parallel BDD operations
// - Work-stealing parallelism
// - Lock-free data structures
// - When parallelism helps

== JDD and JavaBDD

// Content to cover:
// - Java ecosystem options
// - JNI wrappers vs. pure Java
// - Performance considerations
// - Integration with Java tools

== bdd-rs Design Choices

// Content to cover:
// - Rust's ownership model benefits
// - Memory safety without GC overhead
// - Current feature set
// - Roadmap and future plans

== Benchmark Comparisons

// Content to cover:
// - Standard benchmarks (ISCAS, etc.)
// - Operations: build, apply, quantify
// - Memory usage profiles
// - Caveats about benchmarking
