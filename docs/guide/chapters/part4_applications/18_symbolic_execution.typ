#import "../../theme.typ": *

= Symbolic Execution and Program Analysis <ch-symbolic-execution>

// PLAN: BDDs in static analysis and testing.
// Target length: 10-12 pages

== Path Conditions as BDDs

// Content to cover:
// - Symbolic execution explores program paths
// - Path condition: conjunction of branch decisions
// - BDD representation avoids path explosion
// - Merging paths with same condition

== Control Flow Encoding

// Content to cover:
// - Program points as Boolean variables
// - Branch conditions as BDD constraints
// - Reachability as BDD satisfiability
// - Infeasible path detection

== Abstract Interpretation with BDDs

// Content to cover:
// - BDDs as abstract domain
// - Path-sensitive analysis
// - Combining value domains with path conditions
// - Precision vs. scalability trade-off

#insight-box[
  BDDs enable *path-sensitive* analysis without *path enumeration*.
  Instead of analyzing each path separately, we analyze sets of paths symbolically.
  A BDD can represent exponentially many paths in polynomial space.
]

== Test Case Generation

// Content to cover:
// - Path coverage goals
// - Generating inputs from BDD paths
// - Constraint solving via BDD operations
// - Incremental test suite construction

== Concolic Testing

// Content to cover:
// - Concrete + symbolic execution
// - BDDs for path condition management
// - Negating path conditions for new paths
// - Integration with SMT solvers

== Security Analysis

// Content to cover:
// - Taint tracking with BDDs
// - Information flow as reachability
// - Vulnerability detection
// - Policy verification
