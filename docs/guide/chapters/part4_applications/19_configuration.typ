#import "../../theme.typ": *

= Configuration and Feature Models <ch-configuration>

// PLAN: BDDs for product line engineering.
// Target length: 8-10 pages

== Software Product Lines

// Content to cover:
// - Variability in software systems
// - Features and their dependencies
// - Configuration spaces
// - Valid configurations as Boolean constraints

== Feature Models

// Content to cover:
// - Hierarchical feature relationships
// - Mandatory, optional, alternative groups
// - Cross-tree constraints
// - BDD encoding of feature model

#example-box(title: "Feature Model Constraints")[
  A simple feature model might have:
  - Root feature $A$ with children $B$, $C$
  - $B$ is mandatory: $A -> B$
  - $C$ is optional: (no constraint)
  - $B$ and $C$ are mutually exclusive: $not(B and C)$

  The BDD of valid configurations: $A and B and not C$
]

== Configuration Analysis Queries

// Content to cover:
// - Is configuration X valid? (BDD evaluation)
// - How many valid configurations? (counting)
// - Find a valid configuration (SAT witness)
// - What features are always selected? (tautology checking)

== Interactive Configuration

// Content to cover:
// - User selects features incrementally
// - System shows remaining valid choices
// - Conflict detection and explanation
// - Auto-completion of partial configurations

== Optimization over Configurations

// Content to cover:
// - Attributes on features (cost, performance)
// - Finding optimal valid configuration
// - Pareto-optimal configurations
// - BDDs + optimization algorithms

== Industrial Applications

// Content to cover:
// - Automotive configuration (ECU variants)
// - Linux kernel configuration
// - Cloud service configuration
// - Success stories and limitations
