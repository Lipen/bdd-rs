#import "../../theme.typ": *

= Configuration and Feature Models <ch-configuration>

Modern software rarely ships as a single product.
A car configurator might offer 50 optional features, from heated seats to autonomous parking.
With $2^(50)$ combinations --- more than a quadrillion --- how do you ensure every valid configuration actually builds, boots, and behaves correctly?

BDDs are the hidden engine behind *software product line analysis*, compactly representing astronomical configuration spaces and enabling instant queries about variability.

== Software Product Lines

A *software product line* (SPL) is a family of related products sharing a common architecture but varying in *features*.

#figure(
  cetz.canvas(length: 1cm, {
    import cetz.draw: *

    content((6, 7.5), text(weight: "bold", size: 1em)[Product Line Variability])

    // Core platform
    rect(
      (3.5, 5),
      (8.5, 6.5),
      fill: colors.box-definition.lighten(40%),
      stroke: 2pt + colors.primary.lighten(20%),
      radius: 4pt,
    )
    content((6, 6), text(size: 0.9em, weight: "semibold")[Core Platform])
    content((6, 5.4), text(size: 0.8em)[Shared code & architecture])

    // Features
    rect(
      (0.5, 2.5),
      (3, 4),
      fill: colors.box-example.lighten(40%),
      stroke: 1pt + colors.success.lighten(20%),
      radius: 4pt,
    )
    content((1.75, 3.5), text(size: 0.8em)[Feature A])
    content((1.75, 2.9), text(size: 0.7em, fill: colors.text-muted)[Optional])

    rect((4, 2.5), (6.5, 4), fill: colors.box-insight.lighten(30%), stroke: 1pt + colors.info, radius: 4pt)
    content((5.25, 3.5), text(size: 0.8em)[Feature B])
    content((5.25, 2.9), text(size: 0.7em, fill: colors.text-muted)[Required])

    rect(
      (7.5, 2.5),
      (10, 4),
      fill: colors.box-warning.lighten(40%),
      stroke: 1pt + colors.warning.lighten(20%),
      radius: 4pt,
    )
    content((8.75, 3.5), text(size: 0.8em)[Feature C])
    content((8.75, 2.9), text(size: 0.7em, fill: colors.text-muted)[Optional])

    // Connections
    line((4.5, 4.9), (1.75, 4.1), stroke: 1pt + colors.line)
    line((6, 4.9), (5.25, 4.1), stroke: 1.5pt + colors.primary)
    line((7.5, 4.9), (8.75, 4.1), stroke: 1pt + colors.line)

    // Products
    content((2, 1.2), text(size: 0.8em)[Product 1: A+B])
    content((5.5, 1.2), text(size: 0.8em)[Product 2: B+C])
    content((9, 1.2), text(size: 0.8em)[Product 3: A+B+C])
  }),
  caption: [A product line derives multiple products from shared assets plus optional features.],
)

#insight-box[
  With $n$ optional features, there are potentially $2^n$ configurations.
  Not all are valid --- dependencies and conflicts constrain the space.
  BDDs compactly represent *exactly* the valid configurations.
]

== Feature Models

A *feature model* captures variability as a tree with constraints:

#example-box(title: "Feature Model Elements")[
  + *Mandatory*: Child must be selected if parent is ($A -> B$)
  + *Optional*: Child may be selected if parent is ($A -> (B or not B)$)
  + *Alternative (XOR)*: Exactly one child ($A -> (B xor C)$)
  + *Or-group*: At least one child ($A -> (B or C)$)
  + *Cross-tree constraints*: $B -> C$ (selecting B requires C)
]

#figure(
  cetz.canvas(length: 1cm, {
    import cetz.draw: *

    content((6, 8.5), text(weight: "bold", size: 1em)[Feature Model: Mobile Phone])

    // Root
    circle((6, 7), radius: 0.5, fill: colors.box-definition.lighten(30%), stroke: 1.5pt + colors.primary, name: "phone")
    content((6, 7), text(size: 0.8em)[Phone])

    // Level 1
    circle((2.5, 5), radius: 0.45, fill: colors.box-insight.lighten(30%), stroke: 1.5pt + colors.info, name: "calls")
    content((2.5, 5), text(size: 0.7em)[Calls])
    content((2.5, 4.3), text(size: 0.7em, fill: colors.info)[●])

    circle(
      (5, 5),
      radius: 0.45,
      fill: colors.box-example.lighten(40%),
      stroke: 1pt + colors.success.lighten(20%),
      name: "gps",
    )
    content((5, 5), text(size: 0.7em)[GPS])
    content((5, 4.3), text(size: 0.7em, fill: colors.text-muted)[○])

    circle(
      (7, 5),
      radius: 0.45,
      fill: colors.box-example.lighten(40%),
      stroke: 1pt + colors.success.lighten(20%),
      name: "media",
    )
    content((7, 5), text(size: 0.7em)[Media])
    content((7, 4.3), text(size: 0.7em, fill: colors.text-muted)[○])

    circle(
      (9.5, 5),
      radius: 0.45,
      fill: colors.box-warning.lighten(40%),
      stroke: 1pt + colors.warning.lighten(20%),
      name: "screen",
    )
    content((9.5, 5), text(size: 0.7em)[Screen])

    // Level 2: Screen alternatives
    circle((8.5, 3), radius: 0.4, fill: colors.bg-code, stroke: 1pt + colors.line, name: "basic")
    content((8.5, 3), text(size: 0.7em)[Basic])

    circle((10.5, 3), radius: 0.4, fill: colors.bg-code, stroke: 1pt + colors.line, name: "color")
    content((10.5, 3), text(size: 0.7em)[Color])

    // Edges
    line((6, 6.4), (2.5, 5.55), stroke: 1.5pt + colors.line)
    line((6, 6.4), (5, 5.55), stroke: 1pt + colors.line)
    line((6, 6.4), (7, 5.55), stroke: 1pt + colors.line)
    line((6, 6.4), (9.5, 5.55), stroke: 1.5pt + colors.line)

    // XOR arc for screen
    arc((9.5, 4.2), start: 210deg, stop: 330deg, radius: 0.5, stroke: 1pt + colors.warning, mode: "OPEN")
    line((9.5, 4.4), (8.5, 3.5), stroke: 1pt + colors.line)
    line((9.5, 4.4), (10.5, 3.5), stroke: 1pt + colors.line)

    // Legend
    content((1, 2.5), align(left)[
      #set text(size: 0.7em)
      #text(fill: colors.info)[●] Mandatory\
      #text(fill: colors.text-muted)[○] Optional\
      #box(width: 0.5em, height: 0.3em, stroke: 0.5pt + colors.warning) XOR group
    ])

    // Cross-tree constraint
    content((5.5, 2), text(size: 0.7em, fill: colors.primary)[GPS → Color], name: "xtc")
    line((5.3, 3), (5, 2.3), stroke: 1pt + colors.primary.lighten(30%), mark: (start: ">"))
    line((9.8, 3), (6.2, 2.3), stroke: 1pt + colors.primary.lighten(30%), mark: (start: ">"))
  }),
  caption: [Feature model for a mobile phone with mandatory, optional, and alternative features.],
)

=== BDD Encoding

```rust
fn encode_feature_model(bdd: &Bdd) -> Ref {
    // Feature variables
    let phone = bdd.variable(1);
    let calls = bdd.variable(2);
    let gps = bdd.variable(3);
    let media = bdd.variable(4);
    let screen = bdd.variable(5);
    let basic = bdd.variable(6);
    let color = bdd.variable(7);

    // Mandatory: Phone → Calls
    let c1 = bdd.implies(phone, calls);

    // Mandatory: Phone → Screen
    let c2 = bdd.implies(phone, screen);

    // XOR: Screen → (Basic ⊕ Color)
    let xor_screen = bdd.xor(basic, color);
    let c3 = bdd.implies(screen, xor_screen);

    // Cross-tree: GPS → Color
    let c4 = bdd.implies(gps, color);

    // Root must be selected
    let c5 = phone;

    // Conjoin all constraints
    bdd.and_many(&[c1, c2, c3, c4, c5])
}
```

== Configuration Analysis Queries

BDDs answer configuration questions efficiently:

#comparison-table(
  [*Query*],
  [*BDD Operation*],
  [*Complexity*],
  [Is config valid?],
  [Evaluate BDD path],
  [$O(n)$],
  [Any valid config?],
  [BDD ≠ 0?],
  [$O(1)$],
  [Count valid configs],
  [SatCount],
  [$O(|f|)$],
  [List all configs],
  [AllSat enumeration],
  [$O("output")$],
  [Feature always selected?],
  [$f and not x = 0$?],
  [$O(|f|)$],
  [Features compatible?],
  [$f and x and y != 0$?],
  [$O(|f|)$],
)

#example-box(title: "Common Analysis Queries")[
  ```rust
  // Is this configuration valid?
  let config = phone & calls & gps & color & !basic;
  let valid = !bdd.is_zero(bdd.and(feature_model, config));

  // How many valid configurations?
  let count = bdd.sat_count(feature_model, num_features);

  // Is GPS always selected in valid configs?
  let without_gps = bdd.and(feature_model, bdd.not(gps));
  let gps_mandatory = bdd.is_zero(without_gps);

  // Are GPS and Media compatible?
  let both = bdd.and(feature_model, bdd.and(gps, media));
  let compatible = !bdd.is_zero(both);
  ```
]

== Interactive Configuration

When users configure products interactively, BDDs enable smart assistance:

#figure(
  cetz.canvas(length: 1cm, {
    import cetz.draw: *

    content((6, 7.5), text(weight: "bold", size: 1em)[Interactive Configuration Flow])

    // User selects
    rect(
      (0.5, 5),
      (3.5, 6.5),
      fill: colors.box-definition.lighten(40%),
      stroke: 1pt + colors.primary.lighten(20%),
      radius: 4pt,
    )
    content((2, 6.1), text(size: 0.8em, weight: "semibold")[User selects])
    content((2, 5.5), text(size: 0.7em)[Feature GPS])

    // BDD update
    rect((4.5, 5), (7.5, 6.5), fill: colors.box-insight.lighten(30%), stroke: 1pt + colors.info, radius: 4pt)
    content((6, 6.1), text(size: 0.8em, weight: "semibold")[BDD Update])
    content((6, 5.5), text(size: 0.7em)[$f <- f and "GPS"$])

    // System response
    rect(
      (8.5, 4.5),
      (11.5, 7),
      fill: colors.box-example.lighten(40%),
      stroke: 1pt + colors.success.lighten(20%),
      radius: 4pt,
    )
    content((10, 6.5), text(size: 0.8em, weight: "semibold")[System responds])
    content((10, 5.8), text(size: 0.7em)[✓ Color now required])
    content((10, 5.3), text(size: 0.7em)[✗ Basic disabled])
    content((10, 4.8), text(size: 0.7em)[○ Media still optional])

    // Arrows
    line((3.6, 5.75), (4.4, 5.75), stroke: 1pt + colors.line, mark: (end: ">"))
    line((7.6, 5.75), (8.4, 5.75), stroke: 1pt + colors.line, mark: (end: ">"))

    // Loop back
    bezier((10, 4.4), (2, 4.4), (6, 3.2), stroke: 1pt + colors.text-muted, mark: (end: ">"))
    content((6, 3), text(size: 0.7em, fill: colors.text-muted)[Continue selecting...])
  }),
  caption: [Interactive configuration with BDD-backed constraint propagation.],
)

#algorithm(title: "Propagate Selection")[
  ```
  PropagateSelection(bdd, current_config, selected_feature):
    // Add selection to configuration
    new_config = current_config AND selected_feature

    // Check validity
    if new_config == 0:
      return Error("Selection violates constraints")

    // Find implied selections (dead features = features that must be false)
    for each unselected feature f:
      if (new_config AND f) == 0:
        f.status = DISABLED  // Can't be selected
      else if (new_config AND NOT f) == 0:
        f.status = REQUIRED  // Must be selected
      else:
        f.status = OPTIONAL  // User can choose

    return new_config
  ```
]

#insight-box[
  For large feature models (thousands of features), caching partial BDDs and using incremental operations keeps interactive response times under 100ms.
]

== Optimization over Configurations

Often we want not just *any* valid configuration, but the *best* one.

#example-box(title: "Configuration Optimization")[
  Each feature has attributes:
  - *Cost*: $"cost"("GPS") = 50$, $"cost"("Color") = 30$
  - *Performance*: $"perf"("Color") = 0.8$

  Goals:
  - Minimize cost while meeting requirements
  - Find Pareto-optimal configurations (cost vs. features)
]

#figure(
  cetz.canvas(length: 1cm, {
    import cetz.draw: *

    content((6, 7), text(weight: "bold", size: 1em)[Configuration Search Space])

    // Axes
    line((1, 1), (1, 6), stroke: 1pt + colors.line, mark: (end: ">"))
    line((1, 1), (10, 1), stroke: 1pt + colors.line, mark: (end: ">"))
    content((0.5, 6), text(size: 0.8em)[Cost])
    content((10, 0.5), text(size: 0.8em)[Features])

    // Invalid region
    rect((7, 1), (10, 6), fill: colors.box-warning.lighten(70%), stroke: none)
    content((8.5, 5), text(size: 0.7em, fill: colors.warning)[Invalid])

    // Valid configurations (points)
    circle((2, 2), radius: 0.15, fill: colors.bg-code, stroke: 1pt + colors.line)
    circle((3, 2.5), radius: 0.15, fill: colors.bg-code, stroke: 1pt + colors.line)
    circle((4, 3.5), radius: 0.15, fill: colors.bg-code, stroke: 1pt + colors.line)
    circle((5, 4), radius: 0.15, fill: colors.bg-code, stroke: 1pt + colors.line)
    circle((3.5, 4.5), radius: 0.15, fill: colors.bg-code, stroke: 1pt + colors.line)

    // Pareto front
    circle((2, 2), radius: 0.2, fill: colors.success, stroke: 1.5pt + colors.success.darken(20%))
    circle((3, 2.5), radius: 0.2, fill: colors.success, stroke: 1.5pt + colors.success.darken(20%))
    circle((4, 3.5), radius: 0.2, fill: colors.success, stroke: 1.5pt + colors.success.darken(20%))
    circle((5, 4), radius: 0.2, fill: colors.success, stroke: 1.5pt + colors.success.darken(20%))

    line((2, 2), (3, 2.5), stroke: 1.5pt + colors.success)
    line((3, 2.5), (4, 3.5), stroke: 1.5pt + colors.success)
    line((4, 3.5), (5, 4), stroke: 1.5pt + colors.success)

    content((5, 5.5), text(size: 0.7em, fill: colors.success)[Pareto front])
  }),
  caption: [Pareto-optimal configurations balance cost against features.],
)

== Industrial Applications

=== Linux Kernel Configuration

The Linux kernel has over 15,000 configuration options with complex dependencies.

#info-box(title: "Linux Kernel Kconfig")[
  - *Options*: ~15,000+ Boolean and choice features
  - *Constraints*: Thousands of dependencies and conflicts
  - *BDD use*: Configuration tools like `make menuconfig` use constraint solvers
  - *Challenge*: Full BDD can be huge; partitioned/approximate methods used
]

=== Automotive Configuration

Modern cars have thousands of electronic control units (ECUs) with variant configurations:

#comparison-table(
  [*Domain*],
  [*Features*],
  [*BDD Benefit*],
  [Automotive ECUs],
  [Engine, safety, comfort options],
  [Validate combinations pre-production],
  [Cloud services],
  [VM sizes, regions, features],
  [Pricing, compatibility checks],
  [Product configurators],
  [E-commerce customization],
  [Real-time validity feedback],
  [Build systems],
  [Compiler flags, dependencies],
  [Detect incompatible flag combinations],
)

#warning-box(title: "Scalability Limits")[
  Very large feature models (10,000+ features) can cause BDD blowup.
  Industrial tools use:
  - *Partitioning*: Split model into independent sub-models
  - *Approximation*: Over-approximate the valid space
  - *Hybrid*: BDD + SAT solver combination
]

== The Power of Feature Model BDDs

Once you have a BDD for a feature model:

#insight-box[
  - *Validation*: Instantly check any configuration
  - *Counting*: Know exactly how many products are possible
  - *Sampling*: Generate random valid configurations for testing
  - *Analysis*: Find dead features, redundant constraints
  - *Optimization*: Search only valid configurations

  The BDD is a *complete, compact encoding* of your product space.
]
