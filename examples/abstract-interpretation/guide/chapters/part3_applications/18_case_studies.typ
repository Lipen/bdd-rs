#import "../../theme.typ": *

= Case Studies <ch-case-studies>

#reading-path(path: "essential")

Theory is best understood through practice.
In this chapter, we dissect two complete, real-world inspired examples from the `bdd-rs` repository.

== Traffic Light Controller

The `traffic_light.rs` example demonstrates how to verify a state machine with timing constraints.

=== The System
A standard traffic light sequence: Green -> Yellow -> Red -> Green.
Safety property: "Never Green and Red at the same time" (trivial), but also "Yellow must follow Green".

=== The Analysis
We use the `BddControlDomain` to represent the discrete states (colors) and a numeric domain for the timer.

== Mode Controller

The `mode_controller.rs` example represents a more complex embedded system with:
- Multiple subsystems (Heater, Cooler, Fan).
- Interdependencies (Fan must be on if Heater is on).
- User inputs (Target temperature).

=== Key Insight
BDDs excel here because the state space is the *product* of the subsystems.
A path-insensitive analysis would merge states like `(Heat=On, Fan=On)` and `(Heat=Off, Fan=Off)` into `(Heat={On,Off}, Fan={On,Off})`, falsely allowing `(Heat=On, Fan=Off)`.
Our BDD-guided analysis keeps these correlations precise.
