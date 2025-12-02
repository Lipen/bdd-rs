# Symbolic Model Checking with BDDs

A BDD-based symbolic model checking framework implementing classic algorithms from "Symbolic Model Checking: 10^20 States and Beyond" (Burch et al., 1990).

## Overview

This library verifies finite-state systems using Binary Decision Diagrams, handling systems with millions to billions of states by representing state sets symbolically rather than explicitly enumerating them.

## Features

### Core Capabilities

- **Transition Systems**: Symbolic Kripke structures with present/next-state variables
- **CTL Model Checking**: Full Computation Tree Logic (EX, AX, EF, AF, EG, AG, EU, AU)
- **LTL Model Checking**: Linear Temporal Logic via Büchi automata
- **Fairness Constraints**: Strong and weak fairness for realistic liveness properties
- **Counterexample Generation**: Linear traces (safety) and lasso traces (liveness)

### Symbolic Operations

- `image(S, T)`: Forward reachability — ∃s. S(s) ∧ T(s, s')
- `preimage(S, T)`: Backward reachability — ∃s'. T(s, s') ∧ S(s')
- Existential quantification and variable renaming

## Project Structure

```text
examples/model-checking/
├── Cargo.toml
├── README.md
├── guide/
│   └── main.typ            # Typst documentation
├── src/
│   ├── lib.rs              # Public API
│   ├── transition.rs       # Transition systems
│   ├── ctl.rs              # CTL model checking
│   ├── ltl.rs              # LTL model checking
│   ├── fairness.rs         # Fairness constraints
│   └── counterexample.rs   # Counterexample generation
└── examples/
    ├── abp.rs              # Alternating Bit Protocol
    ├── hanoi.rs            # Towers of Hanoi (planning)
    ├── tictactoe.rs        # Game solving (attractors)
    ├── mutex.rs            # Peterson's mutual exclusion
    ├── philosophers.rs     # Dining philosophers
    ├── counter.rs          # N-bit counter (scalability)
    └── traffic_light.rs    # Traffic light controller
```

## Examples

### Alternating Bit Protocol (`abp.rs`)

Demonstrates reliable communication over a lossy channel:

- **Fairness**: Shows why liveness requires fairness constraints
- **Safety vs Liveness**: AF fails without fairness, holds with fairness
- **Key insight**: Adversarial schedulers can always prevent progress

```bash
cargo run --example abp --release
```

### Towers of Hanoi (`hanoi.rs`)

BDD-based symbolic planning for the classic puzzle:

- **State space**: 3^N configurations for N disks
- **Optimal solution**: Symbolic BFS finds 2^N-1 minimum moves
- **Solution extraction**: Displays step-by-step solution with visual diagrams

```bash
cargo run --example hanoi --release
```

### Tic-Tac-Toe (`tictactoe.rs`)

Two-player game solving with attractor computation:

- **Winning regions**: Computes states where each player can force a win
- **Drawing analysis**: Confirms empty board is a draw with perfect play
- **Attractor algorithm**: Backward fixpoint for game-theoretic analysis

```bash
cargo run --example tictactoe --release
```

### Other Examples

- **`mutex.rs`**: Peterson's algorithm for mutual exclusion
- **`philosophers.rs`**: Dining philosophers deadlock analysis
- **`counter.rs`**: N-bit counter demonstrating BDD scalability
- **`traffic_light.rs`**: Simple traffic light controller

## Temporal Logics

### CTL (Computation Tree Logic)

Branching-time logic with path quantifiers (A/E) and temporal operators:

| Formula | Meaning |
|---------|---------|
| `EX φ`  | There exists a next state satisfying φ |
| `AX φ`  | All next states satisfy φ |
| `EF φ`  | There exists a path where φ eventually holds |
| `AF φ`  | On all paths, φ eventually holds |
| `EG φ`  | There exists a path where φ always holds |
| `AG φ`  | On all paths, φ always holds |
| `E[φ U ψ]` | There exists a path where φ holds until ψ |
| `A[φ U ψ]` | On all paths, φ holds until ψ |

### LTL (Linear Temporal Logic)

Linear-time logic for reasoning about individual execution paths:

| Formula | Meaning |
|---------|---------|
| `X φ`   | φ holds in the next state |
| `F φ`   | φ eventually holds (Future) |
| `G φ`   | φ always holds (Globally) |
| `φ U ψ` | φ holds until ψ becomes true |
| `φ R ψ` | ψ holds until (and including when) φ becomes true |

### Fairness Constraints

Fairness assumptions exclude unrealistic infinite behaviors:

- **Strong fairness**: If enabled infinitely often, happens infinitely often
- **Weak fairness**: If continuously enabled, eventually happens

```rust
// Without fairness: AF delivered FAILS (adversarial channel)
// With fairness:    AF delivered HOLDS (realistic behavior)
```

## Algorithms

### Fixpoint Computation

CTL operators are computed via least (μ) and greatest (ν) fixpoints:

```text
EF φ  = μZ. φ ∨ EX Z        [least fixpoint - start from ∅]
EG φ  = νZ. φ ∧ EX Z        [greatest fixpoint - start from all states]
```

### Counterexample Generation

When properties fail, counterexamples explain *why*:

- **Linear traces**: Path from initial state to violation (safety)
- **Lasso traces**: Stem + loop structure (liveness)

  ```text
  Linear:  s₀ → s₁ → s₂ → ... → sₙ (bad)
  Lasso:   [ s₀ → s₁ → ... → sₖ ]  → [ sₖ₊₁ → ... → sₘ → sₖ ]
                                       ↑________________|
  ```

  Here, the loop from sₖ to sₘ demonstrates infinite violation.

## Quick Start

```rust
use model_checking::*;
use bdd_rs::bdd::Bdd;
use std::rc::Rc;

// Create transition system
let bdd = Rc::new(Bdd::default());
let mut ts = TransitionSystem::new(bdd.clone());

// Declare state variable
let x = Var::new("x");
ts.declare_var(x.clone());

// Set initial state and transitions
let x_pres = ts.var_manager().get_present(&x).unwrap();
let initial = ts.bdd().apply_not(ts.bdd().mk_var(x_pres));
ts.set_initial(initial);

let x_trans = ts.assign_var(&x, ts.bdd().apply_not(ts.bdd().mk_var(x_pres)));
ts.set_transition(x_trans);

// Add labels and check properties
ts.add_label("on".to_string(), ts.bdd().mk_var(x_pres));
let ts = Rc::new(ts);

let checker = CtlChecker::new(ts.clone());
let property = CtlFormula::atom("on").ef(); // EF on
assert!(checker.holds_initially(&property));
```

## Testing

```bash
cargo test --lib
```

All tests passing ✓

## References

1. **Symbolic Model Checking: 10^20 States and Beyond** — Burch et al. (1990)
2. **Model Checking** — Clarke, Grumberg, Peled (1999)
3. **Principles of Model Checking** — Baier & Katoen (2008)
4. **NuSMV 2.0 User Manual** — Cimatti et al. (2002)
