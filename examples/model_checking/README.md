# Symbolic Model Checking with BDDs

A BDD-based symbolic model checking framework implementing classic algorithms from "Symbolic Model Checking: 10^20 States and Beyond" (Burch et al., 1990).

## Overview

This library verifies finite-state systems using Binary Decision Diagrams, handling systems with millions to billions of states by representing state sets symbolically rather than explicitly enumerating them.

## Features

**Transition Systems**: Symbolic representation of Kripke structures

- State variables with present/next-state pairs
- BDD-based state sets and transition relations
- Image and preimage computation
- Reachability analysis via fixpoint iteration

**CTL Model Checking**: Full Computation Tree Logic support

- Temporal operators: EX, AX, EF, AF, EG, AG, EU, AU
- Fixpoint-based algorithms (least/greatest fixpoints)
- Efficient symbolic state space exploration

**Symbolic Operations**:

- `image(S, T)`: Forward reachability - ∃s. S(s) ∧ T(s, s')
- `preimage(S, T)`: Backward reachability - ∃s'. T(s, s') ∧ S(s')
- Existential quantification and variable renaming

## Project Structure

```text
examples/model_checking/
├── Cargo.toml
├── README.md
└── src/
    ├── lib.rs          # Public API and documentation
    ├── ctl.rs          # CTL model checking algorithms
    └── bin/
        └── modelcheck.rs  # CLI tool
```

## Examples

### Simple Two-State System

```rust
use model_checking::*;
use bdd_rs::bdd::Bdd;

// Create a toggle system: state alternates between 0 and 1
let bdd = Bdd::default();
let mut ts = TransitionSystem::new(bdd);

let x = Var::new("x");
ts.declare_var(x.clone());

// Initial state: x = false
let x_pres = ts.var_manager().get_present(&x).unwrap();
let initial = ts.bdd().apply_not(ts.bdd().mk_var(x_pres));
ts.set_initial(initial);

// Transition: x' = !x
let x_next = ts.var_manager().get_next(&x).unwrap();
let transition = ts.bdd().apply_xor(
    ts.bdd().mk_var(x_pres),
    ts.bdd().mk_var(x_next)
);
ts.set_transition(transition);

// Check CTL property: AF(x=true) - eventually x becomes true
let checker = CtlChecker::new(&ts);
let property = CtlFormula::atom("one").af();
assert!(checker.holds_initially(&property));
```

### Reachability Analysis

```rust
// Compute all reachable states
let reachable = ts.reachable();
let count = ts.count_states(reachable);
println!("Reachable states: {}", count.unwrap());
```

## CTL (Computation Tree Logic)

CTL combines path quantifiers with temporal operators:

**Path Quantifiers**:

- **A** (All paths): Property holds on all execution paths
- **E** (Exists path): Property holds on at least one execution path

**Temporal Operators**:

- **X** (Next): Property holds in the next state
- **F** (Future): Property eventually becomes true
- **G** (Globally): Property always remains true
- **U** (Until): First property holds until second becomes true

**Supported Formulas**: EX, AX, EF, AF, EG, AG, E[φ U ψ], A[φ U ψ]

### Example Properties

```rust
// Safety: "bad" state is never reached
let safety = CtlFormula::atom("bad").not().ag();

// Liveness: request eventually leads to grant
let liveness = CtlFormula::atom("req")
    .implies(CtlFormula::atom("grant").af());
```

## Algorithms

**Image Computation** (forward reachability):

```text
image(S, T) = ∃s. S(s) ∧ T(s, s')
```

**CTL Model Checking** (fixpoint-based):

```text
EX φ  = preimage(SAT(φ))           [exists next]
AX φ  = ¬EX ¬φ                     [all next]
EF φ  = μZ. φ ∨ EX Z               [exists eventually - least fixpoint]
AF φ  = μZ. φ ∨ AX Z               [all eventually - least fixpoint]
EG φ  = νZ. φ ∧ EX Z               [exists globally - greatest fixpoint]
AG φ  = νZ. φ ∧ AX Z               [all globally - greatest fixpoint]
E[φ U ψ] = μZ. ψ ∨ (φ ∧ EX Z)     [exists until - least fixpoint]
A[φ U ψ] = μZ. ψ ∨ (φ ∧ AX Z)     [all until - least fixpoint]
```

Where μZ denotes least fixpoint (start from ∅) and νZ denotes greatest fixpoint (start from all states).

## Performance

- **State Space**: 10^6 to 10^20+ states depending on structure and variable ordering
- **BDD Size**: Critical dependence on variable ordering
- **Fixpoints**: Typically converge in O(diameter) iterations

## Testing

```bash
cargo test --lib
```

**13 comprehensive tests** covering:

- Variable management and state variable allocation
- Transition system operations (image, preimage, reachability)
- All CTL operators (EX, AX, EF, AF, EG, AG, EU, AU)
- Property verification on toggle and counter systems

All tests passing ✓

## Future Work

- **Counterexample generation**: Witness traces and looping counterexamples (NuSMV-style)
- **LTL model checking**: Linear Temporal Logic via Büchi automata
- **Fairness constraints**: Weak and strong fairness
- **Taint analysis**: Information flow tracking
- **Compositional verification**: Assume-guarantee reasoning
- **SMV modeling language**: Parser and compiler
- **Classic benchmarks**: Mutual exclusion, dining philosophers, cache coherence protocols

## References

1. **Symbolic Model Checking: 10^20 States and Beyond** - Burch et al. (1990) - The foundational paper
2. **Model Checking** - Clarke, Grumberg, Peled (1999) - Comprehensive textbook
3. **Principles of Model Checking** - Baier & Katoen (2008) - Modern treatment
4. **NuSMV** - Cimatti et al. (2000) - Open-source model checker with optimizations
