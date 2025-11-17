# Symbolic Model Checking: Theory and Implementation

This document explains the theoretical foundations and practical implementation details of symbolic model checking using Binary Decision Diagrams (BDDs).

## What is Model Checking?

Model checking is an automated technique for verifying that a system satisfies certain properties. Unlike testing (which checks specific scenarios) or theorem proving (which requires manual proofs), model checking **exhaustively explores all possible behaviors** of a system to verify or refute properties.

### A Simple Example: Traffic Light Controller

Imagine a traffic light system with two states:

- **Red**: Cars must stop
- **Green**: Cars can go

We want to verify: "The light is never both red AND green" (safety property).

Traditional testing might check 100 scenarios. Model checking checks **all possible states** and all possible transitions between them.

## States: What Are They?

A **state** is a complete snapshot of a system at a particular moment. It assigns values to all variables.

### Example: Two-Bit Counter

For a 2-bit counter with variables `x` and `y`:

```text
State 0: x=0, y=0  (binary: 00, decimal: 0)
State 1: x=1, y=0  (binary: 10, decimal: 1)
State 2: x=0, y=1  (binary: 01, decimal: 2)
State 3: x=1, y=1  (binary: 11, decimal: 3)
```

Each state is a boolean assignment to all variables.

### Explicit vs Symbolic Representation

**Explicit representation** (traditional):

- Store each state separately: `{00, 01, 10, 11}`
- Memory: O(number of states)
- Problem: 100 variables → 2^100 states (impossible!)

**Symbolic representation** (BDD-based):

- Store a **formula** that characterizes all states
- Example: "all even states" = `y = 0` (single BDD)
- Memory: O(BDD size) - often much smaller
- Can represent 10^20 states compactly!

### States as Sets

We work with **sets of states** represented as BDD formulas:

```rust
// Set containing just state (x=1, y=0)
let state_set = bdd.apply_and(x_var, bdd.apply_not(y_var));  // x ∧ ¬y

// Set containing all states where x=1 (states 1 and 3)
let x_is_one = x_var;  // just x
```

The BDD is a **characteristic function**: it returns true for states in the set, false otherwise.

## Transition Systems: How Systems Evolve

A **transition system** (Kripke structure) describes how a system changes over time.

### Components

1. **States** (S): All possible configurations
2. **Initial states** (I ⊆ S): Where the system starts
3. **Transition relation** (T ⊆ S × S): Legal moves from one state to another
4. **Atomic propositions** (AP): Properties that can be true/false in states

### Example: Toggle System

```text
System: Single bit that toggles
Variable: x

States: {0, 1}
Initial: {0}
Transitions:
  0 → 1
  1 → 0
Proposition: "on" = {1}
```

### Present and Next State Variables

To encode transitions symbolically, we use **two copies** of each variable:

- **Present-state variables** (unprimed): Current state
  - Example: `x` represents the current value of x
- **Next-state variables** (primed): Next state after transition
  - Example: `x'` represents the value of x after the transition

### Transition Relations

The **transition relation** `T(s, s')` is a formula over present and next-state variables that is true when transitioning from state `s` to state `s'` is legal.

**Example: Toggle system**

```text
T(x, x') = x ⊕ x'  (XOR)
```

This means:

- If `x=0` currently, then `x'=1` next (legal transition)
- If `x=1` currently, then `x'=0` next (legal transition)
- Other combinations are illegal

**Example: 2-bit counter**

```text
Informal: increment by 1 (mod 4)
Variables: x, y (where x is high bit, y is low bit)

Transition relation:
  x' = x ⊕ y     (flip x when y is 1)
  y' = ¬y        (always flip y)

This encodes:
  (0,0) → (0,1)  [0→1: don't flip x, flip y]
  (0,1) → (1,0)  [1→2: flip x, flip y]
  (1,0) → (1,1)  [2→3: don't flip x, flip y]
  (1,1) → (0,0)  [3→0: flip x, flip y]
```

## Image and Preimage: State Space Exploration

These are the fundamental operations for exploring how systems evolve.

### Forward Reachability: Image

**Question**: Given a set of states `from`, what states can we reach in **one step**?

**Formula**: `image(from, T) = ∃s. from(s) ∧ T(s, s')`

**What this means**:

1. Take all states in `from` (using present-state variables)
2. AND with the transition relation T
3. Existentially quantify out the present-state variables
4. The result describes the next states (in next-state variables)
5. Rename next-state variables back to present-state for the result

**Example: Toggle system**

```text
from = {x=0}         (current state set)
T = x ⊕ x'           (transition relation)

Step 1: from(x) ∧ T(x,x') = (¬x) ∧ (x ⊕ x')
        = ¬x ∧ ((x ∧ ¬x') ∨ (¬x ∧ x'))
        = ¬x ∧ x'          (simplified)

Step 2: ∃x. (¬x ∧ x') = x'  (eliminate x)

Step 3: Rename x'→x: result = x  (which represents {x=1})

So: from {x=0} we can reach {x=1} ✓
```

**Intuition**: Image is like asking "where can I go from here?"

### Backward Reachability: Preimage

**Question**: Given a set of states `to`, what states can reach `to` in **one step**?

**Formula**: `preimage(to, T) = ∃s'. T(s, s') ∧ to(s')`

**What this means**:

1. Rename `to` states to use next-state variables
2. AND with the transition relation T
3. Existentially quantify out the next-state variables
4. The result describes the predecessor states (in present-state variables)

**Example: Toggle system**

```text
to = {x=1}           (target state set)
T = x ⊕ x'           (transition relation)

Step 1: Rename to(x) → to(x'): x'

Step 2: T(x,x') ∧ to(x') = (x ⊕ x') ∧ x'
        = x' ∧ ((x ∧ ¬x') ∨ (¬x ∧ x'))
        = ¬x ∧ x'          (simplified)

Step 3: ∃x'. (¬x ∧ x') = ¬x  (eliminate x', which represents {x=0})

So: {x=0} can reach {x=1} ✓
```

**Intuition**: Preimage is like asking "where could I have come from to get here?"

### Why These Operations Matter

**Reachability analysis**: Can we reach a bad state?

```rust
let mut reached = initial_states;
loop {
    let new_states = image(reached, transition);
    let expanded = reached ∪ new_states;
    if expanded == reached {
        return reached;  // Found all reachable states
    }
    reached = expanded;
}
```

If `bad_states ∩ reached ≠ ∅`, then the bad state is reachable (bug found!).

## CTL: Temporal Logic for System Properties

CTL (Computation Tree Logic) lets us express properties about how systems evolve over time.

### The Computation Tree

From any state, multiple futures are possible (non-determinism). This creates a tree:

```text
        s0 (initial state)
       /  \
      s1   s2
     / \    |
    s3  s4  s5
    ...
```

Each path through the tree is one possible execution.

### Path Quantifiers: A and E

- **A** (All paths): Property holds on **every** possible execution
- **E** (Exists path): Property holds on **at least one** execution

### Temporal Operators: X, F, G, U

- **X** (neXt): Property holds in the immediate next state
- **F** (Future/Eventually): Property becomes true at some point
- **G** (Globally/Always): Property stays true forever
- **U** (Until): First property holds until second becomes true

### CTL Formulas: Combining Quantifiers and Operators

CTL requires pairing **one quantifier** with **one temporal operator**:

- **EX φ**: There exists a next state where φ holds
- **AX φ**: In all next states, φ holds
- **EF φ**: There exists a path where φ eventually holds
- **AF φ**: On all paths, φ eventually holds
- **EG φ**: There exists a path where φ always holds
- **AG φ**: On all paths, φ always holds
- **E[φ U ψ]**: There exists a path where φ holds until ψ
- **A[φ U ψ]**: On all paths, φ holds until ψ

### Concrete Example: Mutual Exclusion

Two processes competing for a critical section:

```text
Variables:
  - cs1: process 1 in critical section
  - cs2: process 2 in critical section

Property: "Mutual exclusion is maintained"
Formula: AG(¬(cs1 ∧ cs2))

Meaning: On ALL paths (A), it is ALWAYS true (G) that
         NOT both processes are in the critical section
```

If model checking returns true: system is correct!
If false: there's a path where both can enter (bug found).

### Safety vs Liveness

**Safety**: "Bad things never happen"

- Formula: `AG(¬bad)`
- Example: "No deadlock", "No buffer overflow"

**Liveness**: "Good things eventually happen"

- Formula: `AF(good)`
- Example: "Request eventually gets response", "Process eventually terminates"

## CTL Model Checking Algorithm

The key insight: Compute the **set of states** satisfying a formula.

### Fixpoint Computation

Many CTL operators are defined via **fixpoints** - iterating a function until it stabilizes.

**Least fixpoint** (μZ. f(Z)):

- Start from the empty set (∅)
- Apply f repeatedly: ∅, f(∅), f(f(∅)), ...
- Stop when result doesn't change
- Gives the **smallest** set satisfying the equation

**Greatest fixpoint** (νZ. f(Z)):

- Start from the universal set (all states)
- Apply f repeatedly
- Gives the **largest** set satisfying the equation

### Example: EF φ (Exists Eventually)

**Formula**: μZ. φ ∨ EX Z

**Intuition**: States where φ is reachable

- Base: States where φ already holds
- Induction: States that can reach (in one step) states already in Z

**Algorithm**:

```text
Z₀ = SAT(φ)              [states where φ holds now]
Z₁ = φ ∨ EX Z₀           [φ now OR can reach φ in 1 step]
Z₂ = φ ∨ EX Z₁           [φ now OR can reach φ in ≤2 steps]
...
Zₙ = φ ∨ EX Zₙ₋₁          [fixpoint: can reach φ in ≤n steps]
```

**Example: Can we reach state (1,1)?**

```text
System: 2-bit counter starting at (0,0)
φ = (x ∧ y)  [state (1,1)]

Z₀ = {(1,1)}
Z₁ = {(1,1)} ∪ preimage({(1,1)}) = {(1,1), (1,0)}
Z₂ = {(1,1)} ∪ preimage({(1,1), (1,0)}) = {(1,1), (1,0), (0,1)}
Z₃ = {(1,1)} ∪ preimage({(1,1), (1,0), (0,1)}) = {(1,1), (1,0), (0,1), (0,0)}
Z₄ = Z₃  [fixpoint reached]

Result: All states can reach (1,1) ✓
```

### Example: AG φ (Always Globally)

**Formula**: νZ. φ ∧ AX Z

**Intuition**: States where φ holds and CONTINUES to hold

- Must hold now (φ)
- Must hold after every transition (AX Z)

**Algorithm**:

```text
Z₀ = All states
Z₁ = φ ∧ AX Z₀           [φ holds and all successors in Z₀]
Z₂ = φ ∧ AX Z₁           [φ holds and can only go to states in Z₁]
...
```

**Example: Does x always equal 0?**

```text
System: 2-bit counter
φ = ¬x  [x=0]

Z₀ = {(0,0), (1,0), (0,1), (1,1)}  [all states]
Z₁ = ¬x ∧ AX Z₀ = {(0,0), (0,1)}   [x=0 states]
Z₂ = ¬x ∧ AX Z₁ = ∅                [no x=0 state has only x=0 successors]

Result: Empty set - AG(¬x) is false ✗
```

## Putting It All Together: A Complete Example

Let's verify a simple mutex protocol.

### System Description

```text
Two processes want to access a critical section
Variables:
  - req1, req2: request flags
  - cs1, cs2: critical section flags

Initial state: req1=0, req2=0, cs1=0, cs2=0

Transitions:
  Process 1: If req2=0, then can set cs1=1
  Process 2: If req1=0, then can set cs2=1
  Either process can release (cs→0)
```

### Property to Verify

**Mutual exclusion**: `AG(¬(cs1 ∧ cs2))`

"It is always globally true that NOT both are in critical section"

### Model Checking Process

1. **Encode as BDDs**:
   - States: 4 boolean variables (16 possible states)
   - Initial: BDD for (0,0,0,0)
   - Transition: BDD encoding the protocol rules

2. **Check property**:

   ```rust
   let checker = CtlChecker::new(&ts);
   let property = CtlFormula::atom("cs1")
       .and(CtlFormula::atom("cs2"))
       .not()
       .ag();  // AG(¬(cs1 ∧ cs2))

   if checker.holds_initially(&property) {
       println!("✓ Mutex property verified!");
   } else {
       println!("✗ Bug found!");
   }
   ```

3. **What happens internally**:
   - Compute SAT(AG(¬(cs1 ∧ cs2))) using greatest fixpoint
   - Check if initial state ⊆ SAT(property)
   - If not subset, there's a reachable state violating the property

## Why BDDs Make This Practical

### State Explosion Problem

Traditional model checking (explicit state):

- 10 boolean variables → 1024 states
- 20 variables → 1 million states
- 30 variables → 1 billion states
- 100 variables → 10^30 states (impossible!)

### BDD Advantages

1. **Sharing**: Common subformulas shared → exponential compression
2. **Canonicity**: Same formula → same BDD → fast equality checking
3. **Efficient operations**: Boolean operations in polynomial time (in BDD size)

**Example**: All even numbers from 0 to 2^100

- Explicit: Store 2^99 numbers (impossible)
- BDD: Just encode "last bit = 0" (tiny BDD!)

### When BDDs Work Well

- Regular structures (counters, protocols, hardware)
- Formulas with sharing
- Good variable ordering

### When BDDs Struggle

- Irregular structures
- Multiplication (BDDs for multipliers are large)
- Bad variable ordering → exponential blowup

## Implementation in This Library

### Key Design Decisions

1. **Variable pairs**: Each state variable gets TWO BDD variables (present/next)
2. **Explicit image/preimage**: We implement exists + rename directly
3. **Fixpoint via iteration**: Loop until BDD doesn't change
4. **Symbolic throughout**: Never enumerate states explicitly

### Code Flow Example

```rust
// User code
let mut ts = TransitionSystem::new(bdd);
ts.declare_var(x);  // Allocates BDD vars 1 (x) and 2 (x')

// Internal: image computation
fn image(&self, from: Ref) -> Ref {
    // 1. from(x) ∧ T(x,x')
    let conj = bdd.apply_and(from, transition);

    // 2. ∃x. conj
    let result = exists(conj, [1]);  // Eliminate var 1 (present x)

    // 3. Rename x' → x
    rename(result, [2], [1])  // Map var 2 to var 1
}
```

Every operation maintains the symbolic invariant: never enumerate states!

## Summary

**Key Concepts**:

- **States**: Complete assignments to variables, represented symbolically as BDD formulas
- **Transitions**: Relation T(s,s') over present/next variables
- **Image/Preimage**: Forward/backward reachability using ∃ quantification
- **CTL**: Temporal logic combining path quantifiers (A/E) with temporal operators (X/F/G/U)
- **Fixpoints**: Iterative computation of operator semantics (μ for least, ν for greatest)
- **BDDs**: Compact representation enabling verification of huge state spaces

**The Magic**: By representing sets of states symbolically (not individually), we can verify systems with 10^20+ states that would be impossible with explicit enumeration.
