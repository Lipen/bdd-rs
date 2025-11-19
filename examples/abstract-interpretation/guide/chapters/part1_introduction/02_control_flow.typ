#import "../../theme.typ": *

= Understanding Control Flow <understanding-control-flow>

Abstract interpretation handles data abstraction elegantly, as we saw with the sign domain.
But real programs have branches, loops, and complex control flow.
This creates a new challenge: _path explosion._

Consider a simple function:

```rust
fn compute(x: i32, y: i32) -> i32 {
    let mut result = 0;
    if x > 0 {
        result += x;
    }
    if y > 0 {
        result += y;
    }
    result
}
```

Even with just two `if` statements, we have four possible paths:
1. Both conditions false
2. First true, second false
3. First false, second true
4. Both conditions true

With $n$ independent branches, we get $2^n$ paths.
A function with 30 branches has over a billion paths.
We cannot analyze each path separately.

== Control Flow Graphs

We represent programs as _control flow graphs_ (CFGs).

[CFG diagram would go here showing nodes for basic blocks and edges for control flow]

#definition(title: "Control Flow Graph")[
  A CFG is a directed graph where:
  - Nodes represent _basic blocks_ (straight-line code with no branches)
  - Edges represent possible control flow
  - One entry node, one or more exit nodes
]

Example CFG for our function:

```
Entry
  ↓
[result = 0]
  ↓
[x > 0?] ---no--> [y > 0?] ---no--> Exit
  ↓                 ↓
  yes               yes
  ↓                 ↓
[result += x] -> [y > 0?]
                   ↓
                   yes
                   ↓
                [result += y] -> Exit
```

Each path through the CFG corresponds to one possible execution.

== The Path Explosion Problem

Consider analyzing our heater controller from the Prologue:

```rust
fn control_heater(temp: i32, time: i32, mode: Mode) -> Action {
    if mode == Mode::Off {
        return Action::Off;
    }

    if temp < TEMP_MIN {
        if time > EMERGENCY_TIME {
            return Action::EmergencyHeat;
        }
        return Action::HeatOn;
    }

    if temp > TEMP_MAX {
        return Action::HeatOff;
    }

    if mode == Mode::Eco && time > ECO_THRESHOLD {
        return Action::HeatOff;
    }

    Action::Maintain
}
```

This function has 5 conditional branches.
In the worst case, this creates 32 distinct paths.

Now imagine:
- The function is called in a loop
- The loop has its own conditions
- Multiple functions call each other

Real programs have millions or billions of paths.

#warning-box[
  *Path explosion is exponential.*
  Adding one more branch doubles the number of paths.
  Explicit path enumeration is infeasible for real programs.
]

== Path-Sensitive vs Path-Insensitive Analysis

Abstract interpretation offers two strategies:

=== Path-Insensitive Analysis

*Idea:* Merge information from all branches at join points.

```rust
let mut x = 0;
if condition {
    x = 5;
} else {
    x = -3;
}
// What is x here?
```

Path-insensitive analysis:
- After true branch: `x = +`
- After false branch: `x = -`
- After merge: `x = + ⊔ - = ⊤` (unknown)

We lose precision but avoid path explosion.

#info-box(title: "Trade-off")[
  Path-insensitive analysis is _fast_ (polynomial time) but _imprecise_.
  All branch outcomes are merged, losing correlations between variables.
]

=== Path-Sensitive Analysis

*Idea:* Track constraints that hold on each path.

```rust
let mut x = 0;
if condition {
    x = 5;
} else {
    x = -3;
}
// On path where condition=true: x = +
// On path where condition=false: x = -
```

Instead of merging, we maintain:
- Path 1: `condition=true ∧ x=+`
- Path 2: `condition=false ∧ x=-`

This is more precise but creates $2^n$ paths.

#warning-box[
  *Naive path-sensitive analysis is intractable.*
  Explicitly enumerating all paths leads to exponential blowup.
]

== Symbolic Representation of Paths

The key insight: we don't need to enumerate paths explicitly.
We can represent _sets of paths_ symbolically.

Consider:

```rust
if a > 0 {
    // Path constraint: a > 0
}
if b > 0 {
    // Path constraints:
    // - (a > 0) ∧ (b > 0)
    // - (a > 0) ∧ (b ≤ 0)
    // - (a ≤ 0) ∧ (b > 0)
    // - (a ≤ 0) ∧ (b ≤ 0)
}
```

These path constraints are Boolean formulas.
With $n$ conditions, we have $2^n$ formulas.

_But:_ Boolean formulas can be represented compactly using BDDs!

#example-box(number: "2.1", title: "Compact Path Representation")[
  Consider a program with 100 boolean conditions.
  - Number of paths: $2^(100) approx 10^(30)$ (more than atoms in the universe)
  - BDD representation: Often just thousands of nodes

  The BDD exploits sharing between paths with common structure.
]

This is the breakthrough:
- Path-sensitive analysis with BDDs maintains precision
- Symbolic representation avoids explicit enumeration
- Operations on path sets become BDD operations

== Control Flow Meets Abstract Domains

Combining these ideas:

#info-box(title: "Path-Sensitive Abstract Interpretation with BDDs")[
  1. *Control domain:* BDD tracks which paths are feasible
  2. *Data domain:* Abstract domain (signs, intervals, etc.) tracks variable properties
  3. *Combined state:* Pair $(b, rho)$ where $b$ is BDD and $rho$ maps variables to abstract values

  Path sensitivity comes from BDD distinguishing different paths.
]

Example:

```rust
let mut x = 0;
if flag {
    x = 5;
} else {
    x = -3;
}
```

State representation:
- Path 1: $(b_1, {x |-> +})$ where $b_1$ encodes `flag=true`
- Path 2: $(b_2, {x |-> -})$ where $b_2$ encodes `flag=false`

We maintain _separate_ abstract values for each path, but use BDDs to represent paths compactly.

== A Concrete Example: Temperature Controller

Let's revisit the heater controller with this approach.

```rust
fn control_heater(temp: i32, time: i32, mode: Mode) -> Action {
    if mode == Mode::Off {
        return Action::Off;  // Path 1
    }

    if temp < TEMP_MIN {
        if time > EMERGENCY_TIME {
            return Action::EmergencyHeat;  // Path 2
        }
        return Action::HeatOn;  // Path 3
    }

    if temp > TEMP_MAX {
        return Action::HeatOff;  // Path 4
    }

    if mode == Mode::Eco && time > ECO_THRESHOLD {
        return Action::HeatOff;  // Path 5
    }

    Action::Maintain  // Path 6
}
```

Path conditions (simplified):
1. `mode=Off`
2. `mode≠Off ∧ temp<MIN ∧ time>EMERG`
3. `mode≠Off ∧ temp<MIN ∧ time≤EMERG`
4. `mode≠Off ∧ temp≥MIN ∧ temp>MAX`
5. `mode≠Off ∧ temp≥MIN ∧ temp≤MAX ∧ mode=Eco ∧ time>ECO`
6. `mode≠Off ∧ temp≥MIN ∧ temp≤MAX ∧ (mode≠Eco ∨ time≤ECO)`

Without BDDs:
- Must track 6 separate states
- Each state duplication multiplies cost
- Loops create infinite unrolling

With BDDs:
- Single BDD encodes all 6 path conditions
- Boolean operations (∧, ∨, ¬) are efficient
- Common subformulas are shared

#example-box(number: "2.2", title: "BDD Compression")[
  The 6 path conditions above share structure:
  - All except path 1 have `mode≠Off`
  - Paths 2-3 share `temp<MIN`
  - Paths 5-6 share complex conjunction

  A BDD representing these conditions reuses nodes, resulting in far fewer nodes than explicit enumeration.
]

== Handling Loops

Loops create infinite paths in principle:

```rust
let mut count = 0;
while count < n {
    count += 1;
}
```

Possible iterations: 0, 1, 2, ..., $n$, or even infinite if `n` is unknown.

Path-insensitive analysis uses _fixpoint iteration_ (from Chapter 1).
Path-sensitive analysis does the same, but with BDD-represented paths.

Strategy:
1. Start with entry path: $b_0 = "true"$ (all paths enabled)
2. Iterate:
  - Compute paths that exit loop
  - Compute paths that continue
  - Merge with widening if needed
3. Stop when BDD stabilizes

The BDD encodes which loop iterations are feasible.

#insight-box[
  *Key Insight:* BDDs turn the exponential path explosion into a compact symbolic representation.
  Operations on path sets become BDD operations, which are often efficient despite worst-case exponential complexity.
]

== Comparison with Other Approaches

=== Symbolic Execution

Symbolic execution also tracks path conditions but maintains them as logical formulas.

Differences:
- Symbolic execution queries SMT solvers at each branch (expensive)
- Our approach uses BDD operations (often faster for boolean conditions)
- Symbolic execution aims for exact solutions
- Our approach abstracts numeric values (more scalable)

Both suffer from path explosion; symbolic execution typically limits search depth.

=== Model Checking

Model checking explores state space explicitly or symbolically.

Differences:
- Model checking checks specific properties (temporal logic)
- Abstract interpretation computes all reachable states
- Model checking often uses BDDs for state representation
- Our approach uses BDDs for _path_ representation within abstract interpretation

Both use BDDs but for different purposes.

=== Type Systems

Type systems are path-insensitive by design.

Differences:
- Types merge all paths at join points
- No path explosion, very fast
- Very imprecise for value-dependent properties
- Cannot verify assertions like "x > 0"

Type systems are a special case of abstract interpretation with extreme abstraction.

== When Do We Need Path Sensitivity?

Not always!
Path-insensitive analysis suffices for many properties.

#info-box(title: "When Path Sensitivity Helps")[
  1. *Correlated variables:* Properties depend on relationships between variables
  2. *Conditional invariants:* Assertions hold only on some paths
  3. *Error paths:* Detecting bugs in specific scenarios
  4. *Precise null checking:* Tracking which pointers are null on which paths
]

Examples requiring path sensitivity:

```rust
// Correlated variables
if x > 0 {
    y = x + 1;
    assert!(y > 1);  // Path-insensitive loses this
}

// Conditional invariants
if mode == Safe {
    assert!(speed < MAX_SAFE_SPEED);  // Only holds on this path
}

// Error paths
if ptr.is_null() {
    return Err(...);
}
// Here ptr is non-null, but path-insensitive loses this
ptr.dereference()
```

Path-insensitive analysis would merge all branches, losing these properties.

== Summary

Control flow creates path explosion: $2^n$ paths for $n$ branches.
Path-insensitive analysis merges all paths (fast, imprecise).
Path-sensitive analysis tracks paths separately (precise, exponential).

The solution: _symbolic representation_ with BDDs.
Instead of enumerating paths, represent path sets compactly.
BDD operations (∧, ∨, ¬) manipulate path sets efficiently.

Combined with abstract domains, this gives path-sensitive abstract interpretation that scales.

In the next chapter, we introduce Binary Decision Diagrams formally and see how they achieve this compression.

#chapter-summary(
  [
    *Path explosion is exponential.*
    With $n$ branches, we get $2^n$ paths. Real programs have millions to billions of paths.
  ],
  [
    *Control Flow Graphs represent programs structurally.*
    Nodes are basic blocks, edges are control flow. Each path is a sequence of nodes.
  ],
  [
    *Path-insensitive analysis merges branches.*
    Fast (polynomial time) but imprecise. All correlations between variables are lost at join points.
  ],
  [
    *Path-sensitive analysis tracks separate paths.*
    Precise but faces exponential blowup if paths are enumerated explicitly.
  ],
  [
    *Symbolic representation with BDDs solves path explosion.*
    Path conditions are boolean formulas. BDDs compactly represent sets of paths by exploiting shared structure.
  ],
  [
    *Combined approach: BDD control + abstract data domain.*
    BDD tracks feasible paths, abstract domain tracks variable properties. Pair $(b, rho)$ gives path-sensitive analysis.
  ],
  [
    *Not all problems need path sensitivity.*
    Path-insensitive analysis suffices when properties don't depend on control flow correlations.
  ],
  [
    *Main Insight:*
    BDDs transform intractable path-sensitive analysis into a practical technique by compressing exponential path sets into compact symbolic representations.
  ],
)

#v(2em)
