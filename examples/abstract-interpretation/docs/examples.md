# Examples Catalog: BDD-Guided Abstract Interpretation

## 1. Simple Educational Examples

### Example 1.1: Basic Counter Analysis

**Program:**

```rust
let x = 0;
while x < 10 {
    x = x + 1;
}
assert!(x == 10);
```

**Step-by-Step Analysis:**

**Initial State:**

```text
Control: ⊤ (all control locations)
Numeric: x ∈ [0, 0]
```

**Iteration 1:**

```text
Entry: x ∈ [0, 0]
Guard (x < 10): x ∈ [0, 0]  ✓ condition holds
Body (x := x + 1): x ∈ [1, 1]
Join with Entry: x ∈ [0, 1]
```

**Iteration 2:**

```text
Entry: x ∈ [0, 1]
Guard: x ∈ [0, 1]  ✓
Body: x ∈ [1, 2]
Join: x ∈ [0, 2]
```

**Iteration 3 (Widening Applied):**

```text
Entry: x ∈ [0, 2]
Guard: x ∈ [0, 2]  ✓
Body: x ∈ [1, 3]
Join: x ∈ [0, 3]
Widen: x ∈ [0, +∞]  ← extrapolate upper bound
```

**Iteration 4 (Fixpoint):**

```text
Entry: x ∈ [0, +∞]
Guard: x ∈ [0, 9]  ← refine with x < 10
Body: x ∈ [1, 10]
Join: x ∈ [0, +∞]  ← no change, fixpoint reached
```

**Exit Condition:**

```text
Exit: ¬(x < 10), so x ≥ 10
Refine: x ∈ [10, +∞] ∩ [0, +∞] = [10, +∞]
```

**Assertion Check:**

```text
x == 10 requires x ∈ [10, 10]
Current: x ∈ [10, +∞]
Result: MAY FAIL (false positive due to widening)
```

**Narrowing Phase:**

```text
Re-analyze with invariant x ∈ [0, +∞]
After refinement: x ∈ [0, 10]
Exit: x ∈ [10, 10]  ✓
Assertion: PROVEN
```

---

### Example 1.2: Conditional Branch

**Program:**

```rust
let y = if x >= 0 {
    x + 10
} else {
    -x
};
assert!(y >= 0);
```

**Without BDD Partitioning:**

```text
Entry: x ∈ [-100, 100]

Branch 1 (x ≥ 0):
  x ∈ [0, 100]
  y = x + 10 → y ∈ [10, 110]

Branch 2 (x < 0):
  x ∈ [-100, -1]
  y = -x → y ∈ [1, 100]

Join:
  y ∈ [10, 110] ⊔ [1, 100] = [1, 110]

Assertion y ≥ 0: ✓ PROVEN
```

**With BDD Partitioning:**

```text
Control State: (pc, cond)
  pc: program counter
  cond: x ≥ 0

BDD Representation:
  Branch1: pc=1 ∧ cond=true → y ∈ [10, 110]
  Branch2: pc=1 ∧ cond=false → y ∈ [1, 100]

Join:
  Merged BDD: pc=2
  Per-control invariants maintained

Assertion: Check both partitions
  ✓ All paths satisfy y ≥ 0
```

---

### Example 1.3: Nested Loops

**Program:**

```rust
let mut i = 0;
let mut j = 0;
while i < 10 {
    j = 0;
    while j < 10 {
        j = j + 1;
    }
    i = i + 1;
}
assert!(i == 10 && j == 10);
```

**Analysis:**

**Inner Loop (j):**

```text
Entry: j ∈ [0, 0]
Fixpoint: j ∈ [0, 10]
Exit: j ∈ [10, 10]
```

**Outer Loop (i):**

```text
Iteration 1:
  i ∈ [0, 0], j ∈ [10, 10]
  i := i + 1 → i ∈ [1, 1]

Iteration 2:
  i ∈ [1, 1], j reset to [0, 0]
  Inner loop → j ∈ [10, 10]
  i := i + 1 → i ∈ [2, 2]

Widening:
  i ∈ [0, +∞], j ∈ [10, 10]

Exit:
  ¬(i < 10) → i ∈ [10, +∞]
  Refine: i ∈ [10, 10], j ∈ [10, 10]

Assertion: ✓ PROVEN
```

---

## 2. Control-Intensive Examples

### Example 2.1: State Machine Controller

**Program:**

```rust
enum State { Init, Ready, Active, Done }

let mut state = State::Init;
let mut value = 0;

for step in 0..100 {
    match state {
        State::Init => {
            value = 0;
            if step > 10 {
                state = State::Ready;
            }
        }
        State::Ready => {
            if value < 50 {
                state = State::Active;
            }
        }
        State::Active => {
            value = value + 1;
            if value >= 50 {
                state = State::Done;
            }
        }
        State::Done => {
            // Stay in Done
        }
    }
}
```

**BDD Encoding:**

```text
State encoding (2 bits):
  Init:   s₁=0, s₀=0
  Ready:  s₁=0, s₀=1
  Active: s₁=1, s₀=0
  Done:   s₁=1, s₀=1

BDD Variables: [s₁, s₀, step_bits...]
```

**Analysis with Product Domain:**

```text
Element: (BDD_control, Interval_numeric)

Initial:
  Control: s₁=0 ∧ s₀=0 (Init)
  Numeric: value ∈ [0, 0], step ∈ [0, 0]

Fixpoint Iterations:

Iter 1:
  Init → Ready transition:
    Control: (s₁=0 ∧ s₀=0 ∧ step>10) → (s₁=0 ∧ s₀=1)
    Numeric: step ∈ [11, 100], value ∈ [0, 0]

  Ready → Active transition:
    Control: (s₁=0 ∧ s₀=1 ∧ value<50) → (s₁=1 ∧ s₀=0)
    Numeric: value ∈ [0, 49]

  Active → Done transition:
    Control: (s₁=1 ∧ s₀=0 ∧ value≥50) → (s₁=1 ∧ s₀=1)
    Numeric: value ∈ [50, 100]

Final Invariants:
  Init: value = 0
  Ready: value ∈ [0, 49]
  Active: value ∈ [0, 49] (increments until 50)
  Done: value ∈ [50, 50]
```

**Precision Advantage:**

- BDD maintains separate numeric invariants per state
- Interval domain alone would merge: value ∈ [0, 50]
- Product domain: precise per-state invariants

---

### Example 2.2: Multi-Flag Configuration

**Program:**

```rust
let mut enable = false;
let mut debug = false;
let mut fast = false;
let mut value = 100;

if input_enable() { enable = true; }
if input_debug() { debug = true; }
if input_fast() { fast = true; }

if enable && !debug {
    value = value / 2;  // Optimize
}
if debug {
    value = value + 10;  // Add overhead
}
if fast && enable {
    value = value - 20;  // Fast path
}

// What is the range of value?
```

**BDD Analysis:**

```text
Control States (3 Boolean flags = 8 combinations):
  BDD Variables: [enable, debug, fast]

Possible Paths:
  1. ¬E ∧ ¬D ∧ ¬F: value ∈ [100, 100]
  2. E ∧ ¬D ∧ ¬F: value ∈ [50, 50]
  3. ¬E ∧ D ∧ ¬F: value ∈ [110, 110]
  4. E ∧ D ∧ ¬F: value ∈ [110, 110]
  5. ¬E ∧ ¬D ∧ F: value ∈ [100, 100]
  6. E ∧ ¬D ∧ F: value ∈ [30, 30]
  7. ¬E ∧ D ∧ F: value ∈ [110, 110]
  8. E ∧ D ∧ F: value ∈ [90, 90]

BDD Representation:
  (¬E ∧ ¬D ∧ ¬F) → value=100
  ∨ (E ∧ ¬D ∧ ¬F) → value=50
  ∨ (D) → value=110  (simplified)
  ∨ (E ∧ ¬D ∧ F) → value=30
  ∨ ...

Join without BDD:
  value ∈ [30, 110]

Join with BDD partitioning:
  Precise value per configuration
```

---

## 3. Real-World Application Examples

### Example 3.1: Traffic Light Controller

**System Description:**

- 4 states: Green, Yellow, Red, AllRed
- Timing constraints: Green≥30s, Yellow=5s, Red≥30s
- Sensor input: car_waiting (boolean)
- Safety: Never two conflicting greens

**Code:**

```rust
enum Light { Green, Yellow, Red, AllRed }

struct TrafficController {
    ns_light: Light,
    ew_light: Light,
    timer: u32,
}

impl TrafficController {
    fn step(&mut self, car_waiting_ew: bool) {
        self.timer += 1;

        match (self.ns_light, self.ew_light) {
            (Light::Green, Light::Red) => {
                if self.timer >= 30 && car_waiting_ew {
                    self.ns_light = Light::Yellow;
                    self.timer = 0;
                }
            }
            (Light::Yellow, Light::Red) => {
                if self.timer >= 5 {
                    self.ns_light = Light::Red;
                    self.ew_light = Light::AllRed;
                    self.timer = 0;
                }
            }
            (Light::Red, Light::AllRed) => {
                if self.timer >= 2 {
                    self.ew_light = Light::Green;
                    self.timer = 0;
                }
            }
            // ... other cases
            _ => {}
        }
    }

    fn check_safety(&self) -> bool {
        !matches!(
            (self.ns_light, self.ew_light),
            (Light::Green, Light::Green) | (Light::Green, Light::Yellow)
        )
    }
}
```

**Analysis:**

**Control State Space:**

- 16 combinations of (ns_light, ew_light)
- BDD encodes with 4 Boolean variables
- Valid states: subset of 16 (e.g., never both Green)

**Numeric Invariants:**

```text
State: (NS=Green, EW=Red)
  → timer ∈ [0, +∞]
  → Widening stabilizes: timer ∈ [0, +∞]
  → Transition at timer ≥ 30

State: (NS=Yellow, EW=Red)
  → timer ∈ [0, 5]
  → Precise bounds (no widening needed)

Safety Property:
  ∀ states. ¬(NS=Green ∧ EW=Green)
  BDD Check: Intersection is empty ✓
```

---

### Example 3.2: Packet Protocol Stack

**System:**

- States: Idle, Receiving, Processing, Sending, Error
- Packet counter: tracks received packets
- Timeout counter: detects stalls
- Buffer size: bounded by MAX_BUFFER

**Code:**

```rust
const MAX_BUFFER: usize = 64;

struct ProtocolStack {
    state: State,
    buffer_size: usize,
    packet_count: u32,
    timeout: u32,
}

fn process_packet(&mut self, packet_arrives: bool) {
    match self.state {
        State::Idle => {
            if packet_arrives {
                self.state = State::Receiving;
                self.timeout = 0;
            }
        }
        State::Receiving => {
            if self.buffer_size < MAX_BUFFER {
                self.buffer_size += 1;
                self.packet_count += 1;
            } else {
                self.state = State::Error;
            }
            if self.buffer_size >= 10 {
                self.state = State::Processing;
            }
        }
        State::Processing => {
            if self.buffer_size > 0 {
                self.buffer_size -= 1;
            } else {
                self.state = State::Sending;
            }
        }
        State::Sending => {
            self.state = State::Idle;
            self.timeout = 0;
        }
        State::Error => {
            // Recovery logic
            self.buffer_size = 0;
            self.state = State::Idle;
        }
    }

    self.timeout += 1;
    if self.timeout > 1000 {
        self.state = State::Error;
    }
}
```

**Analysis Results:**

**Invariants:**

```text
Idle:
  buffer_size ∈ [0, 0]
  timeout ∈ [0, +∞]

Receiving:
  buffer_size ∈ [0, MAX_BUFFER]
  timeout ∈ [0, 1000]
  Transition: buffer_size ≥ 10 → Processing

Processing:
  buffer_size ∈ [0, 63]  (at entry ≥ 10, decrements)
  timeout ∈ [0, 1000]

Sending:
  buffer_size ∈ [0, 0]  (emptied in Processing)

Error:
  buffer_size ∈ [0, MAX_BUFFER]
  timeout ∈ [1000, +∞] (overflow detected)
```

**Safety Properties:**

```text
P1: buffer_size ≤ MAX_BUFFER
  ✓ Checked in Receiving state

P2: timeout < 1000 → state ≠ Error
  ✓ Error only reached when timeout > 1000

P3: state = Sending → buffer_size = 0
  ✓ Invariant enforced by Processing state
```

---

## 4. Integration Examples

### Example 4.1: Integration with Existing Model Checker

**Scenario:** Use BDD-guided AI to compute invariants, feed to model checker

```rust
use bdd_rs::bdd::Bdd;
use bdd_rs::abstract_interp::*;
use bdd_rs::model_checking::*;

fn verify_with_invariants() {
    let bdd = Rc::new(Bdd::default());
    let interval = IntervalDomain;

    // Step 1: Compute invariants with abstract interpretation
    let ctx = AnalysisContext::new(bdd.clone(), interval);
    let program = load_program("traffic_light.rs");
    let initial = initial_state(&program);
    let invariants = ctx.analyze(&program, initial);

    // Step 2: Convert invariants to BDD assertions
    let mut ts = TransitionSystem::new(bdd.clone());
    for (state, numeric_inv) in invariants {
        let bdd_inv = encode_numeric_to_bdd(&ts, numeric_inv);
        ts.add_label(format!("inv_{}", state), bdd_inv);
    }

    // Step 3: Model check with strengthened invariants
    let property = CtlFormula::ag(CtlFormula::atom("safety"));
    let result = model_check(&ts, &property);

    println!("Verification result: {:?}", result);
}
```

---

### Example 4.2: Integration with SMT Solver

**Scenario:** Use BDD for control, SMT for complex numeric constraints

```rust
use z3::*;

struct HybridAnalyzer {
    bdd: Rc<Bdd>,
    interval: IntervalDomain,
    smt_ctx: Context,
}

impl HybridAnalyzer {
    fn analyze_with_smt(&self, program: &Stmt) {
        // Use intervals for fast over-approximation
        let interval_result = self.analyze_interval(program);

        // For assertions, use SMT for precise check
        for assertion in program.assertions() {
            let control_states = self.extract_control_states(&interval_result);

            for state in control_states {
                let numeric_inv = self.get_numeric_invariant(state);

                // Encode to SMT
                let smt_inv = self.encode_to_smt(&numeric_inv);
                let smt_assert = self.encode_assertion(assertion);

                let solver = Solver::new(&self.smt_ctx);
                solver.assert(&smt_inv);
                solver.assert(&smt_assert.not());

                match solver.check() {
                    SatResult::Unsat => {
                        println!("Assertion proven for state {}", state);
                    }
                    SatResult::Sat => {
                        println!("Counterexample found!");
                    }
                    SatResult::Unknown => {
                        println!("SMT solver timeout");
                    }
                }
            }
        }
    }
}
```

---

## 5. Tutorial: Building Your First Analysis

### Step 1: Setup

```rust
use std::rc::Rc;
use bdd_rs::bdd::Bdd;
use bdd_rs::abstract_interp::*;

fn main() {
    // Create BDD manager
    let bdd = Rc::new(Bdd::default());

    // Choose numeric domain
    let interval_domain = IntervalDomain;

    // Create analysis context
    let ctx = AnalysisContext::new(bdd.clone(), interval_domain);

    println!("Analysis context created!");
}
```

### Step 2: Define Program

```rust
// Build abstract syntax tree
let program = Stmt::Seq(
    Box::new(Stmt::Assign(
        "x".into(),
        NumExpr::Const(0),
    )),
    Box::new(Stmt::While(
        NumPred::Lt(
            NumExpr::Var("x".into()),
            NumExpr::Const(10),
        ),
        Box::new(Stmt::Assign(
            "x".into(),
            NumExpr::Add(
                Box::new(NumExpr::Var("x".into())),
                Box::new(NumExpr::Const(1)),
            ),
        )),
    )),
);
```

### Step 3: Run Analysis

```rust
// Initial state
let initial = ProductElement {
    control: bdd.one,  // Any control location
    numeric: {
        let mut elem = IntervalElement::new();
        elem.set("x".into(), Interval::constant(0));
        elem
    },
};

// Analyze
let result = ctx.analyze(&program, initial);

println!("Final invariant:");
println!("  Control: {}", result.control);
println!("  x ∈ {}", result.numeric.get("x"));
```

### Step 4: Check Assertions

```rust
fn check_assertion(
    result: &ProductElement<Ref, IntervalElement>,
    var: &str,
    expected: i64,
) -> bool {
    if let Some(actual) = result.numeric.get_constant(var) {
        actual == expected
    } else {
        false  // Not uniquely determined
    }
}

let verified = check_assertion(&result, "x", 10);
println!("Assertion verified: {}", verified);
```

---

## 6. Common Pitfalls and Solutions

### Pitfall 1: Over-Widening

**Problem:** Widening too aggressively loses precision

**Solution:**

```rust
// Increase widening threshold
let engine = FixpointEngine {
    widening_threshold: 5,  // Instead of 3
    narrowing_iterations: 3,
    ..Default::default()
};
```

### Pitfall 2: BDD Explosion

**Problem:** Too many Boolean variables cause BDD blowup

**Solution:**

- Use variable grouping
- Apply dynamic reordering
- Limit control partitioning depth

```rust
// Configure BDD with more capacity and reordering
let bdd = Bdd::new(24);  // 16M nodes
// Enable dynamic reordering (if implemented)
```

### Pitfall 3: Imprecise Interval Analysis

**Problem:** Intervals too coarse for relational properties

**Solution:**

- Use octagon or polyhedra domain
- Manually specify relational invariants
- Apply predicate abstraction

```rust
// Switch to octagon domain
let octagon_domain = OctagonDomain::new();
let ctx = AnalysisContext::new(bdd.clone(), octagon_domain);
```

---

**Summary:** This catalog provides progressively complex examples demonstrating the power and flexibility of BDD-guided abstract interpretation. Start with simple loops, progress to control-intensive systems, and finally tackle real-world applications like protocol stacks and embedded controllers.

---

## 8. New Domain Examples

### Example 8.1: Sign Analysis for Division Safety

See `examples/realistic_programs.rs` for full implementations of:

1. **Array Bounds Checking**: Detects out-of-bounds access using Sign + Interval domains
2. **Constant Propagation**: Dead code elimination using Constant domain
3. **Pointer Alias Analysis**: Must-alias and may-alias detection using Points-to domain
4. **Combined Multi-Domain Analysis**: Memory safety verification with all domains
5. **Reduced Product**: Sign × Constant × Interval cooperation for maximum precision

**Run with:** `cargo run --example realistic_programs`

**Integration tests** in `tests/domain_integration.rs` demonstrate:

- Domain cooperation (Sign, Constant, Interval, Points-to)
- Pointer arithmetic with numeric domains
- Combined sign/interval/points-to analysis

**Run with:** `cargo test --test domain_integration`
