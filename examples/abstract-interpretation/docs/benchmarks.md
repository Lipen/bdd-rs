# Benchmarks & Evaluation: BDD-Guided Abstract Interpretation

## 1. Benchmark Categories

### 1.1 Simple Loops (Baseline Validation)

**Purpose**: Verify correctness and basic precision

**Programs:**

```c
// B1: Counter with constant bound
void counter_simple() {
    int x = 0;
    while (x < 100) {
        x = x + 1;
    }
    assert(x == 100);
}

// B2: Nested counters
void counter_nested() {
    int i = 0, j = 0;
    while (i < 10) {
        j = 0;
        while (j < 10) {
            j = j + 1;
        }
        i = i + 1;
    }
    assert(i == 10 && j == 10);
}

// B3: Down-counting loop
void countdown() {
    int x = 100;
    while (x > 0) {
        x = x - 1;
    }
    assert(x == 0);
}
```

**Expected Results:**

- Interval domain should infer precise bounds
- Widening should stabilize within 3-5 iterations
- Final invariants should satisfy assertions

### 1.2 Control-Intensive Programs

**Purpose**: Demonstrate BDD advantages for control partitioning

**Programs:**

```c
// B4: Mode-based controller (embedded system)
enum Mode { INIT, READY, ACTIVE, ERROR };

void mode_controller() {
    Mode mode = INIT;
    int sensor = 0;
    int actuator = 0;

    for (int step = 0; step < 100; step++) {
        switch (mode) {
            case INIT:
                sensor = read_sensor();
                if (sensor > 0) mode = READY;
                break;
            case READY:
                if (sensor > 50) {
                    mode = ACTIVE;
                    actuator = 1;
                }
                break;
            case ACTIVE:
                if (sensor < 30) {
                    mode = READY;
                    actuator = 0;
                } else if (sensor > 100) {
                    mode = ERROR;
                    actuator = 0;
                }
                break;
            case ERROR:
                actuator = 0;
                // Restart after timeout
                if (step > 80) mode = INIT;
                break;
        }
    }

    // Safety properties:
    assert(mode == INIT || mode == READY || mode == ACTIVE || mode == ERROR);
    assert(actuator == 0 || actuator == 1);
}
```

**Expected Results:**

- BDD represents 4 control modes compactly
- Numeric domain tracks sensor/actuator ranges per mode
- Control partitioning avoids false alarms

**Programs:**

```c
// B5: Boolean flag combinations
void flag_combinations() {
    bool flag1 = false, flag2 = false, flag3 = false;
    int value = 0;

    if (input1()) flag1 = true;
    if (input2()) flag2 = true;
    if (input3()) flag3 = true;

    if (flag1 && flag2) value = 10;
    if (flag1 && flag3) value = value + 20;
    if (flag2 && flag3) value = value + 30;
    if (flag1 && flag2 && flag3) value = value + 40;

    // Possible values: 0, 10, 20, 30, 40, 50, 60, 100
    assert(value >= 0 && value <= 100);
}
```

### 1.3 Path-Sensitive Analysis

**Purpose**: Show precision gains from control-dependent invariants

**Programs:**

```c
// B6: Conditional bounds
void conditional_bounds(int x) {
    int y;
    if (x >= 0) {
        y = x + 10;  // y ∈ [10, +∞]
    } else {
        y = -x;      // y ∈ [0, +∞]
    }
    // Merge: y ∈ [0, +∞]
    assert(y >= 0);
}

// B7: Disjunctive invariant
void disjunctive(int x) {
    int y = 0;
    if (x < 50) {
        y = x;       // y ∈ [0, 49]
    } else {
        y = 100 - x; // y ∈ [-∞, 50]
    }
    // Exact: (x < 50 ∧ y = x) ∨ (x ≥ 50 ∧ y = 100-x)
    // Interval join: y ∈ [-∞, 50]
    // With control partition: precise per branch
}
```

**Expected Results:**

- Product domain maintains separate invariants per control path
- Join at merge points may lose precision
- BDD partitioning prevents spurious counterexamples

### 1.4 Relational Properties

**Purpose**: Test numeric domain expressiveness

**Programs:**

```c
// B8: Difference bounds (suitable for octagons)
void difference_bounds() {
    int x = 0, y = 0;
    while (x < 100) {
        if (x % 2 == 0) {
            y = y + 1;
        }
        x = x + 1;
    }
    // Invariant: x - 2*y = 0 (for even x)
    // Octagon: x - y ≤ c, x + y ≤ c
    assert(y <= 50);
}

// B9: Linear relationship
void linear_relation() {
    int a = 0, b = 0, c = 0;
    while (a < 10) {
        b = b + 2;
        c = c + 3;
        a = a + 1;
    }
    // Invariants: b = 2*a, c = 3*a
    assert(a == 10 && b == 20 && c == 30);
}
```

**Expected Results:**

- Intervals lose relational information
- Octagons capture some relationships (x - y ≤ c)
- Polyhedra (if implemented) capture full linear invariants

### 1.5 Real-World Examples

**Purpose**: Practical validation with realistic programs

**B10: Ring Buffer**

```c
#define SIZE 16

typedef struct {
    int buffer[SIZE];
    int read_idx;
    int write_idx;
    int count;
} RingBuffer;

void ring_buffer_ops(RingBuffer *rb) {
    rb->read_idx = 0;
    rb->write_idx = 0;
    rb->count = 0;

    for (int i = 0; i < 100; i++) {
        if (rb->count < SIZE) {
            // Write
            rb->buffer[rb->write_idx] = i;
            rb->write_idx = (rb->write_idx + 1) % SIZE;
            rb->count++;
        } else {
            // Read
            int val = rb->buffer[rb->read_idx];
            rb->read_idx = (rb->read_idx + 1) % SIZE;
            rb->count--;
        }
    }

    // Invariants:
    assert(rb->read_idx >= 0 && rb->read_idx < SIZE);
    assert(rb->write_idx >= 0 && rb->write_idx < SIZE);
    assert(rb->count >= 0 && rb->count <= SIZE);
}
```

**B11: Autopilot Mode Controller**

```c
enum FlightMode { MANUAL, STABILIZE, AUTO, LANDING };

void autopilot(int altitude, int speed, int distance_to_runway) {
    FlightMode mode = MANUAL;
    int throttle = 0;
    int elevator = 0;

    for (int t = 0; t < 1000; t++) {
        switch (mode) {
            case MANUAL:
                // Pilot control
                if (altitude > 1000 && speed > 50) {
                    mode = STABILIZE;
                }
                break;

            case STABILIZE:
                throttle = 50;
                if (altitude > 5000) {
                    mode = AUTO;
                }
                if (altitude < 500) {
                    mode = MANUAL;
                }
                break;

            case AUTO:
                throttle = 60;
                elevator = altitude > 5000 ? -5 : 5;
                if (distance_to_runway < 1000) {
                    mode = LANDING;
                }
                break;

            case LANDING:
                throttle = 30;
                elevator = -10;
                if (altitude < 100) {
                    throttle = 0;
                    mode = MANUAL;
                }
                break;
        }

        // Update physics (simplified)
        altitude = altitude + elevator;
        speed = speed + (throttle - 50) / 10;
    }

    // Safety properties
    assert(throttle >= 0 && throttle <= 100);
    assert(elevator >= -15 && elevator <= 15);
    assert(mode == MANUAL || mode == STABILIZE || mode == AUTO || mode == LANDING);
}
```

## 2. Evaluation Metrics

### 2.1 Correctness Metrics

**Soundness:**

- No false negatives (missed bugs)
- All assertions proven or flagged

**Precision:**

- False positive rate
- Spurious counterexamples
- Invariant tightness (interval width, constraint count)

### 2.2 Performance Metrics

**Time:**

- Total analysis time
- Time per fixpoint iteration
- BDD operation time vs. numeric domain time
- Convergence speed (iteration count)

**Space:**

- BDD node count
- Peak memory usage
- Abstract element size

### 2.3 Scalability Metrics

**Program Size:**

- Lines of code
- Number of variables
- Control flow complexity (cyclomatic complexity)
- Loop nesting depth

**Analysis Parameters:**

- Widening threshold
- Narrowing iterations
- BDD variable ordering

## 3. Comparison Baselines

### 3.1 Pure BDD Analysis

**Configuration:**

- Bit-blast all numeric variables
- Use BDD for entire state space
- No abstract domains

**Expected Behavior:**

- Precise but may not scale
- Exponential blowup for large integers
- Good for Boolean-heavy programs

### 3.2 Pure Numeric Domain Analysis

**Configuration:**

- No BDD, only interval/octagon domain
- Single global invariant
- Path-insensitive

**Expected Behavior:**

- Scales well for data-heavy programs
- Loses precision on control-dependent properties
- May produce false alarms

### 3.3 Existing Tools (if available)

**CPAchecker:**

- Predicate abstraction + explicit-state
- CEGAR refinement

**Frama-C:**

- Value analysis plugin (intervals + garbled mix)

**Astrée:**

- Commercial tool (if accessible)
- State-of-the-art for embedded C

## 4. Benchmark Organization

### 4.1 Directory Structure

```text
bdd-rs/benchmarks/
├── simple_loops/
│   ├── counter_simple.c
│   ├── counter_nested.c
│   └── countdown.c
├── control_intensive/
│   ├── mode_controller.c
│   ├── flag_combinations.c
│   └── state_machine.c
├── path_sensitive/
│   ├── conditional_bounds.c
│   ├── disjunctive.c
│   └── branch_merge.c
├── relational/
│   ├── difference_bounds.c
│   ├── linear_relation.c
│   └── octagon_test.c
├── real_world/
│   ├── ring_buffer.c
│   ├── autopilot.c
│   └── protocol_stack.c
└── README.md
```

### 4.2 Benchmark Metadata

Each benchmark includes:

```yaml
name: "counter_simple"
category: "simple_loops"
source: "hand-crafted"
description: "Basic counter loop with constant bound"
expected_result: "SAFE"
properties:
  - type: "assertion"
    line: 7
    condition: "x == 100"
variables:
  - name: "x"
    type: "int"
    range: [0, 100]
features:
  - "single_loop"
  - "constant_bound"
  - "interval_sufficient"
difficulty: "easy"
```

## 5. Experimental Protocol

### 5.1 Setup

**Environment:**

- Hardware: 8-core CPU, 32GB RAM
- OS: Linux (Ubuntu 22.04)
- Rust: Latest stable
- Compiler: rustc with release optimizations

**Configuration Files:**

```toml
# analysis_config.toml
[domain]
type = "interval"  # or "octagon", "polyhedra"

[fixpoint]
widening_threshold = 3
narrowing_iterations = 2
max_iterations = 1000

[bdd]
storage_bits = 20  # 1M nodes
cache_bits = 16

[logging]
level = "info"
output = "results/analysis.log"
```

### 5.2 Execution

```bash
# Run single benchmark
cargo run --release --example analyze -- \
    --input benchmarks/simple_loops/counter_simple.c \
    --config analysis_config.toml \
    --output results/counter_simple.json

# Run benchmark suite
./scripts/run_benchmarks.sh --suite all --output results/
```

### 5.3 Data Collection

**Output Format (JSON):**

```json
{
  "benchmark": "counter_simple",
  "timestamp": "2025-11-17T12:00:00Z",
  "configuration": {
    "domain": "interval",
    "widening_threshold": 3,
    "bdd_storage_bits": 20
  },
  "results": {
    "status": "SAFE",
    "analysis_time_ms": 123,
    "iterations": 5,
    "bdd_nodes_peak": 1234,
    "memory_mb": 45,
    "invariants": {
      "x": "[0, 100]"
    },
    "assertions": [
      {
        "line": 7,
        "status": "PROVEN",
        "time_ms": 10
      }
    ]
  }
}
```

## 6. Analysis & Visualization

### 6.1 Statistical Analysis

**Aggregations:**

- Mean, median, stddev for time/memory
- Success rate (proven/flagged/timeout)
- Correlation: program size vs. analysis time

**Plots:**

- Scatter: program size vs. time
- Bar chart: domain comparison (precision/time trade-off)
- Histogram: iteration count distribution
- Heat map: widening threshold vs. precision

### 6.2 Precision Comparison

**Metrics:**

- Invariant width (for intervals)
- Constraint count (for polyhedra)
- False positive rate

**Example:**

```text
Benchmark: conditional_bounds
┌──────────────┬──────────────┬─────────────┬──────────┐
│ Domain       │ Invariant    │ Time (ms)   │ Precise? │
├──────────────┼──────────────┼─────────────┼──────────┤
│ Interval     │ y ∈ [0, +∞]  │ 50          │ No       │
│ BDD×Interval │ Per branch   │ 120         │ Yes      │
│ Octagon      │ y ≥ 0        │ 200         │ No       │
└──────────────┴──────────────┴─────────────┴──────────┘
```

## 7. Expected Outcomes

### 7.1 Hypothesis

**H1:** BDD-guided analysis outperforms pure numeric domains on control-intensive programs.

**Validation:** Compare false positive rates on B4, B5 benchmarks.

**H2:** Interval domain is sufficient for many embedded system properties.

**Validation:** Success rate on real-world benchmarks (B10, B11).

**H3:** Widening threshold of 3 balances precision and performance.

**Validation:** Sensitivity analysis across thresholds 1-10.

### 7.2 Threats to Validity

**Internal:**

- Implementation bugs affecting results
- Suboptimal BDD variable ordering
- Widening strategy not tuned

**External:**

- Benchmarks not representative of real workloads
- Small benchmark suite
- Comparison tools configured differently

**Mitigation:**

- Extensive unit testing
- Cross-validation with manual analysis
- Open-source benchmark suite
- Detailed configuration documentation

## 8. Reporting

### 8.1 Paper Sections

**Abstract:** Summary of approach and key results

**Introduction:** Motivation, problem statement, contributions

**Background:** Abstract interpretation, BDDs, related work

**Approach:** Product domain design, transfer functions, fixpoint

**Implementation:** Rust architecture, domain implementations

**Evaluation:** Benchmark results, performance analysis, case studies

**Discussion:** Precision-performance trade-offs, limitations, future work

**Conclusion:** Summary and impact

### 8.2 Artifact Package

**Contents:**

- Source code (GitHub repository)
- Benchmark suite with expected results
- Configuration files
- VM image for reproducibility
- README with build instructions

**Badges:**

- Artifact Available
- Artifact Evaluated - Functional
- Results Reproduced

---

**Next Document**: `examples.md` - Catalog of simple and complex use cases with step-by-step analysis
