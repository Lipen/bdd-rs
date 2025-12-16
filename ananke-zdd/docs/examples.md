# Practical Examples & Patterns

## Pattern 1: Combinatorial Enumeration

### All K-Element Subsets

```rust
use ananke_zdd::zdd::ZddManager;
use ananke_zdd::types::Var;

fn main() {
    let mgr = ZddManager::new();

    // Find all 3-element subsets from {1,2,3,4,5}
    let subsets = mgr.combinations([1u32, 2, 3, 4, 5], 3);

    println!("C(5,3) = {}", mgr.count(subsets));  // 10

    for set in mgr.iter_sets(subsets) {
        println!("{:?}", set);
    }
}
```

**Output**:

```
C(5,3) = 10
[Var(1), Var(2), Var(3)]
[Var(1), Var(2), Var(4)]
...
[Var(3), Var(4), Var(5)]
```

---

## Pattern 2: Constraint Satisfaction as Set Filtering

### N-Queens Problem

ZDDs represent solutions as sets of occupied board positions.

```rust
fn build_queens_zdd(mgr: &ZddManager, n: usize) -> ZddId {
    // Start: all boards with exactly one queen per row
    // Each row-choice is {{(row,col)} | col in 0..n}
    let mut result = mgr.one();

    for row in 0..n {
        let row_choices = mgr.union(
            (0..n)
                .map(|col| mgr.base(Var::new(pos_to_var(row, col, n))))
                .reduce(|a, b| mgr.union(a, b))
                .unwrap_or_else(|| mgr.zero())
        );
        result = mgr.join(result, row_choices);
    }

    // Filter: no two queens in same column
    for col in 0..n {
        let mut col_vars = vec![];
        for row in 0..n {
            col_vars.push(Var::new(pos_to_var(row, col, n)));
        }

        for i in 0..col_vars.len() {
            for j in (i+1)..col_vars.len() {
                result = mgr.remove_sets_with_both(result, col_vars[i], col_vars[j]);
            }
        }
    }

    // Similar filtering for diagonals...
    result
}
```

**Key idea**:

1. Generate candidate solutions (one queen per row)
2. Filter by applying constraints incrementally
3. Each constraint removes invalid configurations

---

## Pattern 3: Set Family Operations

### Filtering and Combining Families

```rust
let mgr = ZddManager::new();

// Family 1: subsets containing element 1
let with_1 = mgr.subset1(some_family, Var::new(1));

// Family 2: subsets NOT containing element 2
let without_2 = mgr.subset0(some_family, Var::new(2));

// Intersection: subsets with 1 but without 2
let result = mgr.intersection(with_1, without_2);

println!("Subsets with {1} but not {2}: {}", mgr.count(result));
```

---

## Pattern 4: Building Families Incrementally

### Pascal's Triangle (Combinatorial Proof)

$$ C(n, k) = C(n-1, k-1) + C(n-1, k) $$

```rust
fn pascal_triangle(mgr: &ZddManager, n: usize) {
    for k in 0..=n {
        let c_nk = mgr.combinations((1..=n as u32).collect::<Vec<_>>(), k);
        println!("C({},{}) = {}", n, k, mgr.count(c_nk));
    }
}

fn main() {
    let mgr = ZddManager::new();
    pascal_triangle(&mgr, 5);
}
```

**Output**:

```
C(5,0) = 1
C(5,1) = 5
C(5,2) = 10
C(5,3) = 10
C(5,4) = 5
C(5,5) = 1
```

---

## Pattern 5: Element Toggling

### Analyzing Symmetric Difference

```rust
let mgr = ZddManager::new();

let f = mgr.powerset([1u32, 2, 3]);  // All 8 subsets of {1,2,3}

// Toggle element 1 in all sets
let toggled = mgr.change(f, Var::new(1));

// Result: for each set S in f,
//   - if 1 in S: S \ {1}
//   - if 1 not in S: S ∪ {1}

// So toggling maps:
// {} → {1}, {1} → {}, {2} → {1,2}, {1,2} → {2}, etc.

assert_eq!(mgr.count(f), mgr.count(toggled));  // Same number of sets
```

---

## Pattern 6: Cross-Product Enumeration

### Generating Permutations (Conceptually)

ZDDs don't directly enumerate permutations, but you can use join to combine partial solutions:

```rust
let mgr = ZddManager::new();

// Represent "position i can have value j"
fn position_choices(mgr: &ZddManager, n: usize) -> ZddId {
    let mut result = mgr.one();

    for pos in 0..n {
        // For each position, choose one value: {(pos,0), (pos,1), ..., (pos,n-1)}
        let choices = mgr.union(
            (0..n)
                .map(|val| mgr.base(Var::new(encode(pos, val))))
                .reduce(|a, b| mgr.union(a, b))
                .unwrap_or_else(|| mgr.zero())
        );
        result = mgr.join(result, choices);
    }

    result  // All n^n possible assignments
}

fn encode(pos: usize, val: usize) -> u32 {
    (pos * 100 + val + 1) as u32
}
```

---

## Pattern 7: Membership Queries

### Checking Solutions

```rust
let mgr = ZddManager::new();
let solutions = build_queens_zdd(&mgr, 4);

// Manually encode one solution
let sol = vec![
    Var::new(pos_to_var(0, 2, 4)),  // Row 0, Col 2
    Var::new(pos_to_var(1, 0, 4)),  // Row 1, Col 0
    Var::new(pos_to_var(2, 3, 4)),  // Row 2, Col 3
    Var::new(pos_to_var(3, 1, 4)),  // Row 3, Col 1
];

if mgr.contains(solutions, &sol) {
    println!("This is a valid 4-Queens solution!");
} else {
    println!("Not a valid solution.");
}
```

---

## Pattern 8: Filtering by Constraints

### Remove Conflicting Configurations

```rust
let mgr = ZddManager::new();

// Start with all boards
let mut boards = all_possible_boards(&mgr, n);

// Define conflicts: pairs of variables that can't both be true
let conflicts = vec![
    (Var::new(1), Var::new(5)),   // Conflict 1
    (Var::new(3), Var::new(7)),   // Conflict 2
    (Var::new(2), Var::new(4)),   // Conflict 3
];

for (v1, v2) in conflicts {
    boards = mgr.remove_sets_with_both(boards, v1, v2);
}

println!("Valid configurations: {}", mgr.count(boards));
```

---

## Pattern 9: Analyzing Set Structures

### Count Sets by Size

```rust
fn analyze_family(mgr: &ZddManager, family: ZddId, max_vars: usize) {
    let mut size_counts = vec![0; max_vars + 1];

    for set in mgr.iter_sets(family) {
        size_counts[set.len()] += 1;
    }

    for (size, count) in size_counts.iter().enumerate() {
        if *count > 0 {
            println!("Sets of size {}: {}", size, count);
        }
    }
}

fn main() {
    let mgr = ZddManager::new();
    let ps = mgr.powerset([1u32, 2, 3, 4]);

    analyze_family(&mgr, ps, 4);
}
```

**Output**:

```
Sets of size 0: 1
Sets of size 1: 4
Sets of size 2: 6
Sets of size 3: 4
Sets of size 4: 1
```

---

## Pattern 10: Reducing via Intersection

### Finding Common Configurations

```rust
let mgr = ZddManager::new();

// Constraint families (each represents valid configurations)
let constraint1 = build_no_adjacent(&mgr, n);    // No adjacent elements
let constraint2 = build_no_triple(&mgr, n);      // No three consecutive
let constraint3 = build_max_spacing(&mgr, n);    // Max spacing 5

// Find configurations satisfying all constraints
let valid = mgr.intersection(
    constraint1,
    mgr.intersection(constraint2, constraint3)
);

println!("Valid configurations: {}", mgr.count(valid));
```

---

## Performance Expectations

For typical problems:

| Problem | Variables | ZDD Nodes | Time |
|---------|-----------|-----------|------|
| C(20, 10) | 20 | ~800 | <1ms |
| N-Queens (N=8) | 64 | 373 | 300ms |
| N-Queens (N=10) | 100 | 3,120 | 130s |
| Partition 2^10 | 10 | ~1,000 | 50ms |
| Graph paths (grid 10×10) | 90 | ~50,000 | 2s |

**Takeaway**: ZDDs excel on sparse, structured problems. For dense families, consider simpler representations.

---

## Common Pitfalls

### 1. Variable Ordering

```rust
// Bad: Random ordering
let vars = [42, 1, 88, 3, 19, ...];  // Jumbled
for v in vars {
    mgr.ensure_var(Var::new(v));
}
// Result: Huge intermediate ZDDs

// Good: Ordered by problem structure
for row in 0..n {
    for col in 0..n {
        mgr.ensure_var(Var::new(row * n + col + 1));
    }
}
```

### 2. Early Filtering

```rust
// Bad: Build complete ZDD first
let all_configs = build_all_configs(&mgr, ...);  // Huge!
let result = mgr.intersection(all_configs, constraints);

// Good: Apply constraints during construction
let result = build_configs_with_constraints(&mgr, ...);  // Smaller!
```

### 3. Over-Allocation

```rust
// Bad: Pre-allocate all variables
for v in 1..=1000 {
    mgr.ensure_var(Var::new(v));
}
// One: Wasted memory

// Good: Allocate as needed
for elem in selected_elements {
    mgr.ensure_var(Var::new(elem));
}
```

---

## Summary

**ZDD sweet spots**:

- Combinatorial enumeration ($k$-subsets, partitions)
- Sparse constraint satisfaction
- Set family operations with rich semantics

**Use alternative tools if**:

- You need boolean satisfiability directly (use SAT solver + BDD)
- Your family is dense (use hash tables)
- You have just one set (use bit vector)

---

Next: [Back to index →](index.md)
