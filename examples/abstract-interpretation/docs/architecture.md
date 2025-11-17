# Architecture Design: BDD-Guided Abstract Interpretation

## 1. System Architecture Overview

### 1.1 High-Level Components

```text
┌─────────────────────────────────────────────────────────────┐
│                    Analysis Driver                          │
│  (Fixpoint Computation, Widening/Narrowing Control)        │
└─────────────────────┬───────────────────────────────────────┘
                      │
        ┌─────────────┴─────────────┐
        │                           │
┌───────▼────────┐          ┌───────▼─────────┐
│  BDD Manager   │          │  Numeric Domain │
│   (Control)    │◄────────►│    (Data)       │
└────────────────┘          └─────────────────┘
        │                           │
        │    Product Domain         │
        │  (BDD × Numeric)          │
        └─────────────┬─────────────┘
                      │
        ┌─────────────▼─────────────┐
        │   Transfer Functions      │
        │  (Statement Semantics)    │
        └───────────────────────────┘
```

### 1.2 Core Design Principles

1. **Separation of Concerns**: BDD and numeric domains are independent
2. **Composability**: Different numeric domains can be plugged in
3. **Extensibility**: New domains and operations via traits
4. **Integration**: Leverage existing `bdd-rs` infrastructure
5. **Performance**: Minimize allocations, use arena/interning patterns

## 2. Trait Hierarchy

### 2.1 Abstract Domain Trait

```rust
/// Core abstract domain interface
pub trait AbstractDomain: Clone + Debug + PartialEq {
    /// The type representing abstract elements
    type Element: Clone + Debug;

    /// Create the bottom element (empty set, infeasible)
    fn bottom() -> Self::Element;

    /// Create the top element (all states, no information)
    fn top() -> Self::Element;

    /// Check if element is bottom
    fn is_bottom(&self, elem: &Self::Element) -> bool;

    /// Check if element is top
    fn is_top(&self, elem: &Self::Element) -> bool;

    /// Partial order: elem1 ⊑ elem2 (elem1 is more precise)
    fn le(&self, elem1: &Self::Element, elem2: &Self::Element) -> bool;

    /// Join (least upper bound, over-approximation)
    fn join(&self, elem1: &Self::Element, elem2: &Self::Element) -> Self::Element;

    /// Meet (greatest lower bound, refinement)
    fn meet(&self, elem1: &Self::Element, elem2: &Self::Element) -> Self::Element;

    /// Widening operator (ensures termination)
    fn widen(&self, elem1: &Self::Element, elem2: &Self::Element) -> Self::Element;

    /// Narrowing operator (refines over-approximation)
    fn narrow(&self, elem1: &Self::Element, elem2: &Self::Element) -> Self::Element;
}
```

### 2.2 Numeric Domain Trait

```rust
/// Numeric abstract domain for integers/reals
pub trait NumericDomain: AbstractDomain {
    /// Variable type (e.g., String, u32)
    type Var: Clone + Eq + Hash + Debug;

    /// Numeric value type (e.g., i64, BigInt)
    type Value: Clone + Debug;

    /// Create element representing single variable assignment
    fn constant(&self, var: &Self::Var, value: Self::Value) -> Self::Element;

    /// Create interval constraint: var ∈ [low, high]
    fn interval(&self, var: &Self::Var, low: Self::Value, high: Self::Value) -> Self::Element;

    /// Assignment: var := expr
    fn assign(&self, elem: &Self::Element, var: &Self::Var, expr: &NumExpr<Self::Var>) -> Self::Element;

    /// Assume predicate (guard): elem ∧ (pred is true)
    fn assume(&self, elem: &Self::Element, pred: &NumPred<Self::Var>) -> Self::Element;

    /// Projection: forget variable (existential quantification)
    fn project(&self, elem: &Self::Element, var: &Self::Var) -> Self::Element;

    /// Get concrete value if variable is constant
    fn get_constant(&self, elem: &Self::Element, var: &Self::Var) -> Option<Self::Value>;

    /// Get interval bounds for variable
    fn get_bounds(&self, elem: &Self::Element, var: &Self::Var) -> Option<(Self::Value, Self::Value)>;
}
```

### 2.3 BDD Control Domain

```rust
/// BDD-based control state domain
pub struct BddDomain {
    bdd: Rc<Bdd>,
}

impl AbstractDomain for BddDomain {
    type Element = Ref;  // BDD reference

    fn bottom() -> Self::Element { Ref::ZERO }
    fn top() -> Self::Element { Ref::ONE }
    fn is_bottom(&self, elem: &Self::Element) -> bool { self.bdd.is_zero(*elem) }
    fn is_top(&self, elem: &Self::Element) -> bool { self.bdd.is_one(*elem) }
    fn le(&self, e1: &Self::Element, e2: &Self::Element) -> bool {
        // e1 ⊑ e2  iff  e1 ⇒ e2  iff  e1 ∧ ¬e2 = 0
        let implies = self.bdd.apply_imply(*e1, *e2);
        self.bdd.is_one(implies)
    }
    fn join(&self, e1: &Self::Element, e2: &Self::Element) -> Self::Element {
        self.bdd.apply_or(*e1, *e2)
    }
    fn meet(&self, e1: &Self::Element, e2: &Self::Element) -> Self::Element {
        self.bdd.apply_and(*e1, *e2)
    }
    fn widen(&self, _e1: &Self::Element, e2: &Self::Element) -> Self::Element {
        // BDD domain is finite, no widening needed
        *e2
    }
    fn narrow(&self, _e1: &Self::Element, e2: &Self::Element) -> Self::Element {
        *e2
    }
}
```

### 2.4 Product Domain Trait

```rust
/// Product of two abstract domains
pub struct ProductDomain<C, N>
where
    C: AbstractDomain,
    N: AbstractDomain,
{
    control: C,
    numeric: N,
}

pub struct ProductElement<C, N> {
    control: C,
    numeric: N,
}

impl<C, N> AbstractDomain for ProductDomain<C, N>
where
    C: AbstractDomain,
    N: AbstractDomain,
{
    type Element = ProductElement<C::Element, N::Element>;

    fn bottom() -> Self::Element {
        ProductElement {
            control: C::bottom(),
            numeric: N::bottom(),
        }
    }

    fn join(&self, e1: &Self::Element, e2: &Self::Element) -> Self::Element {
        ProductElement {
            control: self.control.join(&e1.control, &e2.control),
            numeric: self.numeric.join(&e1.numeric, &e2.numeric),
        }
    }

    fn widen(&self, e1: &Self::Element, e2: &Self::Element) -> Self::Element {
        ProductElement {
            control: self.control.widen(&e1.control, &e2.control),
            numeric: self.numeric.widen(&e1.numeric, &e2.numeric),
        }
    }

    // ... other operations
}
```

## 3. Numeric Expression and Predicate Types

### 3.1 Numeric Expressions

```rust
/// Numeric expressions (right-hand side of assignments)
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum NumExpr<V> {
    /// Variable
    Var(V),
    /// Constant
    Const(i64),
    /// Addition: e1 + e2
    Add(Box<NumExpr<V>>, Box<NumExpr<V>>),
    /// Subtraction: e1 - e2
    Sub(Box<NumExpr<V>>, Box<NumExpr<V>>),
    /// Multiplication: e1 * e2
    Mul(Box<NumExpr<V>>, Box<NumExpr<V>>),
    /// Division: e1 / e2
    Div(Box<NumExpr<V>>, Box<NumExpr<V>>),
    /// Negation: -e
    Neg(Box<NumExpr<V>>),
    /// Modulo: e1 % e2
    Mod(Box<NumExpr<V>>, Box<NumExpr<V>>),
}
```

### 3.2 Numeric Predicates

```rust
/// Numeric predicates (guards, conditions)
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum NumPred<V> {
    /// True
    True,
    /// False
    False,
    /// Equality: e1 == e2
    Eq(NumExpr<V>, NumExpr<V>),
    /// Inequality: e1 != e2
    Neq(NumExpr<V>, NumExpr<V>),
    /// Less than: e1 < e2
    Lt(NumExpr<V>, NumExpr<V>),
    /// Less or equal: e1 <= e2
    Le(NumExpr<V>, NumExpr<V>),
    /// Greater than: e1 > e2
    Gt(NumExpr<V>, NumExpr<V>),
    /// Greater or equal: e1 >= e2
    Ge(NumExpr<V>, NumExpr<V>),
    /// Negation: !p
    Not(Box<NumPred<V>>),
    /// Conjunction: p1 && p2
    And(Box<NumPred<V>>, Box<NumPred<V>>),
    /// Disjunction: p1 || p2
    Or(Box<NumPred<V>>, Box<NumPred<V>>),
}
```

## 4. Transfer Function Architecture

### 4.1 Statement Types

```rust
/// Program statements
#[derive(Debug, Clone)]
pub enum Stmt<V> {
    /// Skip (no-op)
    Skip,
    /// Assignment: var := expr
    Assign(V, NumExpr<V>),
    /// Sequence: s1; s2
    Seq(Box<Stmt<V>>, Box<Stmt<V>>),
    /// Conditional: if (pred) then s1 else s2
    If(NumPred<V>, Box<Stmt<V>>, Box<Stmt<V>>),
    /// While loop: while (pred) do s
    While(NumPred<V>, Box<Stmt<V>>),
    /// Assertion: assert(pred)
    Assert(NumPred<V>),
    /// Assumption: assume(pred)
    Assume(NumPred<V>),
    /// Havoc: var := * (non-deterministic)
    Havoc(V),
}
```

### 4.2 Transfer Function Trait

```rust
/// Abstract transfer function for statements
pub trait TransferFunction<D: AbstractDomain> {
    /// Type of program variables
    type Var;

    /// Apply transfer function: ⟦stmt⟧♯(elem)
    fn apply(&self, domain: &D, elem: &D::Element, stmt: &Stmt<Self::Var>) -> D::Element;

    /// Apply to a set of elements (batch processing)
    fn apply_many(&self, domain: &D, elems: &[D::Element], stmt: &Stmt<Self::Var>) -> Vec<D::Element> {
        elems.iter().map(|e| self.apply(domain, e, stmt)).collect()
    }
}
```

### 4.3 Product Domain Transfer Function

```rust
pub struct ProductTransferFunction<CV, NV> {
    control_var: PhantomData<CV>,
    numeric_var: PhantomData<NV>,
}

impl<C, N> TransferFunction<ProductDomain<C, N>> for ProductTransferFunction<C::Var, N::Var>
where
    C: AbstractDomain,
    N: NumericDomain,
{
    type Var = N::Var;

    fn apply(&self, domain: &ProductDomain<C, N>, elem: &ProductElement<C::Element, N::Element>, stmt: &Stmt<Self::Var>) -> ProductElement<C::Element, N::Element> {
        match stmt {
            Stmt::Skip => elem.clone(),

            Stmt::Assign(var, expr) => {
                // Only numeric part changes
                ProductElement {
                    control: elem.control.clone(),
                    numeric: domain.numeric.assign(&elem.numeric, var, expr),
                }
            }

            Stmt::If(pred, then_stmt, else_stmt) => {
                // Branch on predicate
                let then_numeric = domain.numeric.assume(&elem.numeric, pred);
                let else_pred = NumPred::Not(Box::new(pred.clone()));
                let else_numeric = domain.numeric.assume(&elem.numeric, &else_pred);

                let then_elem = ProductElement { control: elem.control.clone(), numeric: then_numeric };
                let else_elem = ProductElement { control: elem.control.clone(), numeric: else_numeric };

                let then_result = self.apply(domain, &then_elem, then_stmt);
                let else_result = self.apply(domain, &else_elem, else_stmt);

                domain.join(&then_result, &else_result)
            }

            // ... other cases
        }
    }
}
```

## 5. Fixpoint Computation Engine

### 5.1 Fixpoint Iterator

```rust
/// Fixpoint computation with widening/narrowing
pub struct FixpointEngine<D: AbstractDomain> {
    domain: D,
    widening_threshold: usize,
    narrowing_iterations: usize,
}

impl<D: AbstractDomain> FixpointEngine<D> {
    /// Compute least fixpoint: µX. F(X) ⊔ init
    pub fn lfp<F>(&self, init: D::Element, f: F) -> D::Element
    where
        F: Fn(&D::Element) -> D::Element,
    {
        let mut x = init.clone();
        let mut iterations = 0;

        loop {
            let fx = f(&x);
            let next = self.domain.join(&init, &fx);

            if self.domain.le(&next, &x) {
                // Fixpoint reached
                break;
            }

            iterations += 1;

            if iterations >= self.widening_threshold {
                // Apply widening
                x = self.domain.widen(&x, &next);
            } else {
                x = next;
            }

            // Safety: prevent infinite loops
            if iterations > 1000 {
                panic!("Fixpoint computation did not converge after 1000 iterations");
            }
        }

        // Optional: narrowing phase for precision
        if self.narrowing_iterations > 0 {
            self.narrow(x, f)
        } else {
            x
        }
    }

    /// Narrowing phase
    fn narrow<F>(&self, mut x: D::Element, f: F) -> D::Element
    where
        F: Fn(&D::Element) -> D::Element,
    {
        for _ in 0..self.narrowing_iterations {
            let fx = f(&x);
            let next = self.domain.join(&fx, &self.domain.narrow(&x, &fx));
            if self.domain.le(&x, &next) {
                break;
            }
            x = next;
        }
        x
    }

    /// Compute greatest fixpoint: νX. F(X) ⊓ init
    pub fn gfp<F>(&self, init: D::Element, f: F) -> D::Element
    where
        F: Fn(&D::Element) -> D::Element,
    {
        let mut x = init.clone();

        loop {
            let fx = f(&x);
            let next = self.domain.meet(&init, &fx);

            if self.domain.le(&x, &next) {
                break;
            }

            x = next;
        }

        x
    }
}
```

## 6. Concrete Numeric Domain Implementations

### 6.1 Interval Domain

```rust
pub struct IntervalDomain;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Interval {
    low: Bound,
    high: Bound,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum Bound {
    NegInf,
    Finite(i64),
    PosInf,
}

pub struct IntervalElement {
    intervals: HashMap<String, Interval>,
}

impl NumericDomain for IntervalDomain {
    type Var = String;
    type Value = i64;
    type Element = IntervalElement;

    // Implementation details...
}
```

### 6.2 Octagon Domain (Simplified)

```rust
pub struct OctagonDomain;

/// Difference Bound Matrix representation
pub struct OctagonElement {
    /// Matrix of constraints: x_i - x_j ≤ c_ij
    dbm: Vec<Vec<Bound>>,
    /// Variable mapping
    vars: Vec<String>,
}

impl NumericDomain for OctagonDomain {
    type Var = String;
    type Value = i64;
    type Element = OctagonElement;

    // Implementation using DBM operations
}
```

## 7. Integration with Existing BDD Infrastructure

### 7.1 Leveraging Current Features

```rust
use bdd_rs::bdd::Bdd;
use bdd_rs::reference::Ref;

/// Analysis context integrating BDD and numeric domains
pub struct AnalysisContext<N: NumericDomain> {
    /// Shared BDD manager
    bdd: Rc<Bdd>,
    /// Numeric domain
    numeric: N,
    /// Product domain
    product: ProductDomain<BddDomain, N>,
}

impl<N: NumericDomain> AnalysisContext<N> {
    pub fn new(bdd: Rc<Bdd>, numeric: N) -> Self {
        let bdd_domain = BddDomain { bdd: bdd.clone() };
        let product = ProductDomain {
            control: bdd_domain,
            numeric: numeric.clone(),
        };
        Self { bdd, numeric, product }
    }

    /// Analyze a program starting from initial state
    pub fn analyze(&self, program: &Stmt<N::Var>, initial: ProductElement<Ref, N::Element>) -> ProductElement<Ref, N::Element> {
        let transfer = ProductTransferFunction::new();
        let engine = FixpointEngine {
            domain: self.product.clone(),
            widening_threshold: 3,
            narrowing_iterations: 2,
        };

        // For loops, compute fixpoint
        match program {
            Stmt::While(pred, body) => {
                engine.lfp(initial, |state| {
                    // Apply body and loop back
                    let body_result = transfer.apply(&self.product, state, body);
                    let pred_numeric = self.numeric.assume(&body_result.numeric, pred);
                    ProductElement {
                        control: body_result.control,
                        numeric: pred_numeric,
                    }
                })
            }
            _ => transfer.apply(&self.product, &initial, program),
        }
    }
}
```

### 7.2 Control-Data Interaction

```rust
/// Helper for encoding numeric predicates into BDD
pub struct PredicateEncoder {
    bdd: Rc<Bdd>,
    /// Maps predicates to BDD variables
    predicate_map: HashMap<String, u32>,
    next_var: u32,
}

impl PredicateEncoder {
    /// Encode a numeric predicate as a BDD variable
    pub fn encode<V>(&mut self, pred: &NumPred<V>) -> Ref
    where
        V: ToString,
    {
        let pred_str = format!("{:?}", pred);

        if let Some(&var_idx) = self.predicate_map.get(&pred_str) {
            self.bdd.mk_var(var_idx)
        } else {
            let var_idx = self.next_var;
            self.next_var += 1;
            self.predicate_map.insert(pred_str, var_idx);
            self.bdd.mk_var(var_idx)
        }
    }

    /// Create BDD representing control flow based on predicate
    pub fn control_partition<V>(&mut self, pred: &NumPred<V>) -> (Ref, Ref)
    where
        V: ToString,
    {
        let pred_bdd = self.encode(pred);
        let not_pred = self.bdd.apply_not(pred_bdd);
        (pred_bdd, not_pred)
    }
}
```

## 8. Module Organization

```text
bdd-rs/
├── src/
│   ├── lib.rs
│   ├── bdd.rs                    (existing)
│   └── abstract_interp/          (new module)
│       ├── mod.rs
│       ├── domain.rs             (AbstractDomain trait)
│       ├── numeric.rs            (NumericDomain trait)
│       ├── product.rs            (Product domain)
│       ├── interval.rs           (Interval domain impl)
│       ├── octagon.rs            (Octagon domain impl)
│       ├── transfer.rs           (Transfer functions)
│       ├── fixpoint.rs           (Fixpoint engine)
│       ├── expr.rs               (NumExpr, NumPred types)
│       └── encoder.rs            (Predicate encoder)
└── examples/
    └── abstract_interpretation/
        ├── Cargo.toml
        ├── src/
        │   ├── main.rs
        │   ├── simple_loops.rs   (basic examples)
        │   ├── counters.rs       (counter abstractions)
        │   └── mode_controller.rs (embedded system)
        └── README.md
```

## 9. API Design Considerations

### 9.1 Usability Goals

- **Simple for common cases**: Default domain choices (intervals)
- **Flexible for advanced use**: Pluggable domains, custom transfer functions
- **Safe abstractions**: Type system prevents invalid combinations
- **Performance-aware**: Zero-cost abstractions where possible

### 9.2 Example API Usage

```rust
use bdd_rs::bdd::Bdd;
use bdd_rs::abstract_interp::*;

fn main() {
    // Create BDD manager and interval domain
    let bdd = Rc::new(Bdd::default());
    let interval_domain = IntervalDomain::new();

    // Create analysis context
    let ctx = AnalysisContext::new(bdd.clone(), interval_domain);

    // Define program
    let program = Stmt::While(
        NumPred::Lt(NumExpr::Var("x".into()), NumExpr::Const(100)),
        Box::new(Stmt::Assign("x".into(), NumExpr::Add(
            Box::new(NumExpr::Var("x".into())),
            Box::new(NumExpr::Const(1)),
        ))),
    );

    // Initial state: x ∈ [0, 0]
    let initial = ProductElement {
        control: bdd.one,
        numeric: interval_domain.interval(&"x".into(), 0, 0),
    };

    // Analyze
    let result = ctx.analyze(&program, initial);

    println!("Final state: {:?}", result);
}
```

---

**Next Steps:**

1. Implement core traits in `src/abstract_interp/`
2. Provide interval domain as reference implementation
3. Create example programs demonstrating the API
4. Benchmark against pure BDD and pure numeric approaches
