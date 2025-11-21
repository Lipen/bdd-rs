// Chapter 1: The World of Abstract Interpretation

#import "../../theme.typ": *

= The World of Abstract Interpretation <ch-abstraction>

#reading-path(path: "essential") #h(0.5em) #reading-path(path: "beginner")

The Prologue established the need: testing is insufficient, perfect verification is impossible.
We require approximation that is both sound and tractable.
Abstract interpretation provides the mathematical foundation for this compromise.

To make this concrete, we will build a *MiniVerifier* throughout this guide.
We will analyze a simple toy language called *IMP* (Imperative Language).

== The IMP Language

IMP is a minimal language with variables, loops, and conditionals.
It is simple enough to understand fully, yet complex enough to exhibit the challenges of verification.

=== Syntax

IMP programs consist of assignments, sequences, conditionals, and while loops.
Here is a simple example that computes the sum of numbers from 0 to 9:

```rust
// Example IMP program
x = 0;
y = 0;
while x < 10 {
    x = x + 1;
    y = y + x;
}
```

=== The AST (Abstract Syntax Tree)

In our Rust `MiniVerifier`, we represent IMP programs using this AST.
This will be the input to our analysis engine.

```rust
#[derive(Clone, Debug, PartialEq)]
pub enum Expr {
    Var(String),
    Const(i32),
    Add(Box<Expr>, Box<Expr>),
    Sub(Box<Expr>, Box<Expr>),
    // ... other operations
}

#[derive(Clone, Debug, PartialEq)]
pub enum Cond {
    Eq(Expr, Expr),
    Lt(Expr, Expr),
    Le(Expr, Expr),
    And(Box<Cond>, Box<Cond>),
    Or(Box<Cond>, Box<Cond>),
    Not(Box<Cond>),
}

#[derive(Clone, Debug, PartialEq)]
pub enum Stmt {
    Assign(String, Expr),
    Seq(Box<Stmt>, Box<Stmt>),
    If(Cond, Box<Stmt>, Box<Stmt>),
    While(Cond, Box<Stmt>),
    Assert(Cond),
    Skip,
}
```

Our goal is to write a function `analyze(program: &Stmt) -> AnalysisResult` that proves properties about variables in the program.

== The Essence of Abstraction

Abstraction is the art of forgetting details while preserving essential structure.
Consider the integer 5.
- Concrete value: 5
- Sign: Positive (+)
- Parity: Odd
- Interval: [0, 10]

Each of these is an *abstraction* of the value 5.
Abstract Interpretation runs the program using these abstract values instead of concrete numbers.

=== The Sign Domain

Let's start with the simplest useful domain: Signs.
We care only if a number is Negative (-), Zero (0), or Positive (+).

But what if we add `(+) + (-)`? The result could be anything!
We need a value for "I don't know". We call this *Top* ($top$).
And for "Impossible" (e.g., division by zero), we use *Bottom* ($bot$).

The set of values is $D = {bot, -, 0, +, top}$.

=== The Abstract Domain Trait

In Rust, we define this behavior using a trait.
This is the core interface for all analyses in our `MiniVerifier`.

```rust
pub trait AbstractDomain: Sized + Clone + PartialEq + std::fmt::Debug {
    // The "Impossible" value (empty set)
    fn bottom() -> Self;

    // The "Unknown" value (all possible values)
    fn top() -> Self;

    // Combine two possibilities (Union)
    // e.g., if x could be 0 OR x could be +, then x is NonNegative
    fn join(&self, other: &Self) -> Self;

    // Intersect two possibilities
    fn meet(&self, other: &Self) -> Self;
}

=== Bridging Theory and Code: Galois Connections

In the theory of Abstract Interpretation, the relationship between concrete values and abstract values is formalized as a *Galois Connection*.
This involves two functions:
- $alpha$ (alpha): *Abstraction*. Converts a set of concrete values to an abstract value.
- $gamma$ (gamma): *Concretization*. Converts an abstract value back to the set of concrete values it represents.

We can express this in our trait (or as helper functions):

```rust
trait GaloisConnection<C> {
    // Concrete -> Abstract
    fn alpha(concrete: &C) -> Self;

    // Abstract -> Concrete (Set of values)
    fn gamma(&self) -> Vec<C>;
}
```

For our Sign domain:
- `alpha(-5) = Sign::Neg`
- `gamma(Sign::Pos) = {1, 2, 3, ...}`

This mathematical framework ensures our approximation is *sound*.
If we say `x` is Positive, then the actual concrete value of `x` *must* be in the set `gamma(Positive)`.
```

== Abstract Semantics

How do we execute code with these abstract values?
We define *abstract transfer functions*.

For `x = y + z`:
- If `y` is (+) and `z` is (+), then `x` is (+).
- If `y` is (+) and `z` is (-), then `x` is ($top$) (unknown).

We can implement this in Rust for our Sign domain:

```rust
impl std::ops::Add for Sign {
    type Output = Sign;

    fn add(self, rhs: Sign) -> Sign {
        match (self, rhs) {
            (Sign::Pos, Sign::Pos) => Sign::Pos,
            (Sign::Neg, Sign::Neg) => Sign::Neg,
            (Sign::Pos, Sign::Neg) => Sign::Top, // Lost precision!
            (Sign::Zero, x) => x,
            (x, Sign::Zero) => x,
            _ => Sign::Top,
        }
    }
}
```

== The Challenge of Control Flow

Straight-line code is easy. Loops and branches are hard.

```rust
if x > 0 {
    y = 1;
} else {
    y = -1;
}
// At this point, what is y?
```

At the merge point, `y` could be 1 (Positive) OR -1 (Negative).
In the Sign domain, `(+) join (-) = top`.
We lost the information that `y` is non-zero!

This is where *BDDs* will come in.
Instead of merging everything into a single abstract value (and getting $top$), we can use BDDs to track *which path* leads to which value.

- Path 1 ($x > 0$): $y = +$
- Path 2 ($x \le 0$): $y = -$

This is called *Path Sensitivity*, and it is the main focus of this guide.

#chapter-summary(
  [
    *IMP is our toy language.*
    It has assignments, loops, and conditionals, represented by a Rust AST.
  ],
  [
    *Abstraction simplifies values.*
    We replace concrete integers with abstract properties like Signs or Intervals.
  ],
  [
    *The `AbstractDomain` trait defines the interface.*
    It requires `join` (union), `meet` (intersection), `top` (unknown), and `bottom` (impossible).
  ],
  [
    *Abstract execution loses precision.*
    Operations like `(+) + (-)` result in `Top` because the answer is ambiguous.
  ],
  [
    *Control flow merges paths.*
    Joining branches often leads to precision loss. BDDs will help us solve this by keeping paths separate.
  ],
)
