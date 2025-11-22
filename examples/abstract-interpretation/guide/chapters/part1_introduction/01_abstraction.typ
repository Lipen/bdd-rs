// Chapter 1: The World of Abstract Interpretation

#import "../../theme.typ": *

= The Art of Approximation <ch-abstraction>

#reading-path(path: "essential") #h(0.5em) #reading-path(path: "beginner")

In the Prologue, we established that exact verification is impossible for general programs.
We must approximate.
But how do we approximate in a way that is useful?
How do we ensure we don't "approximate away" the bugs we are trying to find?

This chapter introduces the core concept of Abstract Interpretation:
*Sound Approximation*.

== The Geometric Analogy

Imagine a complex 3D object, such as a cylinder, floating in space.
Describing its exact position and shape requires precise coordinates for every point on its surface.
This is like the *concrete state* of a program: complex, detailed, and hard to manipulate.

Now, imagine shining a light on the object to cast a shadow on the wall.
- From the top, the shadow is a *circle*.
- From the side, the shadow is a *rectangle*.

#intuition-box[
  Neither shadow captures the full object.
  However, both shadows provide *sound constraints*.
  - If the circular shadow has a diameter of 10cm, we know for a fact that the object fits within a 10cm width.
  - If the rectangular shadow has a height of 20cm, we know the object is no taller than 20cm.
]

Abstract Interpretation is the art of choosing the right "projection" (abstraction) for the property we want to prove.
- If we want to prove the object fits through a round hole, we project it to a circle.
- If we want to prove a variable never exceeds 100, we project it to an *Interval*.
- If we want to prove a pointer is never null, we project it to a *Nullability* state.

== Interactive Reasoning

Before we write code, let's build intuition by playing a game.
I have two hidden integers, $x$ and $y$.
I won't tell you their values, but I will tell you their *properties*.

*Round 1:*
- Fact: $x$ is a positive integer ($x > 0$).
- Fact: $y$ is a positive integer ($y > 0$).
- Question: What is the sign of $x + y$?

*Answer:* Positive.
Reasoning: The sum of two positive numbers is always positive.
We didn't need to know the values to know the result.

*Round 2:*
- Fact: $x$ is positive.
- Fact: $y$ is positive.
- Question: What is the sign of $x - y$?

*Answer:* Unknown.
Reasoning:
- If $x = 5, y = 2$, then $x - y = 3$ (Positive).
- If $x = 2, y = 5$, then $x - y = -3$ (Negative).
- If $x = 5, y = 5$, then $x - y = 0$ (Zero).

Because the result depends on the *concrete values* which we have abstracted away, we cannot give a precise answer.
In Abstract Interpretation, we call this state *Top* ($top$) --- representing "Any value is possible."

*Round 3:*
- Fact: $x$ is positive.
- Fact: $y$ is negative.
- Question: What is the sign of $x * y$?

*Answer:* Negative.
Reasoning: A positive times a negative is always negative.

This game demonstrates the core mechanism:
We replace *concrete operations* (arithmetic on numbers) with *abstract operations* (arithmetic on properties).

== The IMP Language

To make this concrete, we will build a *MiniVerifier* throughout this guide.
We will analyze a simple toy language called *IMP* (Imperative Language).

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

== The Sign Domain

Let's formalize our "Positive/Negative" game.
We define a set of abstract values $D$:
$ D = {bot, -, 0, +, top} $

- $bot$ (Bottom): Impossible / Unreachable.
- $-$: Strictly negative integers.
- $0$: The integer zero.
- $+$: Strictly positive integers.
- $top$ (Top): Unknown / Any integer.

We can implement this in Rust:

#example-reference(
  "domains",
  "sign.rs",
  "sign_domain",
  [
    Complete implementation of the sign domain with lattice operations, abstract arithmetic, and path merging demonstrations.
    Shows how abstraction trades precision for tractability.
  ],
)

=== Abstract Semantics

We define *abstract transfer functions* to execute code in this domain.
For addition (`+`):

```rust
impl std::ops::Add for Sign {
    type Output = Sign;

    fn add(self, rhs: Sign) -> Sign {
        match (self, rhs) {
            // Precise cases
            (Sign::Pos, Sign::Pos) => Sign::Pos,
            (Sign::Neg, Sign::Neg) => Sign::Neg,
            (Sign::Zero, x) => x,
            (x, Sign::Zero) => x,

            // Imprecise cases (Loss of information)
            (Sign::Pos, Sign::Neg) => Sign::Top,
            (Sign::Neg, Sign::Pos) => Sign::Top,

            // Propagation of uncertainty
            (Sign::Top, _) => Sign::Top,
            (_, Sign::Top) => Sign::Top,

            // Propagation of impossibility
            (Sign::Bot, _) => Sign::Bot,
            (_, Sign::Bot) => Sign::Bot,
        }
    }
}
```

#info-box(title: "More Precise Domains")[
  Signs are simple but imprecise.
  For more precision, we can use *intervals* like `[0, 10]` to track numeric bounds.
  See #inline-example("domains", "interval.rs", "interval_domain") for interval arithmetic, widening operators, and loop analysis.
]

== The Challenge of Control Flow

Straight-line code is easy.
Loops and branches are hard.

```rust
if x > 0 {
    y = 1;
} else {
    y = -1;
}
// At this point, what is y?
```

At the merge point, `y` could be 1 (Positive) OR -1 (Negative).
In the Sign domain, we must find a single value that covers *both* possibilities.
The smallest value covering both $+$ and $-$ is $top$.

We lost the information that `y` is non-zero!
We know `y` is either 1 or -1, but our abstraction forces us to say "It could be anything."

This is where *BDDs* will come in.
Instead of merging everything into a single abstract value (and getting $top$), we can use BDDs to track *which path* leads to which value.

- Path 1 ($x > 0$): $y = +$
- Path 2 ($x <= 0$): $y = -$

This is called *Path Sensitivity*, and it is the main focus of this guide.

#chapter-summary[
  - *Abstraction is Projection.*
    Like a shadow of a 3D object, an abstract domain captures some properties while ignoring others.

  - *Soundness is Key.*
    If the abstraction says "Safe", the concrete program must be safe.
    If the abstraction says "Unknown", the program might be safe or unsafe.

  - *Precision vs. Speed.*
    More complex domains (Intervals vs. Signs) give better answers but cost more to compute.

  - *The Merge Problem.*
    Control flow merges force us to combine conflicting information, often leading to precision loss ($top$).
]
