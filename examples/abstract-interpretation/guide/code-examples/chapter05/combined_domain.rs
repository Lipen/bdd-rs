//! Chapter 5: Combined Domain (Product Domain)
//!
//! This example demonstrates combining multiple abstract domains.
//! Product domain provides more precision through coordinated analysis.

use std::collections::HashMap;
use std::fmt;

// Reuse Sign domain from chapter01
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Sign {
    Bot,
    Neg,
    Zero,
    Pos,
    Top,
}

impl Sign {
    pub fn join(&self, other: &Self) -> Self {
        use Sign::*;
        match (self, other) {
            (Bot, x) | (x, Bot) => *x,
            (Top, _) | (_, Top) => Top,
            (x, y) if x == y => *x,
            (Neg, Zero) | (Zero, Neg) | (Neg, Pos) | (Pos, Neg) => Top,
            (Zero, Pos) | (Pos, Zero) => Pos,
            _ => Top,
        }
    }

    pub fn add(&self, other: &Self) -> Self {
        use Sign::*;
        match (self, other) {
            (Bot, _) | (_, Bot) => Bot,
            (Pos, Pos) => Pos,
            (Neg, Neg) => Neg,
            (Zero, x) | (x, Zero) => *x,
            _ => Top,
        }
    }
}

impl fmt::Display for Sign {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Sign::Bot => write!(f, "⊥"),
            Sign::Neg => write!(f, "−"),
            Sign::Zero => write!(f, "0"),
            Sign::Pos => write!(f, "+"),
            Sign::Top => write!(f, "⊤"),
        }
    }
}

// Parity domain
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Parity {
    Bot,
    Even,
    Odd,
    Top,
}

impl Parity {
    pub fn join(&self, other: &Self) -> Self {
        use Parity::*;
        match (self, other) {
            (Bot, x) | (x, Bot) => *x,
            (Top, _) | (_, Top) => Top,
            (x, y) if x == y => *x,
            _ => Top,
        }
    }

    pub fn add(&self, other: &Self) -> Self {
        use Parity::*;
        match (self, other) {
            (Bot, _) | (_, Bot) => Bot,
            (Even, Even) | (Odd, Odd) => Even,
            (Even, Odd) | (Odd, Even) => Odd,
            _ => Top,
        }
    }
}

impl fmt::Display for Parity {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Parity::Bot => write!(f, "⊥"),
            Parity::Even => write!(f, "even"),
            Parity::Odd => write!(f, "odd"),
            Parity::Top => write!(f, "⊤"),
        }
    }
}

/// Product domain: Sign × Parity
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SignParity {
    sign: Sign,
    parity: Parity,
}

impl SignParity {
    pub fn new(sign: Sign, parity: Parity) -> Self {
        Self { sign, parity }
    }

    pub fn bot() -> Self {
        Self {
            sign: Sign::Bot,
            parity: Parity::Bot,
        }
    }

    pub fn top() -> Self {
        Self {
            sign: Sign::Top,
            parity: Parity::Top,
        }
    }

    /// Reduced product: eliminate impossible combinations
    pub fn reduce(&self) -> Self {
        // Zero must be even
        let (sign, parity) = match (&self.sign, &self.parity) {
            (Sign::Zero, Parity::Odd) => (Sign::Bot, Parity::Bot), // Impossible
            (Sign::Zero, _) => (Sign::Zero, Parity::Even),         // Refine
            (s, p) => (*s, *p),
        };

        Self { sign, parity }
    }

    pub fn join(&self, other: &Self) -> Self {
        Self {
            sign: self.sign.join(&other.sign),
            parity: self.parity.join(&other.parity),
        }
        .reduce()
    }

    pub fn add(&self, other: &Self) -> Self {
        Self {
            sign: self.sign.add(&other.sign),
            parity: self.parity.add(&other.parity),
        }
        .reduce()
    }
}

impl fmt::Display for SignParity {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "({}, {})", self.sign, self.parity)
    }
}

/// Abstract state with product domain
#[derive(Debug, Clone)]
pub struct ProductState {
    env: HashMap<String, SignParity>,
}

impl ProductState {
    pub fn new() -> Self {
        Self { env: HashMap::new() }
    }

    pub fn set(&mut self, var: &str, value: SignParity) {
        self.env.insert(var.to_string(), value);
    }

    pub fn get(&self, var: &str) -> SignParity {
        self.env.get(var).cloned().unwrap_or_else(SignParity::top)
    }

    pub fn join(&self, other: &Self) -> Self {
        let mut result = Self::new();
        for (var, val1) in &self.env {
            let val2 = other.get(var);
            result.set(var, val1.join(&val2));
        }
        for (var, val2) in &other.env {
            if !self.env.contains_key(var) {
                result.set(var, val2.clone());
            }
        }
        result
    }
}

impl fmt::Display for ProductState {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{{")?;
        for (i, (var, val)) in self.env.iter().enumerate() {
            if i > 0 {
                write!(f, ", ")?;
            }
            write!(f, "{}: {}", var, val)?;
        }
        write!(f, "}}")
    }
}

fn main() {
    println!("=== Product Domain Example ===\n");

    // Example 1: Reduced product power
    println!("Example 1: Reduced Product Refinement");
    let val1 = SignParity::new(Sign::Zero, Parity::Odd);
    println!("  Before reduction: {}", val1);
    let val1_reduced = val1.reduce();
    println!("  After reduction: {}", val1_reduced);
    println!("  => Zero cannot be odd, refined to ⊥\n");

    let val2 = SignParity::new(Sign::Zero, Parity::Top);
    println!("  Before reduction: {}", val2);
    let val2_reduced = val2.reduce();
    println!("  After reduction: {}", val2_reduced);
    println!("  => Zero must be even, refined parity\n");

    // Example 2: Analysis with product domain
    println!("Example 2: Program Analysis");
    println!("  let x = 2;     // (+, even)");
    println!("  let y = 3;     // (+, odd)");
    println!("  let z = x + y; // (+, odd)\n");

    let mut state = ProductState::new();
    state.set("x", SignParity::new(Sign::Pos, Parity::Even));
    state.set("y", SignParity::new(Sign::Pos, Parity::Odd));

    let x = state.get("x");
    let y = state.get("y");
    let z = x.add(&y);
    state.set("z", z);

    println!("  State: {}\n", state);

    // Example 3: More precision than components alone
    println!("Example 3: Precision Advantage");
    println!("  With sign alone: 2 + 3 = (+)");
    println!("  With parity alone: 2 + 3 = (odd)");
    println!("  With product: 2 + 3 = (+, odd)");
    println!("  => More precise than either domain alone!\n");

    // Example 4: Loop analysis
    println!("Example 4: Loop with Product Domain");
    println!("  x = 0; while x < 10 {{ x = x + 2; }}\n");

    let mut state = ProductState::new();
    state.set("x", SignParity::new(Sign::Zero, Parity::Even));

    println!("  Iteration 0: {}", state);

    for i in 1..=3 {
        let x = state.get("x");
        let two = SignParity::new(Sign::Pos, Parity::Even);
        let next = x.add(&two);
        state.set("x", next);
        println!("  Iteration {}: {}", i, state);
    }

    println!("\n  After widening: x = (+, even)");
    println!("  => Both sign and parity preserved!\n");

    println!("=== Summary ===");
    println!("✓ Product domain combines multiple abstractions");
    println!("✓ Reduced product eliminates impossible combinations");
    println!("✓ More precise than components in isolation");
    println!("✓ Cost: quadratic in number of domains");
}
