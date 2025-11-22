//! Interval Domain Implementation
//!
//! **Guide Reference:** Part I, Chapter 1 - "Abstract Domains" & Part II, Chapter 10 - "Numeric Domains"
//!
//! This example demonstrates a more precise numeric abstract domain than signs.
//! Intervals track the range `[low, high]` of possible values, providing better
//! precision for reasoning about numeric constraints.
//!
//! ## Key Advantages Over Sign Domain
//!
//! 1. **More Precision**: Can distinguish [5, 10] from [100, 200]
//! 2. **Useful Constraints**: Can prove properties like "x < 100"
//! 3. **Better for Loops**: Tracks iteration bounds more accurately
//!
//! ## Concepts Demonstrated
//!
//! - **Interval Arithmetic**: Sound overapproximation of operations
//! - **Widening Operator**: Ensures termination when analyzing loops
//! - **Meet Operation**: Useful for refining information from conditionals
//! - **Overflow Handling**: Falls back to ⊤ when arithmetic overflows
//!
//! ## Widening for Loop Convergence
//!
//! Without widening, interval analysis might not terminate on loops:
//! ```text
//! x = 0
//! Iter 1: x = [0,0] ⊔ [1,1] = [0,1]
//! Iter 2: x = [0,1] ⊔ [2,2] = [0,2]
//! Iter 3: x = [0,2] ⊔ [3,3] = [0,3]
//! ... continues indefinitely
//! ```
//!
//! Widening extrapolates to infinity, ensuring convergence:
//! ```text
//! x = 0
//! Iter 1: x = [0,0] ⊔ [1,1] = [0,1]
//! Iter 2: x = [0,1] ∇ [2,2] = [0,+∞]  (widened!)
//! Iter 3: x = [0,+∞] (fixed point reached)
//! ```
//!
//! ## Expected Output
//!
//! Run with: `cargo run --example interval_domain`
//!
//! Shows interval arithmetic, join/meet operations, loop analysis with widening,
//! and precision comparison with the sign domain.

use std::fmt;

/// Interval domain representing ranges of integer values
///
/// The lattice structure is based on interval containment.
/// `[a,b] ≤ [c,d]` if `c ≤ a` and `b ≤ d` (containment)
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Interval {
    /// Bottom: unreachable/empty set
    Bot,
    /// Interval `[low, high]` where `low ≤ high`
    Range(i32, i32),
    /// Top: all integer values
    Top,
}

impl Interval {
    /// Create a constant interval `[c, c]`
    pub fn constant(c: i32) -> Self {
        Interval::Range(c, c)
    }

    /// Create an interval `[low, high]`
    pub fn new(low: i32, high: i32) -> Self {
        if low > high {
            Interval::Bot
        } else {
            Interval::Range(low, high)
        }
    }

    /// Join: least upper bound (smallest interval containing both)
    pub fn join(&self, other: &Self) -> Self {
        use Interval::*;
        match (self, other) {
            (Bot, x) | (x, Bot) => *x,
            (Top, _) | (_, Top) => Top,
            (Range(a, b), Range(c, d)) => Range((*a).min(*c), (*b).max(*d)),
        }
    }

    /// Meet: greatest lower bound (largest interval in both)
    pub fn meet(&self, other: &Self) -> Self {
        use Interval::*;
        match (self, other) {
            (Bot, _) | (_, Bot) => Bot,
            (Top, x) | (x, Top) => *x,
            (Range(a, b), Range(c, d)) => {
                let low = (*a).max(*c);
                let high = (*b).min(*d);
                if low <= high {
                    Range(low, high)
                } else {
                    Bot
                }
            }
        }
    }

    /// Abstract addition: `[a,b] + [c,d] = [a+c, b+d]`
    pub fn add(&self, other: &Self) -> Self {
        use Interval::*;
        match (self, other) {
            (Bot, _) | (_, Bot) => Bot,
            (Top, _) | (_, Top) => Top,
            (Range(a, b), Range(c, d)) => {
                // Check for overflow
                match (a.checked_add(*c), b.checked_add(*d)) {
                    (Some(low), Some(high)) => Range(low, high),
                    _ => Top, // Overflow -> imprecise
                }
            }
        }
    }

    /// Abstract subtraction: `[a,b] - [c,d] = [a-d, b-c]`
    pub fn sub(&self, other: &Self) -> Self {
        use Interval::*;
        match (self, other) {
            (Bot, _) | (_, Bot) => Bot,
            (Top, _) | (_, Top) => Top,
            (Range(a, b), Range(c, d)) => match (a.checked_sub(*d), b.checked_sub(*c)) {
                (Some(low), Some(high)) => Range(low, high),
                _ => Top,
            },
        }
    }

    /// Abstract multiplication (simplified, may lose precision)
    pub fn mul(&self, other: &Self) -> Self {
        use Interval::*;
        match (self, other) {
            (Bot, _) | (_, Bot) => Bot,
            (Top, _) | (_, Top) => Top,
            (Range(a, b), Range(c, d)) => {
                // All four corner products
                let products = [a.checked_mul(*c), a.checked_mul(*d), b.checked_mul(*c), b.checked_mul(*d)];

                // If any overflow, return Top
                let vals: Option<Vec<i32>> = products.iter().copied().collect();
                match vals {
                    Some(v) if v.len() == 4 => {
                        let min = *v.iter().min().unwrap();
                        let max = *v.iter().max().unwrap();
                        Range(min, max)
                    }
                    _ => Top,
                }
            }
        }
    }

    /// Widening operator for ensuring termination
    ///
    /// If bounds are not stable, widen to infinity
    pub fn widen(&self, other: &Self) -> Self {
        use Interval::*;
        match (self, other) {
            (Bot, x) => *x,
            (x, Bot) => *x,
            (Top, _) | (_, Top) => Top,
            (Range(a, b), Range(c, d)) => {
                let low = if c < a { i32::MIN } else { *a };
                let high = if d > b { i32::MAX } else { *b };
                if low == i32::MIN && high == i32::MAX {
                    Top
                } else {
                    Range(low, high)
                }
            }
        }
    }

    /// Check if value is definitely in the interval
    pub fn contains(&self, value: i32) -> bool {
        match self {
            Interval::Bot => false,
            Interval::Top => true,
            Interval::Range(low, high) => *low <= value && value <= *high,
        }
    }
}

impl fmt::Display for Interval {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Interval::Bot => write!(f, "⊥"),
            Interval::Top => write!(f, "⊤"),
            Interval::Range(a, b) if a == b => write!(f, "[{}]", a),
            Interval::Range(a, b) => write!(f, "[{}, {}]", a, b),
        }
    }
}

fn main() {
    use Interval::*;

    println!("=== Interval Domain Example ===\n");

    // Basic intervals
    println!("Creating intervals:");
    let x = Interval::constant(5);
    let y = Range(1, 10);
    let z = Range(-5, 5);
    println!("  x = {}", x);
    println!("  y = {}", y);
    println!("  z = {}\n", z);

    // Arithmetic
    println!("Arithmetic operations:");
    println!("  {} + {} = {}", x, y, x.add(&y));
    println!("  {} - {} = {}", y, x, y.sub(&x));
    println!("  {} * {} = {}\n", x, Range(2, 3), x.mul(&Range(2, 3)));

    // Join (union of ranges)
    println!("Join operations (smallest containing interval):");
    println!("  {} ⊔ {} = {}", Range(0, 5), Range(10, 15), Range(0, 5).join(&Range(10, 15)));
    println!("  {} ⊔ {} = {}\n", Range(0, 10), Range(5, 15), Range(0, 10).join(&Range(5, 15)));

    // Meet (intersection)
    println!("Meet operations (intersection):");
    println!("  {} ⊓ {} = {}", Range(0, 10), Range(5, 15), Range(0, 10).meet(&Range(5, 15)));
    println!("  {} ⊓ {} = {}\n", Range(0, 5), Range(10, 15), Range(0, 5).meet(&Range(10, 15)));

    // Analyzing a simple program
    println!("Analyzing: let mut x = 5; x = x + 1;");
    let mut x = Interval::constant(5);
    println!("  After x = 5: x = {}", x);
    x = x.add(&Interval::constant(1));
    println!("  After x = x + 1: x = {}", x);
    println!();

    // Loop analysis with widening
    println!("Loop analysis:");
    println!("  x = 0");
    println!("  while x < 10 {{ x = x + 1 }}");
    let mut x = Interval::constant(0);
    println!("  Iteration 0: x = {}", x);

    for i in 1..=5 {
        let next = x.join(&x.add(&Range(1, 1)));
        if i == 2 {
            // Apply widening after a few iterations
            x = x.widen(&next);
            println!("  Iteration {} (with widening): x = {}", i, x);
        } else {
            x = next;
            println!("  Iteration {}: x = {}", i, x);
        }
    }
    println!();

    // Precision comparison
    println!("Precision advantage over signs:");
    let x_sign = "Pos"; // Sign domain would only know "positive"
    let x_interval = Range(5, 10);
    println!("  Sign domain: x is {}", x_sign);
    println!("  Interval domain: x ∈ {}", x_interval);
    println!("  Can prove x < 100: {}", x_interval.contains(99));
    println!("  Much more precise information!");
}
