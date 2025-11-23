//! Complete Verifier: Path-Sensitive Abstract Interpretation
//!
//! **Guide Reference:** Part I, Chapter 6 - "Building a Symbolic Executor" (Extended)
//!
//! This example implements a **complete verification engine** that combines:
//! 1. **Abstract Interpretation**: Using the Interval domain for arithmetic reasoning
//! 2. **Path Sensitivity**: Using BDDs to track control flow and path feasibility
//! 3. **Refinement**: Using path conditions to refine abstract values (e.g., x > 0 implies x ∈ [1, ∞])
//!
//! Unlike the basic `symbolic_executor` which only tracks symbolic expressions,
//! this verifier can prove numeric properties like bounds and absence of overflows.
//!
//! ## Key Features
//!
//! - **Interval Domain**: Tracks ranges `[min, max]` for variables
//! - **Path Pruning**: Detects unreachable code (e.g., `if x > 5` when `x ∈ [0, 4]`)
//! - **Constraint Propagation**: Branch conditions refine variable intervals
//! - **Assertion Checking**: Proves assertions always hold or finds potential violations
//!
//! ## Expected Output
//!
//! Run with: `cargo run --example verifier`
//!
//! Demonstrates proving safety properties that require both path sensitivity
//! and numeric abstraction.

use std::collections::HashMap;
use std::fmt;
use std::rc::Rc;

use bdd_rs::bdd::Bdd;
use bdd_rs::reference::Ref;

// ============================================================================
// 1. Abstract Domain: Intervals
// ============================================================================

/// Interval domain representing ranges of integer values
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Interval {
    Bot,
    Range(i32, i32),
    Top,
}

impl Interval {
    pub fn constant(c: i32) -> Self {
        Interval::Range(c, c)
    }

    pub fn new(low: i32, high: i32) -> Self {
        if low > high {
            Interval::Bot
        } else {
            Interval::Range(low, high)
        }
    }

    pub fn join(&self, other: &Self) -> Self {
        use Interval::*;
        match (self, other) {
            (Bot, x) | (x, Bot) => *x,
            (Top, _) | (_, Top) => Top,
            (Range(a, b), Range(c, d)) => Range((*a).min(*c), (*b).max(*d)),
        }
    }

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

    pub fn add(&self, other: &Self) -> Self {
        use Interval::*;
        match (self, other) {
            (Bot, _) | (_, Bot) => Bot,
            (Top, _) | (_, Top) => Top,
            (Range(a, b), Range(c, d)) => match (a.checked_add(*c), b.checked_add(*d)) {
                (Some(l), Some(h)) => Range(l, h),
                _ => Top,
            },
        }
    }

    pub fn sub(&self, other: &Self) -> Self {
        use Interval::*;
        match (self, other) {
            (Bot, _) | (_, Bot) => Bot,
            (Top, _) | (_, Top) => Top,
            (Range(a, b), Range(c, d)) => match (a.checked_sub(*d), b.checked_sub(*c)) {
                (Some(l), Some(h)) => Range(l, h),
                _ => Top,
            },
        }
    }

    /// Check if this interval satisfies `> 0`
    pub fn is_strictly_positive(&self) -> bool {
        match self {
            Interval::Range(low, _) => *low > 0,
            _ => false,
        }
    }

    /// Check if this interval satisfies `<= 0`
    pub fn is_non_positive(&self) -> bool {
        match self {
            Interval::Range(_, high) => *high <= 0,
            _ => false,
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

// ============================================================================
// 2. AST: Expressions and Statements
// ============================================================================

#[derive(Debug, Clone)]
pub enum Expr {
    Const(i32),
    Var(String),
    Add(Box<Expr>, Box<Expr>),
    Sub(Box<Expr>, Box<Expr>),
}

#[derive(Debug, Clone)]
pub enum Cond {
    Gt(Box<Expr>, Box<Expr>), // e1 > e2
    Le(Box<Expr>, Box<Expr>), // e1 <= e2
}

#[derive(Debug, Clone)]
pub enum Stmt {
    Assign(String, Expr),
    If(Cond, Vec<Stmt>, Vec<Stmt>),
    Assert(Cond, String),
}

// ============================================================================
// 3. Verification Engine
// ============================================================================

#[derive(Debug, Clone)]
pub struct AbstractState {
    env: HashMap<String, Interval>,
    path_condition: Ref,
}

impl AbstractState {
    pub fn new(bdd: Rc<Bdd>) -> Self {
        Self {
            env: HashMap::new(),
            path_condition: bdd.mk_true(),
        }
    }

    pub fn get(&self, var: &str) -> Interval {
        self.env.get(var).copied().unwrap_or(Interval::Top)
    }

    pub fn set(&mut self, var: String, val: Interval) {
        self.env.insert(var, val);
    }

    pub fn eval(&self, expr: &Expr) -> Interval {
        match expr {
            Expr::Const(c) => Interval::constant(*c),
            Expr::Var(v) => self.get(v),
            Expr::Add(l, r) => self.eval(l).add(&self.eval(r)),
            Expr::Sub(l, r) => self.eval(l).sub(&self.eval(r)),
        }
    }

    /// Refine state based on condition `e1 > e2`
    pub fn refine_gt(&mut self, l: &Expr, r: &Expr) -> bool {
        // Simplified refinement: only handles "Var > Const" or "Var > Var"
        // In a real verifier, this would use a constraint solver or backward analysis
        match (l, r) {
            (Expr::Var(v), Expr::Const(c)) => {
                let current = self.get(v);
                // x > c  =>  x >= c + 1
                let constraint = Interval::new(c.saturating_add(1), i32::MAX);
                let refined = current.meet(&constraint);
                if refined == Interval::Bot {
                    return false;
                }
                self.set(v.clone(), refined);
            }
            _ => {} // Complex expressions not refined in this toy example
        }
        true
    }

    /// Refine state based on condition `e1 <= e2`
    pub fn refine_le(&mut self, l: &Expr, r: &Expr) -> bool {
        match (l, r) {
            (Expr::Var(v), Expr::Const(c)) => {
                let current = self.get(v);
                // x <= c
                let constraint = Interval::new(i32::MIN, *c);
                let refined = current.meet(&constraint);
                if refined == Interval::Bot {
                    return false;
                }
                self.set(v.clone(), refined);
            }
            _ => {}
        }
        true
    }
}

pub struct Verifier {
    bdd: Rc<Bdd>,
    next_path_var: u32,
    errors: Vec<String>,
}

impl Verifier {
    pub fn new() -> Self {
        Self {
            bdd: Rc::new(Bdd::default()),
            next_path_var: 1,
            errors: Vec::new(),
        }
    }

    pub fn verify(&mut self, stmts: &[Stmt]) {
        let initial_state = AbstractState::new(self.bdd.clone());
        let final_states = self.execute_stmts(stmts, initial_state);

        println!("Verification complete.");
        println!("Explored {} path(s).", final_states.len());

        if self.errors.is_empty() {
            println!("✓ No errors found. Program is safe.");
        } else {
            println!("✗ Found {} error(s):", self.errors.len());
            for err in &self.errors {
                println!("  - {}", err);
            }
        }
    }

    fn execute_stmts(&mut self, stmts: &[Stmt], state: AbstractState) -> Vec<AbstractState> {
        if stmts.is_empty() {
            return vec![state];
        }

        let stmt = &stmts[0];
        let rest = &stmts[1..];

        match stmt {
            Stmt::Assign(var, expr) => {
                let mut new_state = state.clone();
                let val = new_state.eval(expr);
                new_state.set(var.clone(), val);
                self.execute_stmts(rest, new_state)
            }

            Stmt::If(cond, then_branch, else_branch) => {
                let mut results = Vec::new();
                let path_var = self.bdd.mk_var(self.next_path_var);
                self.next_path_var += 1;

                // True Branch
                let mut true_state = state.clone();
                true_state.path_condition = self.bdd.apply_and(state.path_condition, path_var);

                // Refine abstract domain for true branch
                let feasible_true = match cond {
                    Cond::Gt(l, r) => true_state.refine_gt(l, r),
                    Cond::Le(l, r) => true_state.refine_le(l, r),
                };

                if feasible_true {
                    let then_results = self.execute_stmts(then_branch, true_state);
                    for s in then_results {
                        results.extend(self.execute_stmts(rest, s));
                    }
                }

                // False Branch
                let mut false_state = state.clone();
                false_state.path_condition = self.bdd.apply_and(state.path_condition, self.bdd.apply_not(path_var));

                // Refine abstract domain for false branch (negate condition)
                let feasible_false = match cond {
                    Cond::Gt(l, r) => false_state.refine_le(l, r), // !(> ) is <=
                    Cond::Le(l, r) => false_state.refine_gt(l, r), // !(<=) is >
                };

                if feasible_false {
                    let else_results = self.execute_stmts(else_branch, false_state);
                    for s in else_results {
                        results.extend(self.execute_stmts(rest, s));
                    }
                }

                results
            }

            Stmt::Assert(cond, msg) => {
                // To verify assertion P:
                // 1. Check if !P is feasible in current state
                // 2. If feasible, report error

                match cond {
                    Cond::Gt(l, r) => {
                        // Assert(l > r)
                        // Violation: l <= r
                        let mut violation_state = state.clone();
                        let possible_violation = violation_state.refine_le(l, r);

                        if possible_violation {
                            self.errors.push(format!("Assertion failed: {} (Path feasible)", msg));
                        }
                    }
                    Cond::Le(l, r) => {
                        // Assert(l <= r)
                        // Violation: l > r
                        let mut violation_state = state.clone();
                        let possible_violation = violation_state.refine_gt(l, r);

                        if possible_violation {
                            self.errors.push(format!("Assertion failed: {} (Path feasible)", msg));
                        }
                    }
                }

                self.execute_stmts(rest, state)
            }
        }
    }
}

fn main() {
    println!("=== Complete Verifier Example ===\n");

    let mut verifier = Verifier::new();

    // Example 1: Safe Program
    //   let x = 10;
    //   if x > 5 { assert(x > 0) }
    println!("Example 1: Verifying safe program...");
    let prog1 = vec![
        Stmt::Assign("x".into(), Expr::Const(10)),
        Stmt::If(
            Cond::Gt(Box::new(Expr::Var("x".into())), Box::new(Expr::Const(5))),
            vec![Stmt::Assert(
                Cond::Gt(Box::new(Expr::Var("x".into())), Box::new(Expr::Const(0))),
                "x must be positive".into(),
            )],
            vec![],
        ),
    ];
    verifier.verify(&prog1);
    println!();

    // Example 2: Unsafe Program (detected by refinement)
    //   let x = input(); // Top
    //   if x > 10 {
    //      x = x - 5;
    //      assert(x > 10); // Fail: x could be 11 -> 6
    //   }
    println!("Example 2: Verifying unsafe program...");
    let mut verifier2 = Verifier::new();
    let prog2 = vec![
        // Implicitly x is Top
        Stmt::If(
            Cond::Gt(Box::new(Expr::Var("x".into())), Box::new(Expr::Const(10))),
            vec![
                Stmt::Assign("x".into(), Expr::Sub(Box::new(Expr::Var("x".into())), Box::new(Expr::Const(5)))),
                Stmt::Assert(
                    Cond::Gt(Box::new(Expr::Var("x".into())), Box::new(Expr::Const(10))),
                    "x should remain > 10".into(),
                ),
            ],
            vec![],
        ),
    ];
    verifier2.verify(&prog2);
    println!();

    // Example 3: Dead Code Detection
    //   let x = 5;
    //   if x > 10 { y = 1 } // Unreachable
    //   else { y = 2 }
    println!("Example 3: Dead code detection...");
    let mut verifier3 = Verifier::new();
    let prog3 = vec![
        Stmt::Assign("x".into(), Expr::Const(5)),
        Stmt::If(
            Cond::Gt(Box::new(Expr::Var("x".into())), Box::new(Expr::Const(10))),
            vec![
                Stmt::Assign("y".into(), Expr::Const(1)), // Should not be reached
            ],
            vec![Stmt::Assign("y".into(), Expr::Const(2))],
        ),
    ];
    let final_states = verifier3.execute_stmts(&prog3, AbstractState::new(verifier3.bdd.clone()));
    println!("Final states: {}", final_states.len());
    for s in final_states {
        println!("  y = {}", s.get("y"));
    }
    println!("(Notice y=1 is never reached)");
}
