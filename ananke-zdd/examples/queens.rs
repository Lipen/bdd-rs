//! N-Queens problem using ZDDs.
//!
//! Represents all valid queen placements as a family of sets.
//! Each solution is a set of N positions (encoded as variables).
//!
//! **ZDD Approach**:
//! ZDDs efficiently represent families of sets. For N-Queens, each set represents
//! one valid solution (a collection of queen positions). We build the ZDD row-by-row,
//! using join operations to combine partial solutions and removing conflicting placements.
//!
//! **Performance**: Compiled with `--release` for optimal performance.
//!
//! **Usage**:
//! ```bash
//! cargo run --example queens -p ananke-zdd --release -- 8
//! cargo run --example queens -p ananke-zdd --release -- 4 --show
//! cargo run --example queens -p ananke-zdd --release -- 10 --all
//! ```

use std::time::Instant;

use ananke_zdd::reference::ZddId;
use ananke_zdd::types::Var;
use ananke_zdd::zdd::ZddManager;
use clap::Parser;

#[derive(Debug, Parser)]
#[command(name = "N-Queens ZDD Solver")]
#[command(about = "Solve N-Queens using Zero-Suppressed Decision Diagrams", long_about = None)]
struct Cli {
    /// Board size (number of queens and board dimension)
    #[arg(value_name = "N", default_value = "8")]
    n: usize,

    /// Display all solutions for the given N
    #[arg(short, long)]
    show: bool,

    /// Solve and display solutions for all N from 1 to the given value
    #[arg(long)]
    all: bool,
}

fn main() {
    let args = Cli::parse();

    if args.all {
        show_all_solutions(args.n);
    } else {
        show_single_solution(args.n, args.show);
    }
}

fn show_single_solution(n: usize, show_solutions: bool) {
    println!("=== N-Queens Problem (N={}) ===\n", n);

    let (solutions, nodes, time) = solve_queens(n);

    println!("Results:");
    println!("  Solutions: {}", solutions);
    println!("  ZDD Nodes: {}", nodes);
    println!("  Time:      {:.2}ms", time);
    println!();

    if show_solutions {
        let mgr = ZddManager::new();
        let result = build_queens_zdd(&mgr, n);

        println!("─── Solutions ───\n");
        for (i, sol) in mgr.iter_sets(result).enumerate() {
            let positions: Vec<(usize, usize)> = sol.iter().map(|v| var_to_pos(v.id(), n)).collect();
            println!("Solution {}:", i + 1);
            print_board(n, &positions);
            println!();
        }
    }
}

fn show_all_solutions(max_n: usize) {
    println!("=== N-Queens Solutions (N=1..{}) ===\n", max_n);

    // Known solution counts for verification
    let known = [1u64, 1, 0, 0, 2, 10, 4, 40, 92, 352, 724, 2680, 14200];

    println!("  N   Solutions   Expected   ZDD Nodes        Time");
    println!("───   ─────────   ────────   ─────────   ─────────");

    for n in 1..=max_n {
        let (solutions, nodes, time) = solve_queens(n);
        let expected = if n < known.len() { known[n] } else { 0 };
        let check = if n < known.len() && solutions == expected {
            "✓"
        } else if n >= known.len() {
            "?"
        } else {
            "✗"
        };
        println!(
            "{:>3}   {:>8}   {:>8} {}  {:>9} {:>9.1}ms",
            n, solutions, expected, check, nodes, time
        );
    }
}

/// Solve N-Queens and return (solution_count, zdd_nodes, time_ms)
fn solve_queens(n: usize) -> (u64, usize, f64) {
    let start = Instant::now();
    let mgr = ZddManager::new();

    let result = build_queens_zdd(&mgr, n);

    let count = mgr.count(result);
    let nodes = mgr.node_count(result);
    let time = start.elapsed().as_secs_f64() * 1000.0;

    (count, nodes, time)
}

/// Build ZDD representing all valid N-Queens placements.
///
/// **Constraint-based approach**: Build all valid boards by filtering constraints sequentially.
/// Unlike the incremental row-by-row approach, we first generate candidate boards
/// (with one queen per row), then filter by column and diagonal constraints.
fn build_queens_zdd(mgr: &ZddManager, n: usize) -> ZddId {
    if n == 0 {
        return mgr.one();
    }

    // Pre-allocate all variables
    for row in 0..n {
        for col in 0..n {
            mgr.ensure_var(Var::new(pos_to_var(row, col, n)));
        }
    }

    // Start with: all possible placements where each row has exactly one queen
    let mut result = board_with_one_queen_per_row(mgr, n);

    // Constraint 2: At most one queen per column
    result = at_most_one_per_column(mgr, n, result);

    // Constraint 3: At most one queen per diagonal
    result = at_most_one_per_diagonal(mgr, n, result);

    result
}

/// Generate all boards with exactly one queen in each row.
/// This is n^n possible placements (each row has n choices).
fn board_with_one_queen_per_row(mgr: &ZddManager, n: usize) -> ZddId {
    if n == 0 {
        return mgr.one();
    }

    // For row 0, any column is valid: {{col0}, {col1}, ...}
    let mut result = exactly_one_in_row(mgr, n, 0);

    // For each subsequent row, join with all single-column placements
    for row in 1..n {
        let row_choices = exactly_one_in_row(mgr, n, row);
        result = mgr.join(result, row_choices);
    }

    result
}

/// Create ZDD for "exactly one queen in this row" = {{(row,0)}, {(row,1)}, ...}
fn exactly_one_in_row(mgr: &ZddManager, n: usize, row: usize) -> ZddId {
    let mut result = ZddId::ZERO;
    for col in 0..n {
        let var = pos_to_var(row, col, n);
        let singleton = mgr.base(var);
        result = mgr.union(result, singleton);
    }
    result
}

/// Constraint: At most one queen per column.
/// For each column, remove all boards that have more than one queen.
fn at_most_one_per_column(mgr: &ZddManager, n: usize, mut result: ZddId) -> ZddId {
    for col in 0..n {
        let col_vars: Vec<Var> = (0..n).map(|row| Var::new(pos_to_var(row, col, n))).collect();
        result = keep_at_most_one_per_line(mgr, result, &col_vars);
    }
    result
}

/// Constraint: At most one queen per diagonal.
fn at_most_one_per_diagonal(mgr: &ZddManager, n: usize, mut result: ZddId) -> ZddId {
    // Main diagonals (\)
    for k in 0..(2 * n as i32) {
        let diag_vars: Vec<Var> = (0..n)
            .filter_map(|i| {
                let j = k - i as i32;
                if j >= 0 && (j as usize) < n {
                    Some(Var::new(pos_to_var(i, j as usize, n)))
                } else {
                    None
                }
            })
            .collect();
        if diag_vars.len() > 1 {
            result = keep_at_most_one_per_line(mgr, result, &diag_vars);
        }
    }

    // Anti-diagonals (/)
    for k in (-(n as i32))..n as i32 {
        let diag_vars: Vec<Var> = (0..n)
            .filter_map(|i| {
                let j = i as i32 + k;
                if j >= 0 && (j as usize) < n {
                    Some(Var::new(pos_to_var(i, j as usize, n)))
                } else {
                    None
                }
            })
            .collect();
        if diag_vars.len() > 1 {
            result = keep_at_most_one_per_line(mgr, result, &diag_vars);
        }
    }

    result
}

/// Keep only sets where at most one variable is present.
/// Remove sets with 2+ variables from the list.
fn keep_at_most_one_per_line(mgr: &ZddManager, family: ZddId, vars: &[Var]) -> ZddId {
    let mut result = family;
    // Remove all pairs of variables
    for i in 0..vars.len() {
        for j in (i + 1)..vars.len() {
            result = mgr.remove_sets_with_both(result, vars[i], vars[j]);
        }
    }
    result
}

fn pos_to_var(row: usize, col: usize, n: usize) -> u32 {
    (row * n + col + 1) as u32
}

fn var_to_pos(var: u32, n: usize) -> (usize, usize) {
    let idx = (var - 1) as usize;
    (idx / n, idx % n)
}

fn print_board(n: usize, positions: &[(usize, usize)]) {
    println!("  ┌{}┐", "─".repeat(2 * n + 1));
    for row in 0..n {
        print!("  │");
        for col in 0..n {
            if positions.iter().any(|&(r, c)| r == row && c == col) {
                print!(" ♛");
            } else {
                print!(" ·");
            }
        }
        println!(" │");
    }
    println!("  └{}┘", "─".repeat(2 * n + 1));
}
