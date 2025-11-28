//! N-Queens Problem Solver.
//!
//! This example solves the classic N-Queens problem using Binary Decision Diagrams (BDDs).
//!
//! **Problem Statement**:
//! Place N queens on an `N × N` chessboard such that no two queens attack each other.
//!
//! **BDD Approach** (one-hot encoding):
//! 1. **Variables**: Each square `(i, j)` is a boolean variable `x_{i,j}`.
//! 2. **Constraints**:
//!    - At least one queen per row: `x_{i,0} ∨ x_{i,1} ∨ ... ∨ x_{i,n-1}`
//!    - At most one queen per row: `x_{i,j} → ¬x_{i,k}` for all `k ≠ j`
//!    - At most one queen per column: `x_{i,j} → ¬x_{k,j}` for all `k ≠ i`
//!    - At most one queen per diagonal: similar at-most-one constraints
//! 3. **Solution**: The BDD represents the set of all valid solutions.
//!
//! **Reference**:
//! Henrik R. Andersen, "An introduction to binary decision diagrams",
//! Lecture notes for "Efficient Algorithms and Programs", 1999,
//! The IT University of Copenhagen, Section 6.1
//!
//! **Usage**:
//! ```bash
//! cargo run --release --example queens -- 8
//! ```

use std::time::Instant;

use bdd_rs::bdd::Bdd;
use bdd_rs::reference::Ref;
use clap::Parser;

/// Statistics collected during constraint building.
#[derive(Debug, Default)]
struct Stats {
    /// BDD size after each constraint phase.
    sizes: Vec<(&'static str, u64)>,
    /// Time spent in each constraint phase (seconds).
    times: Vec<(&'static str, f64)>,
}

#[derive(Debug, Parser)]
#[command(author, version)]
struct Cli {
    /// Number of queens.
    #[arg(value_name = "INT", default_value = "8")]
    n: usize,

    /// BDD size (in bits, so the actual size is `2^size` nodes).
    #[clap(long, value_name = "INT", default_value = "20")]
    size: usize,

    /// Enable garbage collection.
    #[clap(long)]
    gc: bool,

    /// Enable verbose step-by-step output.
    #[clap(short, long)]
    verbose: bool,
}

fn main() -> color_eyre::Result<()> {
    color_eyre::install()?;

    simplelog::TermLogger::init(
        simplelog::LevelFilter::Info,
        simplelog::Config::default(),
        simplelog::TerminalMode::Mixed,
        simplelog::ColorChoice::Auto,
    )?;

    let time_total = Instant::now();

    let args = Cli::parse();
    println!("args = {:?}", args);

    let bdd = Bdd::new(args.size);
    let n = args.n;
    let num_vars = n * n;
    println!("Solving {}-Queens problem ({} variables)...", n, num_vars);

    // Pre-allocate variables in natural order
    for var_id in 1..=num_vars as u32 {
        bdd.mk_var(var_id);
    }

    let (res, stats) = solve_queens(&bdd, n, args.gc, args.verbose);

    // Print results
    println!();
    println!("=== Results ===");
    println!("Result Size: {} nodes", bdd.size(res));

    let num_solutions = bdd.sat_count(res, num_vars);
    println!("Number of solutions: {}", num_solutions);

    // Print timing breakdown
    println!();
    println!("=== Timing ===");
    for (phase, time) in &stats.times {
        println!("  {:30} {:>8.3}s", phase, time);
    }
    println!("  {:30} {:>8.3}s", "Total", time_total.elapsed().as_secs_f64());

    // Print size progression (subgraph sizes, not total allocated)
    println!();
    println!("=== Subgraph Size Progression ===");
    for (phase, size) in &stats.sizes {
        println!("  {:30} {:>10} nodes", phase, size);
    }

    // Print BDD storage stats
    println!();
    println!("=== BDD Storage ===");
    println!("  Allocated nodes: {} (total in storage, including garbage)", bdd.num_nodes());
    let cache = bdd.cache();
    let total_lookups = cache.hits() + cache.misses();
    let hit_rate = if total_lookups > 0 {
        100.0 * cache.hits() as f64 / total_lookups as f64
    } else {
        0.0
    };
    println!(
        "  Cache: {} hits, {} misses, {} faults ({:.1}% hit rate)",
        cache.hits(),
        cache.misses(),
        cache.faults(),
        hit_rate
    );

    Ok(())
}

/// Returns the variable ID for the cell at `(row, col)`.
/// Variables are 1-indexed: `x_{0,0} = 1`, `x_{0,1} = 2`, etc.
fn var(n: usize, row: usize, col: usize) -> u32 {
    (row * n + col + 1) as u32
}

/// Solves the N-Queens problem and returns the BDD representing all solutions.
fn solve_queens(bdd: &Bdd, n: usize, gc: bool, verbose: bool) -> (Ref, Stats) {
    let mut stats = Stats::default();
    let mut result = bdd.one;

    // Constraint 1: At least one queen per row
    println!("[1/5] At least one queen per row...");
    let t = Instant::now();
    let at_least_one = at_least_one_queen_per_row(bdd, n, verbose);
    result = bdd.apply_and(result, at_least_one);
    stats.times.push(("At least one per row", t.elapsed().as_secs_f64()));
    stats.sizes.push(("After at-least-one", bdd.size(result)));
    println!("       Done. Size: {} nodes, allocated: {}", bdd.size(result), bdd.num_nodes());

    // Constraint 2: At most one queen per row
    println!("[2/5] At most one queen per row...");
    let t = Instant::now();
    let row_amo = at_most_one_queen_per_line(bdd, n, true, gc, &mut result, verbose);
    result = bdd.apply_and(result, row_amo);
    stats.times.push(("At most one per row", t.elapsed().as_secs_f64()));
    stats.sizes.push(("After row AMO", bdd.size(result)));
    println!("       Done. Size: {} nodes, allocated: {}", bdd.size(result), bdd.num_nodes());

    // Constraint 3: At most one queen per column
    println!("[3/5] At most one queen per column...");
    let t = Instant::now();
    let col_amo = at_most_one_queen_per_line(bdd, n, false, gc, &mut result, verbose);
    result = bdd.apply_and(result, col_amo);
    stats.times.push(("At most one per column", t.elapsed().as_secs_f64()));
    stats.sizes.push(("After column AMO", bdd.size(result)));
    println!("       Done. Size: {} nodes, allocated: {}", bdd.size(result), bdd.num_nodes());

    // Constraint 4: At most one queen per anti-diagonal (/)
    println!("[4/5] At most one queen per anti-diagonal (/)...");
    let t = Instant::now();
    let slash = at_most_one_queen_per_diagonal(bdd, n, true, gc, &result, verbose);
    result = bdd.apply_and(result, slash);
    stats.times.push(("At most one per anti-diag", t.elapsed().as_secs_f64()));
    stats.sizes.push(("After anti-diagonal AMO", bdd.size(result)));
    println!("       Done. Size: {} nodes, allocated: {}", bdd.size(result), bdd.num_nodes());

    // Constraint 5: At most one queen per diagonal (\)
    println!("[5/5] At most one queen per diagonal (\\)...");
    let t = Instant::now();
    let backslash = at_most_one_queen_per_diagonal(bdd, n, false, gc, &result, verbose);
    result = bdd.apply_and(result, backslash);
    stats.times.push(("At most one per diagonal", t.elapsed().as_secs_f64()));
    stats.sizes.push(("After diagonal AMO", bdd.size(result)));
    println!("       Done. Size: {} nodes, allocated: {}", bdd.size(result), bdd.num_nodes());

    (result, stats)
}

/// At least one queen per row: `⋀_i (⋁_j x_{i,j})`
fn at_least_one_queen_per_row(bdd: &Bdd, n: usize, verbose: bool) -> Ref {
    let mut result = bdd.one;

    for row in 0..n {
        // Build disjunction: `x_{row,0} ∨ x_{row,1} ∨ ... ∨ x_{row,n-1}`
        let mut row_clause = bdd.zero;
        for col in 0..n {
            let x = bdd.mk_var(var(n, row, col));
            row_clause = bdd.apply_or(row_clause, x);
        }
        result = bdd.apply_and(result, row_clause);
        if verbose {
            println!("       Row {}/{}: size = {}", row + 1, n, bdd.size(result));
        }
    }

    result
}

/// At most one queen per row/column.
/// For each line: `⋀_{x ∈ line} (x → ¬(⋁_{y ∈ line, y≠x} y))`
fn at_most_one_queen_per_line(bdd: &Bdd, n: usize, is_row: bool, gc: bool, current: &Ref, verbose: bool) -> Ref {
    let mut result = bdd.one;
    let kind = if is_row { "Row" } else { "Col" };

    for i in 0..n {
        // Get all variables in this line
        let vars: Vec<u32> = (0..n).map(|j| if is_row { var(n, i, j) } else { var(n, j, i) }).collect();

        let amo = encode_at_most_one(bdd, &vars);
        result = bdd.apply_and(result, amo);

        if verbose {
            println!("       {} {}/{}: size = {}", kind, i + 1, n, bdd.size(result));
        }

        if gc {
            bdd.collect_garbage(&[result, *current]);
        }
    }

    result
}

/// At most one queen per diagonal.
/// `slash=true` for anti-diagonals (`/`), `slash=false` for diagonals (`\`).
fn at_most_one_queen_per_diagonal(bdd: &Bdd, n: usize, slash: bool, gc: bool, current: &Ref, verbose: bool) -> Ref {
    let mut result = bdd.one;

    let (a, b) = if slash { (-(n as i32), n as i32) } else { (0, 2 * n as i32) };
    let total_diags = (b - a) as usize;
    let mut diag_count = 0;

    for k in a..b {
        // Collect cells on this diagonal
        let cells: Vec<(usize, usize)> = (0..n)
            .filter_map(|i| {
                let j = if slash { (i as i32 + k) as usize } else { (k - i as i32) as usize };
                if j < n {
                    Some((i, j))
                } else {
                    None
                }
            })
            .collect();

        diag_count += 1;

        if cells.len() <= 1 {
            continue; // No constraint needed for single cell or empty diagonal
        }

        let vars: Vec<u32> = cells.iter().map(|&(i, j)| var(n, i, j)).collect();
        let amo = encode_at_most_one(bdd, &vars);
        result = bdd.apply_and(result, amo);

        if verbose {
            println!(
                "       Diag {}/{} (len {}): size = {}, nodes = {}",
                diag_count,
                total_diags,
                cells.len(),
                bdd.size(result),
                bdd.num_nodes(),
            );
        }

        if gc {
            bdd.collect_garbage(&[result, *current]);
        }
    }

    result
}

/// Encodes an at-most-one constraint: at most one variable can be true.
/// For each `x`: `x → ¬(⋁_{y≠x} y)`, which is equivalent to `¬x ∨ ¬(⋁_{y≠x} y)`.
fn encode_at_most_one(bdd: &Bdd, vars: &[u32]) -> Ref {
    if vars.len() <= 1 {
        return bdd.one;
    }

    let mut result = bdd.one;

    for (idx, &x_var) in vars.iter().enumerate() {
        let x = bdd.mk_var(x_var);

        // Build disjunction of all other variables
        let mut others = bdd.zero;
        for (other_idx, &y_var) in vars.iter().enumerate() {
            if other_idx != idx {
                let y = bdd.mk_var(y_var);
                others = bdd.apply_or(others, y);
            }
        }

        // x → ¬others, which is ¬x ∨ ¬others
        let implication = bdd.apply_or(-x, -others);
        result = bdd.apply_and(result, implication);
    }

    result
}
