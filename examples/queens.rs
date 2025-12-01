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

use bdd_rs::bdd::{Bdd, BddConfig};
use bdd_rs::reference::Ref;
use clap::Parser;

/// Tracker for step-by-step statistics with concise output.
struct StepTracker<'a> {
    bdd: &'a Bdd,
    verbose: bool,
    // Snapshot of cache stats at start of tracking
    prev_hits: usize,
    prev_misses: usize,
    prev_nodes: usize,
    step_start: Instant,
}

impl<'a> StepTracker<'a> {
    fn new(bdd: &'a Bdd, verbose: bool) -> Self {
        let cache = bdd.cache();
        Self {
            bdd,
            verbose,
            prev_hits: cache.hits(),
            prev_misses: cache.misses(),
            prev_nodes: bdd.num_nodes(),
            step_start: Instant::now(),
        }
    }

    /// Print table header for verbose output.
    fn print_header(&self) {
        if !self.verbose {
            return;
        }
        println!(
            "  {:<12} {:<9} {:<9} {:<9} {:>8}  {}",
            "step", "constr", "result", "Δnodes", "time", "cache hits/misses"
        );
        println!("  {}", "-".repeat(70));
    }

    /// Print a micro-step line (only in verbose mode).
    fn micro_step(&mut self, label: &str, constraint_size: u64, result_size: u64) {
        if !self.verbose {
            return;
        }
        let cache = self.bdd.cache();
        let hits = cache.hits();
        let misses = cache.misses();
        let nodes = self.bdd.num_nodes();

        let delta_hits = hits - self.prev_hits;
        let delta_misses = misses - self.prev_misses;
        let delta_nodes = nodes - self.prev_nodes;
        let delta_total = delta_hits + delta_misses;
        let hit_rate = if delta_total > 0 {
            100.0 * delta_hits as f64 / delta_total as f64
        } else {
            0.0
        };
        let elapsed_ms = self.step_start.elapsed().as_secs_f64() * 1000.0;

        // Format time adaptively
        let time_str = if elapsed_ms < 1000.0 {
            format!("{:>6.0}ms", elapsed_ms)
        } else {
            format!("{:>6.0}s ", elapsed_ms / 1000.0)
        };

        println!(
            "  {:<12} {:>9} {:>9} {:>9} {:>8}  {}/{}({:.0}%)",
            label,
            fmt_num(constraint_size),
            fmt_num(result_size),
            fmt_num(delta_nodes as u64),
            time_str,
            fmt_num(delta_hits as u64),
            fmt_num(delta_misses as u64),
            hit_rate
        );

        // Update snapshots for next step
        self.prev_hits = hits;
        self.prev_misses = misses;
        self.prev_nodes = nodes;
        self.step_start = Instant::now();
    }

    /// Print phase summary line.
    fn phase_done(&self, phase: &str, result_size: u64, phase_time: f64) {
        let cache = self.bdd.cache();
        let total = cache.hits() + cache.misses();
        let hit_rate = if total > 0 {
            100.0 * cache.hits() as f64 / total as f64
        } else {
            0.0
        };
        println!(
            "{} => size={} storage={} {:.3}s (cache {:.1}%)",
            phase,
            fmt_num(result_size),
            fmt_num(self.bdd.num_nodes() as u64),
            phase_time,
            hit_rate
        );
    }

    /// Reset step timer (for micro-step tracking within a phase).
    fn reset_step(&mut self) {
        let cache = self.bdd.cache();
        self.prev_hits = cache.hits();
        self.prev_misses = cache.misses();
        self.prev_nodes = self.bdd.num_nodes();
        self.step_start = Instant::now();
    }
}

/// Format a number with thousand separators for readability.
fn fmt_num(n: u64) -> String {
    if n < 1000 {
        n.to_string()
    } else if n < 1_000_000 {
        format!("{}K", n / 1000)
    } else {
        format!("{:.1}M", n as f64 / 1_000_000.0)
    }
}

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
    #[clap(long, value_name = "INT")]
    size: Option<usize>,

    /// Cache size in bits (size = 2^bits entries).
    #[clap(long, value_name = "INT")]
    cache_bits: Option<usize>,

    /// Enable garbage collection.
    #[clap(long)]
    gc: bool,

    /// Enable verbose step-by-step output.
    #[clap(short, long)]
    verbose: bool,

    /// Use incremental row-wise solver instead of constraint-based solver.
    #[clap(long)]
    incremental: bool,
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

    let mut config = BddConfig::default();
    if let Some(size) = args.size {
        config = config.with_initial_nodes(1 << size);
    }
    if let Some(cache_bits) = args.cache_bits {
        config = config.with_cache_bits(cache_bits);
    }
    let bdd = Bdd::with_config(config);

    let n = args.n;
    let num_vars = n * n;
    println!("Solving {}-Queens problem ({} variables)...", n, num_vars);

    // Pre-allocate variables in natural order
    for var_id in 1..=num_vars as u32 {
        bdd.mk_var(var_id);
    }
    assert!(bdd.var_order().len() == num_vars);

    if args.verbose {
        println!(
            "Var order: {}",
            bdd.var_order().iter().map(|v| v.to_string()).collect::<Vec<_>>().join(", ")
        );
    }

    let (res, stats) = if args.incremental {
        solve_queens_incremental(&bdd, n, args.gc, args.verbose)
    } else {
        solve_queens(&bdd, n, args.gc, args.verbose)
    };

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
    let mut result = bdd.one();
    let mut tracker = StepTracker::new(bdd, verbose);
    tracker.print_header();

    // Constraint 1: At least one queen per row
    println!("[1/5] At-least-one per row");
    let t = Instant::now();
    tracker.reset_step();
    let at_least_one = at_least_one_queen_per_row(bdd, n, &mut tracker);
    result = bdd.apply_and(result, at_least_one);
    let elapsed = t.elapsed().as_secs_f64();
    stats.times.push(("At least one per row", elapsed));
    stats.sizes.push(("After at-least-one", bdd.size(result)));
    tracker.phase_done("[1/5] At-least-one/row", bdd.size(result), elapsed);

    // Constraint 2: At most one queen per row
    println!("[2/5] At-most-one per row");
    let t = Instant::now();
    tracker.reset_step();
    let row_amo = at_most_one_queen_per_line(bdd, n, true, gc, &mut result, &mut tracker);
    result = bdd.apply_and(result, row_amo);
    let elapsed = t.elapsed().as_secs_f64();
    stats.times.push(("At most one per row", elapsed));
    stats.sizes.push(("After row AMO", bdd.size(result)));
    tracker.phase_done("[2/5] At-most-one/row", bdd.size(result), elapsed);

    // Constraint 3: At most one queen per column
    println!("[3/5] At-most-one per column");
    let t = Instant::now();
    tracker.reset_step();
    let col_amo = at_most_one_queen_per_line(bdd, n, false, gc, &mut result, &mut tracker);
    result = bdd.apply_and(result, col_amo);
    let elapsed = t.elapsed().as_secs_f64();
    stats.times.push(("At most one per column", elapsed));
    stats.sizes.push(("After column AMO", bdd.size(result)));
    tracker.phase_done("[3/5] At-most-one/col", bdd.size(result), elapsed);

    // Constraint 4: At most one queen per anti-diagonal (/)
    println!("[4/5] At-most-one per anti-diagonal (/)");
    let t = Instant::now();
    tracker.reset_step();
    let slash = at_most_one_queen_per_diagonal(bdd, n, true, gc, &result, &mut tracker);
    result = bdd.apply_and(result, slash);
    let elapsed = t.elapsed().as_secs_f64();
    stats.times.push(("At most one per anti-diag", elapsed));
    stats.sizes.push(("After anti-diagonal AMO", bdd.size(result)));
    tracker.phase_done("[4/5] At-most-one/anti-diag", bdd.size(result), elapsed);

    // Constraint 5: At most one queen per diagonal (\)
    println!("[5/5] At-most-one per diagonal (\\)");
    let t = Instant::now();
    tracker.reset_step();
    let backslash = at_most_one_queen_per_diagonal(bdd, n, false, gc, &result, &mut tracker);
    result = bdd.apply_and(result, backslash);
    let elapsed = t.elapsed().as_secs_f64();
    stats.times.push(("At most one per diagonal", elapsed));
    stats.sizes.push(("After diagonal AMO", bdd.size(result)));
    tracker.phase_done("[5/5] At-most-one/diag", bdd.size(result), elapsed);

    (result, stats)
}

/// At least one queen per row: `⋀_i (⋁_j x_{i,j})`
fn at_least_one_queen_per_row(bdd: &Bdd, n: usize, tracker: &mut StepTracker) -> Ref {
    let mut result = bdd.one();

    for row in 0..n {
        // Build disjunction: `x_{row,0} ∨ x_{row,1} ∨ ... ∨ x_{row,n-1}`
        let mut row_clause = bdd.zero();
        for col in 0..n {
            let x = bdd.mk_var(var(n, row, col));
            row_clause = bdd.apply_or(row_clause, x);
        }
        let clause_size = bdd.size(row_clause);
        result = bdd.apply_and(result, row_clause);
        tracker.micro_step(&format!("row {}/{}", row + 1, n), clause_size, bdd.size(result));
    }

    result
}

/// At most one queen per row/column.
/// For each line: `⋀_{x ∈ line} (x → ¬(⋁_{y ∈ line, y≠x} y))`
fn at_most_one_queen_per_line(bdd: &Bdd, n: usize, is_row: bool, gc: bool, current: &Ref, tracker: &mut StepTracker) -> Ref {
    let mut result = bdd.one();
    let kind = if is_row { "row" } else { "col" };

    for i in 0..n {
        // Get all variables in this line
        let vars: Vec<u32> = (0..n).map(|j| if is_row { var(n, i, j) } else { var(n, j, i) }).collect();

        let amo = encode_at_most_one(bdd, &vars);
        let amo_size = bdd.size(amo);
        result = bdd.apply_and(result, amo);
        tracker.micro_step(&format!("{} {}/{}", kind, i + 1, n), amo_size, bdd.size(result));

        if gc {
            bdd.collect_garbage(&[result, *current]);
        }
    }

    result
}

/// At most one queen per diagonal.
/// `slash=true` for anti-diagonals (`/`), `slash=false` for diagonals (`\`).
fn at_most_one_queen_per_diagonal(bdd: &Bdd, n: usize, slash: bool, gc: bool, current: &Ref, tracker: &mut StepTracker) -> Ref {
    let mut result = bdd.one();
    let kind = if slash { "/" } else { "\\" };

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
        let amo_size = bdd.size(amo);
        result = bdd.apply_and(result, amo);
        tracker.micro_step(&format!("{}d {}/{}", kind, diag_count, total_diags), amo_size, bdd.size(result));

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
        return bdd.one();
    }

    let mut result = bdd.one();

    for (idx, &x_var) in vars.iter().enumerate() {
        let x = bdd.mk_var(x_var);

        // Build disjunction of all other variables
        let mut others = bdd.zero();
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

// ============================================================================
// Alternative: Incremental row-wise construction
// ============================================================================

/// Incremental row-wise construction of N-Queens BDD.
/// Builds constraints row by row, only considering conflicts with upper rows.
fn solve_queens_incremental(bdd: &Bdd, n: usize, _gc: bool, verbose: bool) -> (Ref, Stats) {
    let mut stats = Stats::default();
    let mut tracker = StepTracker::new(bdd, verbose);
    tracker.print_header();

    let mut solution_bdd = bdd.one();

    // Process each row incrementally
    for row in 0..n {
        println!("[Row {}/{}]", row + 1, n);
        let t = Instant::now();
        tracker.reset_step();

        // Step 1: Exactly one queen in this row
        let row_exact = exactly_one_in_row(bdd, n, row);
        solution_bdd = bdd.apply_and(solution_bdd, row_exact);
        tracker.micro_step("exact-one", bdd.size(row_exact), bdd.size(solution_bdd));

        // Step 2: Conflicts with previous rows (column + diagonal)
        if row > 0 {
            for prev_row in 0..row {
                // Column conflicts
                let col_conflicts = column_conflicts_with_previous(bdd, n, row, prev_row);
                solution_bdd = bdd.apply_and(solution_bdd, col_conflicts);

                // Diagonal conflicts
                let diag_conflicts = diagonal_conflicts_with_previous(bdd, n, row, prev_row);
                solution_bdd = bdd.apply_and(solution_bdd, diag_conflicts);
            }
            tracker.micro_step("conflicts", 0, bdd.size(solution_bdd));
        }

        let elapsed = t.elapsed().as_secs_f64();
        stats.times.push(("Row processing", elapsed));
        stats.sizes.push(("After row", bdd.size(solution_bdd)));
        tracker.phase_done(&format!("[Row {}/{}]", row + 1, n), bdd.size(solution_bdd), elapsed);

        // Early exit if no solutions exist
        if solution_bdd == bdd.zero() {
            println!("No solutions possible, stopping early.");
            break;
        }
    }

    (solution_bdd, stats)
}

/// Exactly one queen in a specific row (at least one AND at most one)
fn exactly_one_in_row(bdd: &Bdd, n: usize, row: usize) -> Ref {
    let at_least = at_least_one_in_row(bdd, n, row);
    let at_most = at_most_one_in_row(bdd, n, row);
    bdd.apply_and(at_least, at_most)
}

/// At least one queen in a specific row
fn at_least_one_in_row(bdd: &Bdd, n: usize, row: usize) -> Ref {
    let mut result = bdd.zero();
    for col in 0..n {
        let v = bdd.mk_var(var(n, row, col));
        result = bdd.apply_or(result, v);
    }
    result
}

/// At most one queen in a specific row (pairwise encoding)
fn at_most_one_in_row(bdd: &Bdd, n: usize, row: usize) -> Ref {
    let mut result = bdd.one();
    for col1 in 0..n {
        for col2 in (col1 + 1)..n {
            let var1 = bdd.mk_var(var(n, row, col1));
            let var2 = bdd.mk_var(var(n, row, col2));
            // ¬(var1 ∧ var2) = ¬var1 ∨ ¬var2
            let constraint = bdd.apply_or(-var1, -var2);
            result = bdd.apply_and(result, constraint);
        }
    }
    result
}

/// Constraints between current row and previous row to avoid column conflicts
fn column_conflicts_with_previous(bdd: &Bdd, n: usize, current_row: usize, prev_row: usize) -> Ref {
    let mut result = bdd.one();
    for col in 0..n {
        let current_var = bdd.mk_var(var(n, current_row, col));
        let prev_var = bdd.mk_var(var(n, prev_row, col));
        // ¬(current ∧ prev) = ¬current ∨ ¬prev
        let constraint = bdd.apply_or(-current_var, -prev_var);
        result = bdd.apply_and(result, constraint);
    }
    result
}

/// Constraints between current row and previous row to avoid diagonal conflicts
fn diagonal_conflicts_with_previous(bdd: &Bdd, n: usize, current_row: usize, prev_row: usize) -> Ref {
    let mut result = bdd.one();
    let row_diff = current_row as i32 - prev_row as i32;

    for prev_col in 0..n {
        // Main diagonal: col difference equals row difference
        let diag1_col = prev_col as i32 + row_diff;
        if diag1_col >= 0 && diag1_col < n as i32 {
            let current_var = bdd.mk_var(var(n, current_row, diag1_col as usize));
            let prev_var = bdd.mk_var(var(n, prev_row, prev_col));
            let constraint = bdd.apply_or(-current_var, -prev_var);
            result = bdd.apply_and(result, constraint);
        }

        // Anti-diagonal: col difference equals negative row difference
        let diag2_col = prev_col as i32 - row_diff;
        if diag2_col >= 0 && diag2_col < n as i32 {
            let current_var = bdd.mk_var(var(n, current_row, diag2_col as usize));
            let prev_var = bdd.mk_var(var(n, prev_row, prev_col));
            let constraint = bdd.apply_or(-current_var, -prev_var);
            result = bdd.apply_and(result, constraint);
        }
    }
    result
}
