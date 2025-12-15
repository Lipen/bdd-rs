//! N-Queens Puzzle with SDDs.
//!
//! Demonstrates encoding the N-Queens problem as an SDD:
//! - Place N queens on an N×N chessboard
//! - No two queens attack each other (row, column, diagonal)
//! - Count all solutions efficiently using model counting
//!
//! Run with: `cargo run --example queens`
//! With options: `cargo run --example queens -- -n 5`

use std::time::Instant;

use clap::Parser;
use num_bigint::BigUint;
use ananke_sdd::SddManager;

#[derive(Parser, Debug)]
#[command(name = "queens")]
#[command(about = "Solve N-Queens puzzle using SDDs")]
struct Args {
    /// Board size (NxN)
    #[arg(short, long, default_value_t = 4)]
    n: u32,

    /// Show all solutions
    #[arg(short, long)]
    show_all: bool,

    /// Maximum solutions to display
    #[arg(short, long, default_value_t = 10)]
    max_solutions: usize,
}

fn main() {
    let args = Args::parse();
    let n = args.n as usize;

    println!("─── N-Queens Puzzle with SDDs ───\n");
    println!("Board size: {}×{}", n, n);
    println!("Variables:  {} (one per cell: x[row][col])", n * n);
    println!();

    if n > 6 {
        println!("Warning: Large boards may take significant time and memory.\n");
    }

    // ────────────────────────────────────────────────────────────────────────
    // ENCODING
    // ────────────────────────────────────────────────────────────────────────

    println!("── Encoding ──\n");

    println!("Variables: x[r][c] = queen at row r, column c");
    println!("  x[r][c] = 1 means queen placed, 0 means empty\n");

    println!("Constraints:");
    println!("  1. Exactly one queen per row");
    println!("  2. At most one queen per column");
    println!("  3. At most one queen per diagonal (↘)");
    println!("  4. At most one queen per anti-diagonal (↙)");
    println!();

    // Create manager with n*n variables
    // Variable (r, c) is at index r*n + c + 1 (1-indexed)
    let mgr = SddManager::new((n * n) as u32);

    // Helper to get variable for cell (r, c)
    let var_at = |r: usize, c: usize| -> ananke_sdd::SddId {
        let idx = (r * n + c + 1) as i32;
        mgr.var(idx as u32)
    };

    // ────────────────────────────────────────────────────────────────────────
    // BUILD CONSTRAINTS
    // ────────────────────────────────────────────────────────────────────────

    println!("── Building Constraints ──\n");

    let build_start = Instant::now();
    let mut formula = mgr.true_sdd();
    let mut constraint_count = 0;

    // 1. Exactly one queen per row
    println!("  [1] Rows: generating...");
    let t1 = Instant::now();
    let mut row_constraint = mgr.true_sdd();
    for r in 0..n {
        // At least one: OR of all cells in row
        let at_least_one: Vec<_> = (0..n).map(|c| var_at(r, c)).collect();
        let row_or = mgr.or_all(at_least_one);
        row_constraint = mgr.and(row_constraint, row_or);
        constraint_count += 1;

        // At most one: for each pair, NOT both
        for c1 in 0..n {
            for c2 in (c1 + 1)..n {
                let not_both = mgr.neg(mgr.and(var_at(r, c1), var_at(r, c2)));
                row_constraint = mgr.and(row_constraint, not_both);
                constraint_count += 1;
            }
        }
    }
    let t1_gen = t1.elapsed();
    println!("       generated: {} nodes in {:.2?}", mgr.size(row_constraint), t1_gen);
    println!("       applying...");
    let t1_apply = Instant::now();
    formula = mgr.and(formula, row_constraint);
    println!("       done: {} nodes in {:.2?}", mgr.size(formula), t1_apply.elapsed());

    // 2. At most one queen per column
    println!("  [2] Columns: generating...");
    let t2 = Instant::now();
    let mut col_constraint = mgr.true_sdd();
    for c in 0..n {
        for r1 in 0..n {
            for r2 in (r1 + 1)..n {
                let not_both = mgr.neg(mgr.and(var_at(r1, c), var_at(r2, c)));
                col_constraint = mgr.and(col_constraint, not_both);
                constraint_count += 1;
            }
        }
    }
    let t2_gen = t2.elapsed();
    println!("       generated: {} nodes in {:.2?}", mgr.size(col_constraint), t2_gen);
    println!("       applying...");
    let t2_apply = Instant::now();
    formula = mgr.and(formula, col_constraint);
    println!("       done: {} nodes in {:.2?}", mgr.size(formula), t2_apply.elapsed());

    // 3. At most one queen per diagonal (↘)
    println!("  [3] Diagonals (↘): generating...");
    let t3 = Instant::now();
    let mut diag_constraint = mgr.true_sdd();
    for start in 0..(2 * n - 1) {
        let mut cells = vec![];
        for i in 0..n {
            let r = i;
            let c = start as i32 - i as i32;
            if c >= 0 && (c as usize) < n {
                cells.push((r, c as usize));
            }
        }
        for i in 0..cells.len() {
            for j in (i + 1)..cells.len() {
                let not_both = mgr.neg(mgr.and(var_at(cells[i].0, cells[i].1), var_at(cells[j].0, cells[j].1)));
                diag_constraint = mgr.and(diag_constraint, not_both);
                constraint_count += 1;
            }
        }
    }
    let t3_gen = t3.elapsed();
    println!("       generated: {} nodes in {:.2?}", mgr.size(diag_constraint), t3_gen);
    println!("       applying...");
    let t3_apply = Instant::now();
    formula = mgr.and(formula, diag_constraint);
    println!("       done: {} nodes in {:.2?}", mgr.size(formula), t3_apply.elapsed());

    // 4. At most one queen per anti-diagonal (↙)
    println!("  [4] Anti-diagonals (↙): generating...");
    let t4 = Instant::now();
    let mut anti_diag_constraint = mgr.true_sdd();
    for start in (1 - n as i32)..(n as i32) {
        let mut cells = vec![];
        for i in 0..n {
            let r = i;
            let c = (start + i as i32) as i32;
            if c >= 0 && (c as usize) < n {
                cells.push((r, c as usize));
            }
        }
        for i in 0..cells.len() {
            for j in (i + 1)..cells.len() {
                let not_both = mgr.neg(mgr.and(var_at(cells[i].0, cells[i].1), var_at(cells[j].0, cells[j].1)));
                anti_diag_constraint = mgr.and(anti_diag_constraint, not_both);
                constraint_count += 1;
            }
        }
    }
    let t4_gen = t4.elapsed();
    println!("       generated: {} nodes in {:.2?}", mgr.size(anti_diag_constraint), t4_gen);
    println!("       applying...");
    let t4_apply = Instant::now();
    formula = mgr.and(formula, anti_diag_constraint);
    println!("       done: {} nodes in {:.2?}", mgr.size(formula), t4_apply.elapsed());

    let build_time = build_start.elapsed();
    println!();
    println!("  Total constraints: {}", constraint_count);
    println!("  Final SDD size: {} nodes", mgr.size(formula));
    println!("  Build time: {:.2?}", build_time);
    println!();

    // ────────────────────────────────────────────────────────────────────────
    // COUNT SOLUTIONS
    // ────────────────────────────────────────────────────────────────────────

    println!("── Solutions ──\n");

    let count_start = Instant::now();
    let count = mgr.model_count(formula);
    let count_time = count_start.elapsed();
    println!("Number of solutions: {} (counted in {:.2?})", count, count_time);
    println!();

    // Known values for verification
    let known = [1, 1, 0, 0, 2, 10, 4, 40, 92, 352, 724, 2680];
    if n < known.len() {
        let expected = known[n];
        println!(
            "Expected for {}×{}: {} {}",
            n,
            n,
            expected,
            if count.to_string() == expected.to_string() { "✓" } else { "✗" }
        );
        println!();
    }

    // ────────────────────────────────────────────────────────────────────────
    // DISPLAY SOLUTIONS
    // ────────────────────────────────────────────────────────────────────────

    if args.show_all || n <= 4 {
        println!("── Solutions Display ──\n");

        let mut current = formula;
        let mut solution_num = 0;

        while mgr.is_satisfiable(current) && solution_num < args.max_solutions {
            if let Some(assignment) = mgr.any_sat(current) {
                solution_num += 1;
                println!("Solution {}:", solution_num);
                print_board(n, &assignment);

                // Block this solution
                let blocking = mgr.neg(mgr.cube(assignment));
                current = mgr.and(current, blocking);
            } else {
                break;
            }
        }

        let remaining: BigUint = count - BigUint::from(solution_num as u64);
        if remaining > BigUint::from(0u32) {
            println!("... and {} more solutions\n", remaining);
        }
    } else {
        println!("(Solutions not displayed. Use --show-all to display them.)\n");
    }

    // ────────────────────────────────────────────────────────────────────────
    // STATISTICS
    // ────────────────────────────────────────────────────────────────────────

    println!("── Statistics ──\n");

    let stats = mgr.stats();
    let hit_rate = if stats.apply_calls > 0 {
        100.0 * stats.cache_hits as f64 / stats.apply_calls as f64
    } else {
        0.0
    };

    println!("Metric              Value");
    println!("──────────────────  ──────────");
    println!("Board size          {}×{}", n, n);
    println!("Variables           {:>10}", n * n);
    println!("Constraints         {:>10}", constraint_count);
    println!("SDD nodes           {:>10}", stats.num_nodes);
    println!("Apply operations    {:>10}", stats.apply_calls);
    println!("Cache hit rate      {:>9.1}%", hit_rate);
    println!();

    // ────────────────────────────────────────────────────────────────────────
    // OBSERVATIONS
    // ────────────────────────────────────────────────────────────────────────

    println!("─── Observations ───\n");

    println!("N-Queens demonstrates SDD capabilities:");
    println!("  • Compiles complex constraints into compact form");
    println!("  • Counts all solutions in one traversal (O(|SDD|))");
    println!("  • Enumerates solutions by iterative blocking");
    println!();
    println!("Known solution counts:");
    println!("  1×1: 1    4×4: 2    7×7: 40");
    println!("  2×2: 0    5×5: 10   8×8: 92");
    println!("  3×3: 0    6×6: 4    ...");
    println!();

    println!("Done.");
}

/// Print a chessboard solution.
fn print_board(n: usize, assignment: &[i32]) {
    println!("  ┌{}┐", "─".repeat(2 * n + 1));
    for r in 0..n {
        print!("  │");
        for c in 0..n {
            let idx = r * n + c;
            if idx < assignment.len() && assignment[idx] > 0 {
                print!(" ♛");
            } else {
                print!(" ·");
            }
        }
        println!(" │");
    }
    println!("  └{}┘\n", "─".repeat(2 * n + 1));
}
