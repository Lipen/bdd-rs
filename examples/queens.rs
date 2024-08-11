use clap::Parser;

use bdd_rs::bdd::Bdd;
use bdd_rs::reference::Ref;

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
}

fn main() -> color_eyre::Result<()> {
    color_eyre::install()?;

    simplelog::TermLogger::init(
        simplelog::LevelFilter::Info,
        simplelog::Config::default(),
        simplelog::TerminalMode::Mixed,
        simplelog::ColorChoice::Auto,
    )?;

    let time_total = std::time::Instant::now();

    let args = Cli::parse();
    println!("args = {:?}", args);

    // Note:
    // - 20 bits (default) are enough to encode at most n=10 queens (time=0.4s).
    // - 23 bits are required for n=11 queens (time=15s).
    // - 25 bits are required for n=12 queens (time=720s).

    let bdd = Bdd::new(args.size);
    println!("bdd = {:?}", bdd);

    // Encode N-queens problem:
    // - N queens on an NxN board
    // - One queen per row
    // - One queen per column
    // - No two queens on the same diagonal
    let n = args.n;
    println!("Encoding n-queens problem with n = {}", n);

    let res = encode_queens_board(&bdd, n, args.gc);
    println!("res = {} of size {}", res, bdd.size(res));

    let num_solutions = bdd.sat_count(res, n * n);
    println!("solutions: {}", num_solutions);

    println!("bdd = {:?}", bdd);
    println!("cache hits: {}", bdd.cache().hits());
    println!("cache faults: {}", bdd.cache().faults());
    println!("cache misses: {}", bdd.cache().misses());

    let time_total = time_total.elapsed();
    println!("Done in {:.3} s", time_total.as_secs_f64());

    Ok(())
}

fn queen(n: usize, row: usize, col: usize) -> u32 {
    (row * n + col + 1) as u32
}

fn encode_queens_square(bdd: &Bdd, n: usize, i: usize, j: usize) -> Ref {
    // println!("Encoding square ({}, {})...", i, j);
    let mut node = bdd.one;

    for row in (0..n).rev() {
        for col in (0..n).rev() {
            let var = queen(n, row, col);

            assert!(bdd.is_terminal(node) || var < bdd.variable(node.index()));

            // Queen must be placed here
            if row == i && col == j {
                let low = bdd.zero;
                let high = node;
                node = bdd.mk_node(var, low, high);
                continue;
            }

            // Conflicting row, column, or diagonal with Queen placement
            let row_diff = (row as i32 - i as i32).abs();
            let col_diff = (col as i32 - j as i32).abs();

            if row == i || col == j || (row_diff == col_diff) {
                let low = node;
                let high = bdd.zero;
                node = bdd.mk_node(var, low, high);
                continue;
            }

            // No conflicts
            node = bdd.mk_node(var, node, node);
        }
    }

    node
}

fn encode_queens_row(bdd: &Bdd, n: usize, r: usize) -> Ref {
    // println!("Encoding row {}...", r);
    let mut node = bdd.zero;

    for c in 0..n {
        let square = encode_queens_square(bdd, n, r, c);
        // println!("Merging column {}...", c);
        node = bdd.apply_or(node, square);
    }

    node
}

fn encode_queens_board(bdd: &Bdd, n: usize, gc: bool) -> Ref {
    // println!("Encoding board of size n = {}...", n);
    let mut node = bdd.one;

    for r in 0..n {
        let row = encode_queens_row(bdd, n, r);
        println!(
            "Merging row {}... size for far = {}, solutions = {}",
            r,
            bdd.size(node),
            bdd.sat_count(node, n * n)
        );
        node = bdd.apply_and(node, row);

        if gc {
            // println!("bdd before GC = {:?}", bdd);
            bdd.collect_garbage(&[node]);
            // println!("bdd after GC = {:?}", bdd);
        }
    }

    node
}
