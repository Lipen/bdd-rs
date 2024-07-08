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
    // - 20 bits (default) are enough to encode at most n=8 queens (time=0.1s).
    // - 22 bits are required for n=9 queens (time=4s).
    // - 24 bits are required (size=7590122) for n=10 queens (time=100s).

    let bdd = Bdd::new(args.size);
    println!("bdd = {:?}", bdd);

    // Encode N-queens problem:
    // - N queens on an NxN board
    // - One queen per row
    // - One queen per column
    // - No two queens on the same diagonal
    let n = args.n;
    println!("Encoding n-queens problem with n = {}", n);
    let mut queens = vec![];
    for i in 0..n {
        let mut row = vec![];
        for j in 0..n {
            row.push(bdd.mk_var((i * n + j + 1) as u32));
        }
        queens.push(row);
    }

    let mut constraints: Vec<Ref> = vec![];

    // One queen per row
    for i in 0..n {
        let mut row = bdd.zero;
        for j in 0..n {
            row = bdd.apply_or(row, queens[i][j]);
        }
        constraints.push(row);
    }

    // One queen per column
    for j in 0..n {
        let mut col = bdd.zero;
        for i in 0..n {
            col = bdd.apply_or(col, queens[i][j]);
        }
        constraints.push(col);
    }

    // No two queens on the same diagonal
    for i in 0..n as i32 {
        for j in 0..n as i32 {
            for k in 0..n as i32 {
                for l in 0..n as i32 {
                    if i != k && j != l && i + j != k + l && i - j != k - l {
                        let i = i as usize;
                        let j = j as usize;
                        let k = k as usize;
                        let l = l as usize;
                        let not_diag = bdd.apply_not(bdd.apply_and(queens[i][j], queens[k][l]));
                        constraints.push(not_diag);
                    }
                }
            }
        }
    }

    println!(
        "Total {} constraints of total size {}",
        constraints.len(),
        bdd.descendants(constraints.iter().copied()).len()
    );
    // for &f in &constraints {
    //     println!("constraint of size {} = {}", bdd.size(f), bdd.to_bracket_string(f));
    // }

    println!("bdd = {:?}", bdd);
    if args.gc {
        println!("GC...");
        bdd.collect_garbage(&constraints);
        println!("bdd = {:?}", bdd);
    }

    println!("Merging constraints...");
    let res = bdd.apply_and_many(constraints.iter().copied());
    println!("bdd = {:?}", bdd);
    println!("res of size {} = {}", bdd.size(res), bdd.to_bracket_string(res));

    println!("cache hits: {}", bdd.cache().hits());
    println!("cache faults: {}", bdd.cache().faults());
    println!("cache misses: {}", bdd.cache().misses());

    let time_total = time_total.elapsed();
    println!("Done in {:.3} s", time_total.as_secs_f64());

    Ok(())
}
