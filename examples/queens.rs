use bdd_rs::bdd::Bdd;
use bdd_rs::reference::Ref;

fn main() -> color_eyre::Result<()> {
    color_eyre::install()?;

    simplelog::TermLogger::init(
        simplelog::LevelFilter::Info,
        simplelog::Config::default(),
        simplelog::TerminalMode::Mixed,
        simplelog::ColorChoice::Auto,
    )?;

    let time_total = std::time::Instant::now();

    // Note: 20 bits (default) are enough to encode at most n=8 queens.
    let bdd = Bdd::default();
    println!("bdd = {:?}", bdd);

    // Encode N-queens problem:
    // - N queens on an NxN board
    // - One queen per row
    // - One queen per column
    // - No two queens on the same diagonal
    let n: usize = if let Some(s) = std::env::args().nth(1) {
        s.parse().expect("invalid number")
    } else {
        8
    };
    println!("n = {}", n);
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
    println!("Merging constraints...");
    let res = bdd.apply_and_many(&constraints);
    println!("bdd = {:?}", bdd);
    println!(
        "res of size {} = {}",
        bdd.size(res),
        bdd.to_bracket_string(res)
    );

    let time_total = time_total.elapsed();
    println!("Done in {:.3} s", time_total.as_secs_f64());

    Ok(())
}
