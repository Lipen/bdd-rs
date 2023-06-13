use bdd_rs::bdd::Bdd;

fn main() -> color_eyre::Result<()> {
    color_eyre::install()?;

    simplelog::TermLogger::init(
        simplelog::LevelFilter::Debug,
        simplelog::Config::default(),
        simplelog::TerminalMode::Mixed,
        simplelog::ColorChoice::Auto,
    )?;

    let mut bdd = Bdd::default();
    println!("bdd = {:?}", bdd);

    println!("zero = {}", bdd.zero);
    println!("one = {}", bdd.one);

    let x1 = bdd.mk_var(1);
    println!("x1 = {}", x1);
    let x2 = bdd.mk_var(2);
    println!("x2 = {}", x2);
    let x3 = bdd.mk_var(3);
    println!("x3 = {}", x3);

    let cube = bdd.cube(&[1, 2, 3]);
    println!("cube = {}", bdd.to_bracket_string(cube));
    let f = bdd.cube(&[2]);
    println!("f = {}", bdd.to_bracket_string(f));
    let h = bdd.constrain(f, cube);
    println!("h = {}", bdd.to_bracket_string(h));

    Ok(())
}
