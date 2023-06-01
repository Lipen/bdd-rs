use bdd_rs::bdd::Bdd;

fn main() -> color_eyre::Result<()> {
    color_eyre::install()?;

    // simplelog::SimpleLogger::init(
    //     simplelog::LevelFilter::Debug,
    //     simplelog::Config::default()
    // )?;
    simplelog::TermLogger::init(
        simplelog::LevelFilter::Debug,
        simplelog::Config::default(),
        simplelog::TerminalMode::Mixed,
        simplelog::ColorChoice::Auto,
    )?;

    let mut bdd = Bdd::new(20);
    println!("bdd = {:?}", bdd);

    println!("zero = {}", bdd.zero);
    println!("one = {}", bdd.one);

    let x1 = bdd.mk_node(1, bdd.zero, bdd.one);
    println!("x1 = {}", x1);
    let x2 = bdd.mk_node(2, bdd.zero, bdd.one);
    println!("x2 = {}", x2);
    let x3 = bdd.mk_node(3, bdd.zero, bdd.one);
    println!("x3 = {}", x3);

    // let f = bdd.apply_ite(x1, x2, x3);
    // println!("ite(x1, x2, x3) = {:?}", f);
    //
    // let g = bdd.mk_node(bdd.variable(x1.index()), x3, x2);
    // println!("g = {:?}", g);

    // let f = bdd.apply_ite(-x1, -x2, -x3);
    // println!("f = {:?}", f);
    // let g = bdd.mk_node(bdd.variable(x1.index()), -x2, -x3);
    // println!("g = {:?}", g);

    let f = bdd.mk_node(bdd.variable(x1.index()), -x2, -x3);
    println!("f = {}", f);
    let g = bdd.apply_ite(-x1, -x2, -x3);
    println!("g = {}", g);
    let h = -bdd.apply_ite(x1, x3, x2);
    println!("h = {}", h);
    println!("f == g: {}", f == g);

    Ok(())
}
