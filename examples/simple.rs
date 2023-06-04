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

    // let f = bdd.apply_ite(x1, x2, x3);
    // println!("ite(x1, x2, x3) = {:?}", f);
    //
    // let g = bdd.mk_node(bdd.variable(x1.index()), x3, x2);
    // println!("g = {:?}", g);

    // let f = bdd.apply_ite(-x1, -x2, -x3);
    // println!("f = {:?}", f);
    // let g = bdd.mk_node(bdd.variable(x1.index()), -x2, -x3);
    // println!("g = {:?}", g);

    // let f = bdd.mk_node(bdd.variable(x1.index()), -x2, -x3);
    // println!("f = {}", f);
    // let g = bdd.apply_ite(-x1, -x2, -x3);
    // println!("g = {}", g);
    // let h = -bdd.apply_ite(x1, x3, x2);
    // println!("h = {}", h);
    // println!("f == g: {}", f == g);

    let s = bdd.mk_node(3, -bdd.one, bdd.one);
    let p = bdd.mk_node(2, -s, s);
    let r = bdd.mk_node(2, s, bdd.one);
    let q = bdd.mk_node(2, -s, bdd.one);
    let t = bdd.mk_node(2, -bdd.one, s);

    println!("s = {}", bdd.to_bracket_string(s));
    println!("p = {}", bdd.to_bracket_string(p));
    println!("r = {}", bdd.to_bracket_string(r));
    println!("q = {}", bdd.to_bracket_string(q));
    println!("t = {}", bdd.to_bracket_string(t));

    println!("---");

    let f = bdd.mk_node(1, -p, s);
    println!("f = {}", bdd.to_bracket_string(f));
    let g = bdd.mk_node(1, -r, q);
    println!("g = {}", bdd.to_bracket_string(g));
    let h = bdd.mk_node(1, -bdd.one, t);
    println!("h = {}", bdd.to_bracket_string(h));

    let fg = bdd.constrain(f, g);
    println!("f|g = {}", bdd.to_bracket_string(fg));

    Ok(())
}
