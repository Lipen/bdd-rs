use ananke_sdd::SddManager;

fn main() {
    let mgr = SddManager::new(5);

    println!("── Example from SDD Beginner's Manual ──\n");

    let a = mgr.literal(1);
    let b = mgr.literal(2);
    let c = mgr.literal(3);
    let faulty1 = mgr.literal(4);
    let faulty2 = mgr.literal(5);

    let mut delta = mgr.true_sdd();
    let mut alpha;

    // ~faulty1  =>  (a <=> ~b)
    alpha = mgr.implies(mgr.neg(faulty1), mgr.equiv(a, mgr.neg(b)));
    delta = mgr.and(delta, alpha);

    // faulty1  =>  (a <=> b)  OR  ~b
    alpha = mgr.implies(faulty1, mgr.or(mgr.equiv(a, b), mgr.neg(b)));
    delta = mgr.and(delta, alpha);

    // ~faulty2  =>  (b <=> ~c)
    alpha = mgr.implies(mgr.neg(faulty2), mgr.equiv(b, mgr.neg(c)));
    delta = mgr.and(delta, alpha);

    // faulty2  =>  (b <=> c)  OR  ~c
    alpha = mgr.implies(faulty2, mgr.or(mgr.equiv(b, c), mgr.neg(c)));
    delta = mgr.and(delta, alpha);

    // Conditioning: A=1, C=0
    delta = mgr.condition(delta, 1);
    delta = mgr.condition(delta, -3);

    println!("SDD for delta: {}", mgr.display(delta));
    println!("DOT for delta:");
    println!("{}", mgr.to_dot(delta));

    // Quantification: exists B
    let diagnosis = mgr.exists(delta, 2);
    println!("SDD for diagnosis: {}", mgr.display(diagnosis));
    println!(
        "Variables for diagnosis: {:?}",
        mgr.vtree().variables_under(mgr.node_vtree(diagnosis))
    );
    println!("Model count for diagnosis: {}", mgr.model_count(diagnosis));
    println!("Model count (local) for diagnosis: {}", mgr.model_count_local(diagnosis));
    println!("DOT for diagnosis:");
    println!("{}", mgr.to_dot(diagnosis));
}
