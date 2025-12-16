//! Simple ZDD example demonstrating basic operations.

use ananke_zdd::reference::ZddId;
use ananke_zdd::types::Var;
use ananke_zdd::zdd::ZddManager;

fn main() {
    println!("=== ZDD Simple Example ===\n");

    let mgr = ZddManager::new();

    // Create base sets (singletons)
    println!("Creating base sets...");
    let x1 = mgr.base(1); // {{1}}
    let x2 = mgr.base(2); // {{2}}
    let x3 = mgr.base(3); // {{3}}

    println!("x1 = {{{{1}}}} : {} sets", mgr.count(x1));
    println!("x2 = {{{{2}}}} : {} sets", mgr.count(x2));
    println!("x3 = {{{{3}}}} : {} sets", mgr.count(x3));

    // Union
    println!("\n--- Union ---");
    let union_12 = mgr.union(x1, x2);
    println!("x1 ∪ x2 = {{{{1}}, {{2}}}} : {} sets", mgr.count(union_12));
    print_sets(&mgr, union_12);

    // Join (cross product)
    println!("\n--- Join (Cross Product) ---");
    let join_12 = mgr.join(x1, x2);
    println!("x1 ⊗ x2 = {{{{1, 2}}}} : {} sets", mgr.count(join_12));
    print_sets(&mgr, join_12);

    // More complex join
    let join_123 = mgr.join(join_12, x3);
    println!("(x1 ⊗ x2) ⊗ x3 = {{{{1, 2, 3}}}} : {} sets", mgr.count(join_123));
    print_sets(&mgr, join_123);

    // Intersection
    println!("\n--- Intersection ---");
    let union_all = mgr.union(mgr.union(x1, x2), x3);
    let inter = mgr.intersection(union_all, x1);
    println!("({{{{1}}, {{2}}, {{3}}}}) ∩ {{{{1}}}} = {{{{1}}}} : {} sets", mgr.count(inter));

    // Difference
    println!("\n--- Difference ---");
    let diff = mgr.difference(union_12, x1);
    println!("{{{{1}}, {{2}}}} \\ {{{{1}}}} = {{{{2}}}} : {} sets", mgr.count(diff));
    print_sets(&mgr, diff);

    // Powerset
    println!("\n--- Powerset ---");
    let ps = mgr.powerset([1u32, 2, 3]);
    println!("2^{{1,2,3}} : {} sets", mgr.count(ps));
    print_sets(&mgr, ps);

    // Combinations
    println!("\n--- Combinations ---");
    let c52 = mgr.combinations([1u32, 2, 3, 4, 5], 2);
    println!("C(5,2) : {} sets (expected 10)", mgr.count(c52));
    print_sets(&mgr, c52);

    // Subset operations
    println!("\n--- Subset Operations ---");
    let family = mgr.union(mgr.union(x1, x2), join_12);
    println!("Family F = {{{{1}}, {{2}}, {{1,2}}}}");
    print_sets(&mgr, family);

    let s0 = mgr.subset0(family, Var::new(1));
    println!("\nsubset0(F, 1) - sets NOT containing 1:");
    print_sets(&mgr, s0);

    let s1 = mgr.subset1(family, Var::new(1));
    println!("\nsubset1(F, 1) - sets containing 1, with 1 removed:");
    print_sets(&mgr, s1);

    // Change operation
    println!("\n--- Change Operation ---");
    let changed = mgr.change(x1, Var::new(1));
    println!("change({{{{1}}}}, 1) = {{∅}}");
    print_sets(&mgr, changed);

    let changed2 = mgr.change(ZddId::ONE, Var::new(2));
    println!("change({{∅}}, 2) = {{{{2}}}}");
    print_sets(&mgr, changed2);

    // Statistics
    println!("\n--- Statistics ---");
    println!("Total nodes in manager: {}", mgr.num_nodes());
    println!("Nodes in powerset ZDD: {}", mgr.node_count(ps));

    // DOT output
    println!("\n--- DOT Output (for C(4,2)) ---");
    let c42 = mgr.combinations([1u32, 2, 3, 4], 2);
    println!("C(4,2) = {} sets", mgr.count(c42));
    println!("{}", mgr.to_dot(c42));
}

fn print_sets(mgr: &ZddManager, f: ZddId) {
    let sets: Vec<_> = mgr.iter_sets(f).collect();
    print!("  {{ ");
    for (i, set) in sets.iter().enumerate() {
        if i > 0 {
            print!(", ");
        }
        if set.is_empty() {
            print!("∅");
        } else {
            print!("{{");
            for (j, var) in set.iter().enumerate() {
                if j > 0 {
                    print!(", ");
                }
                print!("{}", var.id());
            }
            print!("}}");
        }
    }
    println!(" }}");
}
