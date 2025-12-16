//! Combinations example: Computing C(n,k) with ZDDs.

use ananke_zdd::zdd::ZddManager;

fn main() {
    println!("=== ZDD Combinations Example ===\n");

    let mgr = ZddManager::new();

    // Verify Pascal's triangle
    println!("Pascal's Triangle (via ZDD counting):\n");
    for n in 0..=8 {
        let vars: Vec<u32> = (1..=n).collect();
        print!("{:>4}: ", n);
        for k in 0..=n {
            let ck = mgr.combinations(vars.iter().copied(), k as usize);
            print!("{:>4} ", mgr.count(ck));
        }
        println!();
    }

    println!("\n--- Detailed C(5, 2) ---");
    let c52 = mgr.combinations(1u32..=5, 2);
    println!("C(5,2) = {} combinations", mgr.count(c52));
    println!("ZDD nodes: {}", mgr.node_count(c52));

    println!("\nAll 2-element subsets of {{1,2,3,4,5}}:");
    for (i, set) in mgr.iter_sets(c52).enumerate() {
        let elements: Vec<_> = set.iter().map(|v| v.id()).collect();
        println!("  {:2}. {:?}", i + 1, elements);
    }

    println!("\n--- Large Combinations ---");
    for n in [10u32, 15, 20, 25] {
        let vars: Vec<u32> = (1..=n).collect();
        for k in [2, n / 2] {
            let ck = mgr.combinations(vars.iter().copied(), k as usize);
            println!(
                "C({:2}, {:2}) = {:>10} combinations, {:>6} ZDD nodes",
                n,
                k,
                mgr.count(ck),
                mgr.node_count(ck)
            );
        }
    }

    // Demonstrate operations on combinations
    println!("\n--- Operations on Combinations ---");

    let c43 = mgr.combinations(1u32..=4, 3);
    let c42 = mgr.combinations(1u32..=4, 2);

    println!("C(4,3) = {} sets", mgr.count(c43));
    println!("C(4,2) = {} sets", mgr.count(c42));

    // Union of all 2 and 3-element subsets
    let union = mgr.union(c43, c42);
    println!("C(4,3) ∪ C(4,2) = {} sets (expected {})", mgr.count(union), 4 + 6);

    // Intersection is empty (no set is both 2 and 3 elements)
    let inter = mgr.intersection(c43, c42);
    println!("C(4,3) ∩ C(4,2) = {} sets (expected 0)", mgr.count(inter));

    println!("\n--- Memory Efficiency ---");
    println!("Total nodes in manager: {}", mgr.num_nodes());

    // Compare powerset vs combinations
    let n = 10u32;
    let vars: Vec<u32> = (1..=n).collect();
    let ps = mgr.powerset(vars.iter().copied());
    let c_half = mgr.combinations(vars.iter().copied(), 5);

    println!("\nFor n={}:", n);
    println!("  Powerset (2^{} = {} sets): {} ZDD nodes", n, mgr.count(ps), mgr.node_count(ps));
    println!(
        "  C({},{}) = {} sets: {} ZDD nodes",
        n,
        5,
        mgr.count(c_half),
        mgr.node_count(c_half)
    );
}
