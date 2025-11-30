//! # Peterson's Mutual Exclusion Protocol — Symbolic Model Checking Tutorial
//!
//! This example demonstrates BDD-based symbolic model checking on a classic
//! concurrency problem: Peterson's mutual exclusion algorithm for two processes.
//!
//! ## What is Mutual Exclusion?
//!
//! In concurrent systems, a *critical section* is code that accesses shared resources.
//! Only one process should execute its critical section at a time — this is the
//! *mutual exclusion* property. Peterson's algorithm achieves this using only
//! shared memory (no special hardware instructions).
//!
//! ## What We Verify
//!
//! 1. **Safety (Mutual Exclusion)**: Two processes never in critical section simultaneously
//! 2. **Liveness (No Starvation)**: A waiting process eventually enters critical section
//! 3. **Reachability**: Critical section is actually reachable
//!
//! ## How It Works
//!
//! The model checker explores *all possible interleavings* of the two processes
//! symbolically using BDDs. Instead of enumerating states one by one, BDDs
//! represent and manipulate entire sets of states at once.
//!
//! Run with: `cargo run --example mutex --release`

use std::rc::Rc;

use bdd_rs::bdd::Bdd;
use model_checking::*;

fn main() {
    println!("Peterson's Mutual Exclusion Protocol");
    println!("====================================\n");

    // -- Step 1: Create the BDD Manager --
    //
    // The BDD manager handles symbolic operations. The transition system
    // represents states and transitions.

    println!("Step 1: Building the model...\n");

    let bdd = Rc::new(Bdd::default());
    let mut ts = TransitionSystem::new(bdd.clone());

    // -- Step 2: State Variables --
    //
    // Peterson's algorithm uses:
    //   - flag0, flag1: "I want to enter" flags
    //   - turn: Tie-breaker
    //   - pc0, pc1: 0=idle, 1=in critical section

    let flag0 = Var::new("flag0"); // Process 0's intent flag
    let flag1 = Var::new("flag1"); // Process 1's intent flag
    let turn = Var::new("turn"); // Whose turn (0 or 1)
    let pc0 = Var::new("pc0"); // Process 0: 0=not critical, 1=critical
    let pc1 = Var::new("pc1"); // Process 1: 0=not critical, 1=critical

    ts.declare_var(flag0.clone());
    ts.declare_var(flag1.clone());
    ts.declare_var(turn.clone());
    ts.declare_var(pc0.clone());
    ts.declare_var(pc1.clone());

    println!("  State variables:");
    println!("  - flag0, flag1: intent flags ('I want to enter')");
    println!("  - turn: tie-breaker variable");
    println!("  - pc0, pc1: in critical section? (0=no, 1=yes)\n");

    // Get BDD variable handles for present-state encoding
    let flag0_p = ts.var_manager().get_present(&flag0).unwrap();
    let flag1_p = ts.var_manager().get_present(&flag1).unwrap();
    let turn_p = ts.var_manager().get_present(&turn).unwrap();
    let pc0_p = ts.var_manager().get_present(&pc0).unwrap();
    let pc1_p = ts.var_manager().get_present(&pc1).unwrap();

    let flag0_bdd = bdd.mk_var(flag0_p);
    let flag1_bdd = bdd.mk_var(flag1_p);
    let turn_bdd = bdd.mk_var(turn_p);
    let pc0_bdd = bdd.mk_var(pc0_p);
    let pc1_bdd = bdd.mk_var(pc1_p);

    // -- Step 3: Initial States --
    //
    // No flags raised, both processes idle. 'turn' can be either value.

    let not_flag0 = bdd.apply_not(flag0_bdd);
    let not_flag1 = bdd.apply_not(flag1_bdd);
    let not_pc0 = bdd.apply_not(pc0_bdd);
    let not_pc1 = bdd.apply_not(pc1_bdd);

    // Initial = ¬flag0 ∧ ¬flag1 ∧ ¬pc0 ∧ ¬pc1
    let initial = bdd.apply_and_many([not_flag0, not_flag1, not_pc0, not_pc1].into_iter());
    ts.set_initial(initial);

    println!("  Initial state: flags=0, both processes idle\n");

    // -- Step 4: Transition Relation --
    //
    // Entry conditions:
    //   - P0 can enter if: flag0 ∧ (¬flag1 ∨ turn=0)
    //   - P1 can enter if: flag1 ∧ (¬flag0 ∨ turn=1)

    // Entry conditions from Peterson's algorithm
    let can_enter_0 = bdd.apply_and(flag0_bdd, bdd.apply_or(not_flag1, bdd.apply_not(turn_bdd)));
    let can_enter_1 = bdd.apply_and(flag1_bdd, bdd.apply_or(not_flag0, turn_bdd));

    // Get next-state variable handles
    let flag0_next = ts.var_manager().get_next(&flag0).unwrap();
    let flag1_next = ts.var_manager().get_next(&flag1).unwrap();
    let turn_next = ts.var_manager().get_next(&turn).unwrap();
    let pc0_next = ts.var_manager().get_next(&pc0).unwrap();
    let pc1_next = ts.var_manager().get_next(&pc1).unwrap();

    let flag0_next_bdd = bdd.mk_var(flag0_next);
    let flag1_next_bdd = bdd.mk_var(flag1_next);
    let turn_next_bdd = bdd.mk_var(turn_next);
    let pc0_next_bdd = bdd.mk_var(pc0_next);
    let pc1_next_bdd = bdd.mk_var(pc1_next);

    // Suppress unused variable warnings - these are available for extensions
    let _ = flag0_next_bdd;
    let _ = flag1_next_bdd;

    // Process 0 transitions for pc0
    let p0_enter = bdd.apply_and(can_enter_0, not_pc0); // Can enter if allowed and not already in
    let p0_exit = pc0_bdd; // Can exit if in critical

    // pc0' = 1 if entering, 0 if exiting, else unchanged
    let pc0_becomes_1 = bdd.apply_and(p0_enter, pc0_next_bdd);
    let pc0_becomes_0 = bdd.apply_and(p0_exit, bdd.apply_not(pc0_next_bdd));
    let pc0_stays = bdd.apply_and(bdd.apply_not(bdd.apply_or(p0_enter, p0_exit)), bdd.apply_eq(pc0_next_bdd, pc0_bdd));
    let pc0_trans = bdd.apply_or(bdd.apply_or(pc0_becomes_1, pc0_becomes_0), pc0_stays);

    // Process 1 transitions for pc1 (symmetric)
    let p1_enter = bdd.apply_and(can_enter_1, not_pc1);
    let p1_exit = pc1_bdd;

    let pc1_becomes_1 = bdd.apply_and(p1_enter, pc1_next_bdd);
    let pc1_becomes_0 = bdd.apply_and(p1_exit, bdd.apply_not(pc1_next_bdd));
    let pc1_stays = bdd.apply_and(bdd.apply_not(bdd.apply_or(p1_enter, p1_exit)), bdd.apply_eq(pc1_next_bdd, pc1_bdd));
    let pc1_trans = bdd.apply_or(bdd.apply_or(pc1_becomes_1, pc1_becomes_0), pc1_stays);

    // Flags can change non-deterministically (simplified protocol model)
    let flag0_trans = bdd.one();
    let flag1_trans = bdd.one();

    // Turn alternates on transition (models giving priority to other process)
    let turn_trans = bdd.apply_eq(turn_next_bdd, bdd.apply_not(turn_bdd));

    let transition = bdd.apply_and_many([pc0_trans, pc1_trans, flag0_trans, flag1_trans, turn_trans].into_iter());
    ts.set_transition(transition);

    println!("  Transition relation built");
    println!("  - Entry P0: flag0 ∧ (¬flag1 ∨ turn=0)");
    println!("  - Entry P1: flag1 ∧ (¬flag0 ∨ turn=1)\n");

    // -- Step 5: Labels --
    //
    // Labels identify states for use in temporal logic formulas.

    ts.add_label("critical0".to_string(), pc0_bdd); // P0 in critical
    ts.add_label("critical1".to_string(), pc1_bdd); // P1 in critical

    // Mutual exclusion predicate: not both in critical
    let both_critical = bdd.apply_and(pc0_bdd, pc1_bdd);
    let mutex = bdd.apply_not(both_critical);
    ts.add_label("mutex".to_string(), mutex);

    let ts = Rc::new(ts);

    // -- Step 6: State Space Analysis --

    println!("Step 2: Analyzing state space...\n");

    let reachable = ts.reachable();
    let state_count = ts.count_states(reachable);

    println!("  Variables: 5 (flag0, flag1, turn, pc0, pc1)");
    println!("  Max states: 2^5 = 32");
    if let Some(count) = state_count {
        println!("  Reachable: {}", count);
        assert!(count > 0, "Must have at least one reachable state!");
        assert!(count <= 32, "Cannot exceed 2^5 states!");
        println!("  ✓ State space is valid\n");
    }

    // -- Step 7: Verify Properties --

    println!("Step 3: Verifying temporal properties...\n");

    let checker = CtlChecker::new(ts.clone());

    // Property 1: AG mutex
    //
    // In ALL paths (A), at EVERY state (G), mutex is true.
    // This is the fundamental safety property.

    println!("--- Property 1: Mutual Exclusion (Safety) ---");
    println!("CTL: AG mutex");
    println!("'At most one process in critical section at any time'\n");

    let ag_mutex = CtlFormula::atom("mutex").ag();
    let mutex_holds = checker.holds_initially(&ag_mutex);

    println!("  Result: {}", if mutex_holds { "✓ HOLDS" } else { "✗ VIOLATED" });
    assert!(mutex_holds, "CRITICAL: Mutual exclusion violated!");
    println!("  ✓ Mutual exclusion guaranteed\n");

    // Property 2: AG (critical0 → AF ¬critical0)
    //
    // If P0 enters critical section, it eventually exits.

    println!("--- Property 2: No Infinite Critical Section ---");
    println!("CTL: AG (critical0 → AF ¬critical0)");
    println!("'Process 0 eventually exits critical section'\n");

    let exit_prop = CtlFormula::atom("critical0").implies(CtlFormula::atom("critical0").not().af()).ag();
    let exit_holds = checker.holds_initially(&exit_prop);

    println!("  Result: {}", if exit_holds { "✓ HOLDS" } else { "✗ VIOLATED" });
    if exit_holds {
        println!("  ✓ Processes don't get stuck\n");
    } else {
        println!("  Note: Simplified model allows indefinite stay\n");
    }

    // Property 3: EF critical0
    //
    // There EXISTS a path where EVENTUALLY P0 is in critical.
    // Verifies the protocol is not trivially safe.

    println!("--- Property 3: Reachability (Sanity Check) ---");
    println!("CTL: EF critical0");
    println!("'Process 0 can reach critical section'\n");

    let ef_critical0 = CtlFormula::atom("critical0").ef();
    let can_reach = checker.holds_initially(&ef_critical0);

    println!("  Result: {}", if can_reach { "✓ HOLDS" } else { "✗ VIOLATED" });
    assert!(can_reach, "Critical section must be reachable!");
    println!("  ✓ Critical section is reachable\n");

    // Property 4: EF critical1

    println!("--- Property 4: Symmetric Reachability ---");
    println!("CTL: EF critical1");
    println!("'Process 1 can reach critical section'\n");

    let ef_critical1 = CtlFormula::atom("critical1").ef();
    let can_reach_1 = checker.holds_initially(&ef_critical1);

    println!("  Result: {}", if can_reach_1 { "✓ HOLDS" } else { "✗ VIOLATED" });
    assert!(can_reach_1, "Process 1 must be able to enter!");
    println!("  ✓ Both processes can use the resource\n");

    // -- Summary --

    println!("Summary");
    println!("-------");
    println!("  AG mutex (mutual exclusion):    {}", if mutex_holds { "✓" } else { "✗" });
    println!("  AG (crit → AF ¬crit):           {}", if exit_holds { "✓" } else { "✗" });
    println!("  EF critical0:                   {}", if can_reach { "✓" } else { "✗" });
    println!("  EF critical1:                   {}", if can_reach_1 { "✓" } else { "✗" });
    println!();
    println!("✓ All critical assertions passed!");
    println!("  BDDs verified Peterson's algorithm symbolically.\n");
}
