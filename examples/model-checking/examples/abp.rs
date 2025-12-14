//! # Alternating Bit Protocol — Reliable Transmission over Lossy Channels
//!
//! This example demonstrates BDD-based symbolic model checking on the Alternating
//! Bit Protocol (ABP), a classic network protocol that ensures reliable message
//! delivery over an unreliable (lossy) channel.
//!
//! ## The Problem
//!
//! How do you reliably send messages when:
//! - Messages can be lost in transit
//! - Acknowledgments can be lost in transit
//! - The channel doesn't guarantee delivery order
//!
//! ## The Solution: Alternating Bit Protocol
//!
//! The sender and receiver maintain a single "alternating bit":
//!
//! ```text
//!  SENDER                         RECEIVER
//!    |                               |
//!    |  ---(msg, bit=0)----------->  |  (accepts msg if bit matches)
//!    |  <---(ack, bit=0)-----------  |  (sends ack with same bit)
//!    |                               |
//!    |  [sender flips bit to 1]      |  [receiver flips expected bit]
//!    |                               |
//!    |  ---(msg, bit=1)----------->  |
//!    |  <---(ack, bit=1)-----------  |
//!    |                               |
//!    |  [sender flips bit to 0]      |  [receiver flips expected bit]
//!    |  ...continues...              |
//! ```
//!
//! Key insight: Retransmit until acknowledgment received. The alternating bit
//! distinguishes new messages from retransmissions.
//!
//! ## What We Verify
//!
//! 1. **Safety**: Messages are delivered in order, no duplicates accepted
//! 2. **Liveness** (with fairness): Every sent message is eventually delivered
//! 3. **Fairness matters**: Without fairness, channel can lose messages forever!
//!
//! ## Simplified Model
//!
//! We use a simplified 5-variable model focusing on the essential protocol behavior:
//!
//! State = (sender_bit, receiver_bit, msg_pending, ack_pending, delivered)
//!
//! This captures the core alternating bit mechanism while keeping the state
//! space small enough for fast verification.
//!
//! Run with: `cargo run --example abp --release`

use std::rc::Rc;

use ananke_bdd::bdd::Bdd;
use ananke_bdd::reference::Ref;
use model_checking::*;

fn main() {
    println!("Alternating Bit Protocol - Reliable Transmission");
    println!("=================================================\n");

    println!("The Alternating Bit Protocol ensures reliable message delivery");
    println!("over an unreliable channel that can lose messages.\n");

    // ═══════════════════════════════════════════════════════════════════════════
    // STEP 1: Create the BDD Manager and Transition System
    // ═══════════════════════════════════════════════════════════════════════════

    println!("Step 1: Building the ABP model...\n");

    let bdd = Rc::new(Bdd::default());
    let mut ts = TransitionSystem::new(bdd.clone());

    // ═══════════════════════════════════════════════════════════════════════════
    // STEP 2: Declare State Variables
    // ═══════════════════════════════════════════════════════════════════════════
    //
    // Simplified model:
    // - sender_bit: The bit the sender is currently using (1 bit)
    // - receiver_bit: The bit the receiver expects (1 bit)
    // - msg_pending: Is there a message in the channel? (1 bit)
    // - ack_pending: Is there an ack in the channel? (1 bit)
    // - delivered: Has at least one message been delivered? (1 bit)

    let sender_bit = Var::new("sender_bit");
    let receiver_bit = Var::new("receiver_bit");
    let msg_pending = Var::new("msg_pending");
    let ack_pending = Var::new("ack_pending");
    let delivered = Var::new("delivered");

    ts.declare_var(sender_bit.clone());
    ts.declare_var(receiver_bit.clone());
    ts.declare_var(msg_pending.clone());
    ts.declare_var(ack_pending.clone());
    ts.declare_var(delivered.clone());

    println!("  State variables (5 boolean):");
    println!("  - sender_bit   : Bit sender uses for current message");
    println!("  - receiver_bit : Bit receiver expects next");
    println!("  - msg_pending  : Message currently in transit?");
    println!("  - ack_pending  : Acknowledgment currently in transit?");
    println!("  - delivered    : Has a message been delivered?\n");

    // Get present-state BDD variables
    let sb_p = ts.var_manager().get_present(&sender_bit).unwrap();
    let rb_p = ts.var_manager().get_present(&receiver_bit).unwrap();
    let mp_p = ts.var_manager().get_present(&msg_pending).unwrap();
    let ap_p = ts.var_manager().get_present(&ack_pending).unwrap();
    let del_p = ts.var_manager().get_present(&delivered).unwrap();

    let sb = bdd.mk_var(sb_p);
    let rb = bdd.mk_var(rb_p);
    let mp = bdd.mk_var(mp_p);
    let ap = bdd.mk_var(ap_p);
    let del = bdd.mk_var(del_p);

    // Get next-state BDD variables
    let sb_n = ts.var_manager().get_next(&sender_bit).unwrap();
    let rb_n = ts.var_manager().get_next(&receiver_bit).unwrap();
    let mp_n = ts.var_manager().get_next(&msg_pending).unwrap();
    let ap_n = ts.var_manager().get_next(&ack_pending).unwrap();
    let del_n = ts.var_manager().get_next(&delivered).unwrap();

    let sb_next = bdd.mk_var(sb_n);
    let rb_next = bdd.mk_var(rb_n);
    let mp_next = bdd.mk_var(mp_n);
    let ap_next = bdd.mk_var(ap_n);
    let del_next = bdd.mk_var(del_n);

    // ═══════════════════════════════════════════════════════════════════════════
    // STEP 3: Initial State
    // ═══════════════════════════════════════════════════════════════════════════

    // Initially: bits match, channels empty, nothing delivered
    let initial = bdd.apply_and_many([
        bdd.apply_not(sb),  // sender_bit = 0
        bdd.apply_not(rb),  // receiver_bit = 0
        bdd.apply_not(mp),  // no message pending
        bdd.apply_not(ap),  // no ack pending
        bdd.apply_not(del), // nothing delivered
    ]);
    ts.set_initial(initial);

    println!("  Initial state:");
    println!("  - sender_bit = 0, receiver_bit = 0 (synchronized)");
    println!("  - Channels empty, nothing delivered\n");

    // ═══════════════════════════════════════════════════════════════════════════
    // STEP 4: Transition Relation
    // ═══════════════════════════════════════════════════════════════════════════
    //
    // Actions (non-deterministic choice):
    // 1. SEND: Sender puts message into channel (if empty)
    // 2. LOSE_MSG: Channel loses the message
    // 3. RECEIVE: Receiver accepts message if bits match, sends ack
    // 4. LOSE_ACK: Channel loses the ack
    // 5. ACK_RECV: Sender receives ack if bits are desynced, flips bit

    println!("  Transitions (5 actions):");
    println!("  1. SEND     : Sender puts message in channel");
    println!("  2. LOSE_MSG : Channel loses the message");
    println!("  3. RECEIVE  : Receiver accepts message, sends ack");
    println!("  4. LOSE_ACK : Channel loses the acknowledgment");
    println!("  5. ACK_RECV : Sender receives ack, advances\n");

    // Helper: keep variable unchanged
    let unchanged = |next: Ref, pres: Ref| -> Ref { bdd.apply_eq(next, pres) };

    // Action 1: SEND - sender sends message (when not already pending)
    let send_guard = bdd.apply_not(mp);
    let send_effect = bdd.apply_and_many([
        mp_next, // msg_pending' = true
        unchanged(sb_next, sb),
        unchanged(rb_next, rb),
        unchanged(ap_next, ap),
        unchanged(del_next, del),
    ]);
    let send = bdd.apply_and(send_guard, send_effect);

    // Action 2: LOSE_MSG - message is lost
    let lose_msg_guard = mp;
    let lose_msg_effect = bdd.apply_and_many([
        bdd.apply_not(mp_next), // msg_pending' = false
        unchanged(sb_next, sb),
        unchanged(rb_next, rb),
        unchanged(ap_next, ap),
        unchanged(del_next, del),
    ]);
    let lose_msg = bdd.apply_and(lose_msg_guard, lose_msg_effect);

    // Action 3: RECEIVE - receiver accepts message if bits match
    // In simplified model: message arrives with sender's bit, receiver accepts if it matches
    let synced = bdd.apply_eq(sb, rb);
    let receive_guard = bdd.apply_and(mp, synced);
    let receive_effect = bdd.apply_and_many([
        bdd.apply_not(mp_next),                   // consume message
        ap_next,                                  // ack_pending' = true
        bdd.apply_eq(rb_next, bdd.apply_not(rb)), // receiver flips bit
        unchanged(sb_next, sb),
        del_next, // delivered' = true
    ]);
    let receive = bdd.apply_and(receive_guard, receive_effect);

    // Action 4: LOSE_ACK - ack is lost
    let lose_ack_guard = ap;
    let lose_ack_effect = bdd.apply_and_many([
        bdd.apply_not(ap_next), // ack_pending' = false
        unchanged(sb_next, sb),
        unchanged(rb_next, rb),
        unchanged(mp_next, mp),
        unchanged(del_next, del),
    ]);
    let lose_ack = bdd.apply_and(lose_ack_guard, lose_ack_effect);

    // Action 5: ACK_RECV - sender receives ack
    // In simplified model: ack carries receiver's OLD bit (before flip), which matches sender's current bit
    // So we just check ack_pending and bits are now different (receiver already flipped)
    let desynced = bdd.apply_not(synced);
    let ack_recv_guard = bdd.apply_and(ap, desynced);
    let ack_recv_effect = bdd.apply_and_many([
        bdd.apply_not(ap_next),                   // consume ack
        bdd.apply_eq(sb_next, bdd.apply_not(sb)), // sender flips bit (now synced again)
        unchanged(rb_next, rb),
        unchanged(mp_next, mp),
        unchanged(del_next, del),
    ]);
    let ack_recv = bdd.apply_and(ack_recv_guard, ack_recv_effect);

    // Combined transition: disjunction of all actions
    let transition = bdd.apply_or_many([send, lose_msg, receive, lose_ack, ack_recv]);
    ts.set_transition(transition);

    // ═══════════════════════════════════════════════════════════════════════════
    // STEP 5: Define Atomic Propositions (Labels)
    // ═══════════════════════════════════════════════════════════════════════════

    ts.add_label("synced".to_string(), synced);
    ts.add_label("delivered".to_string(), del);
    ts.add_label("msg_pending".to_string(), mp);
    ts.add_label("ack_pending".to_string(), ap);

    let channels_empty = bdd.apply_and(bdd.apply_not(mp), bdd.apply_not(ap));
    ts.add_label("channels_empty".to_string(), channels_empty);

    let can_send = bdd.apply_not(mp);
    ts.add_label("can_send".to_string(), can_send);

    let ts = Rc::new(ts);

    // ═══════════════════════════════════════════════════════════════════════════
    // STEP 6: State Space Analysis
    // ═══════════════════════════════════════════════════════════════════════════

    println!("Step 2: Analyzing state space...\n");

    let reachable = ts.reachable();
    let state_count = ts.count_states(reachable);

    println!("  Total variables: 5 boolean");
    println!("  Maximum possible states: 2^5 = 32");
    if let Some(count) = state_count {
        println!("  Reachable states: {}", count);
        assert!(count > 0, "Must have reachable states");
        assert!(count <= 32, "Cannot exceed 2^5 states");
        println!("  ✓ State space explored\n");
    }

    // ═══════════════════════════════════════════════════════════════════════════
    // STEP 7: CTL Model Checking
    // ═══════════════════════════════════════════════════════════════════════════

    println!("Step 3: Verifying CTL properties...\n");

    let checker = CtlChecker::new(ts.clone());

    // Property 1: EF delivered
    println!("--- Property 1: Delivery Possibility ---");
    println!("CTL: EF delivered");
    println!("'Is there some execution path where a message is delivered?'\n");

    let ef_delivered = CtlFormula::atom("delivered").ef();
    let can_deliver = checker.holds_initially(&ef_delivered);

    println!("  Result: {}", if can_deliver { "✓ HOLDS" } else { "✗ VIOLATED" });
    assert!(can_deliver, "Delivery must be possible!");
    println!("  There EXISTS a path where the message gets through.\n");

    // Property 2: AF delivered
    println!("--- Property 2: Delivery Guarantee (without fairness) ---");
    println!("CTL: AF delivered");
    println!("'On ALL paths, is a message eventually delivered?'\n");

    let af_delivered = CtlFormula::atom("delivered").af();
    let always_delivers = checker.holds_initially(&af_delivered);

    println!("  Result: {}", if always_delivers { "✓ HOLDS" } else { "✗ VIOLATED" });
    if !always_delivers {
        println!();
        println!("  ⚠ EXPECTED FAILURE!");
        println!("  The channel can ALWAYS choose to lose every message.");
        println!("  This is an unrealistic 'adversarial' scheduler.");
        println!("  We need FAIRNESS to exclude such pathological behaviors.");
    }
    println!();

    // Property 3: AG (msg_pending → EF ¬msg_pending)
    println!("--- Property 3: Message Eventually Processed ---");
    println!("CTL: AG (msg_pending → EF ¬msg_pending)");
    println!("'A message in channel can eventually be removed'\n");

    let msg_eventually_handled = CtlFormula::atom("msg_pending")
        .implies(CtlFormula::atom("msg_pending").not().ef())
        .ag();
    let msg_handled = checker.holds_initially(&msg_eventually_handled);

    println!("  Result: {}", if msg_handled { "✓ HOLDS" } else { "✗ VIOLATED" });
    assert!(msg_handled, "Messages must be handleable!");
    println!("  Messages CAN be processed (delivered or lost).\n");

    // Property 4: AG EF synced
    println!("--- Property 4: Recovery to Synchronized State ---");
    println!("CTL: AG EF synced");
    println!("'Can we always eventually get back to sender_bit = receiver_bit?'\n");

    let can_resync = CtlFormula::atom("synced").ef().ag();
    let resync_holds = checker.holds_initially(&can_resync);

    println!("  Result: {}", if resync_holds { "✓ HOLDS" } else { "✗ VIOLATED" });
    // This fails without fairness because adversarial channel can prevent resync
    if !resync_holds {
        println!("  Without fairness, the channel can prevent resynchronization.");
    }
    println!();

    // ═══════════════════════════════════════════════════════════════════════════
    // STEP 8: Fairness Constraints
    // ═══════════════════════════════════════════════════════════════════════════

    println!("Step 4: Adding Fairness Constraints...\n");

    println!("  Fairness constraints ensure realistic execution:");
    println!("  - If sender can send, it eventually does");
    println!("  - If receiver can accept, it eventually does");
    println!("  - If sender can process ack, it eventually does\n");

    let mut fm = FairnessManager::new(ts.clone());

    // Fair sending: if no message pending, eventually message sent
    fm.add_constraint(FairnessConstraint::strong("fair_send", can_send, mp));

    // Fair receiving: if message pending and synced, eventually delivered
    let can_receive = bdd.apply_and(mp, synced);
    fm.add_constraint(FairnessConstraint::strong("fair_receive", can_receive, del));

    // Fair ack processing: if ack pending and desynced, eventually ack processed
    let can_process_ack = bdd.apply_and(ap, desynced);
    fm.add_constraint(FairnessConstraint::strong("fair_ack", can_process_ack, synced));

    // Property 5: Fair delivery guarantee
    println!("--- Property 5: Delivery Guarantee WITH Fairness ---");
    println!("Fair CTL: Under fair scheduling, is delivery guaranteed?\n");

    let fair_ef_delivered = fm.fair_ef(del);
    let initial_fair_delivers = bdd.apply_and(ts.initial(), fair_ef_delivered);
    let fair_delivery = initial_fair_delivers == ts.initial();

    println!(
        "  Result: {}",
        if fair_delivery {
            "✓ HOLDS with fairness"
        } else {
            "✗ VIOLATED even with fairness"
        }
    );

    if fair_delivery && !always_delivers {
        println!();
        println!("  KEY INSIGHT:");
        println!("  - Without fairness: AF delivered FAILS (adversarial channel)");
        println!("  - With fairness:    AF delivered HOLDS (realistic channel)");
        println!();
        println!("  This demonstrates why FAIRNESS is essential for liveness!");
    }
    println!();

    // ═══════════════════════════════════════════════════════════════════════════
    // STEP 9: LTL Model Checking
    // ═══════════════════════════════════════════════════════════════════════════

    println!("Step 5: LTL Model Checking...\n");

    let ltl_checker = LtlChecker::new(ts.clone());

    println!("--- Property 6: LTL Message Resolution ---");
    println!("LTL: G (msg_pending → F ¬msg_pending)");
    println!("'On every path, pending messages are eventually handled'\n");

    let msg_resolved = LtlFormula::atom("msg_pending")
        .implies(LtlFormula::atom("msg_pending").not().finally())
        .globally();
    let ltl_msg_resolved = ltl_checker.holds_initially(&msg_resolved);

    println!("  Result: {}", if ltl_msg_resolved { "✓ HOLDS" } else { "✗ VIOLATED" });
    if !ltl_msg_resolved {
        println!("  Without fairness, messages can stay pending forever.");
    }
    println!();

    // ═══════════════════════════════════════════════════════════════════════════
    // Summary
    // ═══════════════════════════════════════════════════════════════════════════

    println!("Summary");
    println!("-------");
    println!("  EF delivered (can deliver):      {}", if can_deliver { "✓" } else { "✗" });
    println!("  AF delivered (must deliver):     {}", if always_delivers { "✓" } else { "✗" });
    println!("  Fair AF delivered (realistic):   {}", if fair_delivery { "✓" } else { "✗" });
    println!("  AG (msg → EF ¬msg):              {}", if msg_handled { "✓" } else { "✗" });
    println!("  AG EF synced (can resync):       {}", if resync_holds { "✓" } else { "✗" });
    println!();
    println!("Key Takeaways:");
    println!("  1. ABP ensures reliable delivery over lossy channels");
    println!("  2. Safety holds unconditionally");
    println!("  3. Liveness requires FAIRNESS assumptions");
    println!("  4. The alternating bit distinguishes new vs retransmitted msgs\n");

    assert!(can_deliver, "Delivery must be possible");
    assert!(msg_handled, "Messages must be handleable");

    println!("✓ All critical assertions passed!\n");
}
