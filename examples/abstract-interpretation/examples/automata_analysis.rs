//! Automata Domain Example
//!
//! This example demonstrates how to use the `AutomataDomain` to analyze string properties.
//! We will construct automata representing different string formats (e.g., identifiers, numbers)
//! and perform abstract operations like join and meet to analyze potential string values.

use abstract_interpretation::*;

fn main() {
    println!("=== Automata Domain Analysis Example ===");

    let domain = AutomataDomain;

    // 1. Define basic character classes
    let digit = CharClass::range('0', '9');
    let alpha_lower = CharClass::range('a', 'z');
    let alpha_upper = CharClass::range('A', 'Z');
    let alpha = alpha_lower.or(&alpha_upper);
    let alphanumeric = alpha.or(&digit);
    let underscore = CharClass::single('_');
    let identifier_char = alphanumeric.or(&underscore);

    // 2. Construct an automaton for valid identifiers: [a-zA-Z_][a-zA-Z0-9_]*
    println!("\nConstructing Identifier Automaton...");
    let mut nfa_ident = SymbolicNFA::new();
    let start = nfa_ident.start; // state 0
    let body = nfa_ident.add_state(true); // state 1 (accepting)

    // Transition: start --[a-zA-Z_]--> body
    nfa_ident.add_transition(start, alpha.or(&underscore), body);
    // Transition: body --[a-zA-Z0-9_]--> body
    nfa_ident.add_transition(body, identifier_char.clone(), body);

    let dfa_ident = nfa_ident.determinize();
    println!("Identifier DFA has {} states", dfa_ident.states);
    println!("DFA Transitions: {:?}", dfa_ident.transitions);

    // Test some strings
    assert!(dfa_ident.accepts("my_var"));
    assert!(dfa_ident.accepts("_private"));
    assert!(dfa_ident.accepts("var123"));
    assert!(!dfa_ident.accepts("123var")); // Starts with digit
    println!("- 'my_var' accepted: {}", dfa_ident.accepts("my_var"));
    println!("- '123var' accepted: {}", dfa_ident.accepts("123var"));

    // 3. Construct an automaton for integer literals: [0-9]+
    println!("\nConstructing Integer Automaton...");
    let mut nfa_int = SymbolicNFA::new();
    let start = nfa_int.start;
    let body = nfa_int.add_state(true);

    nfa_int.add_transition(start, digit.clone(), body);
    nfa_int.add_transition(body, digit.clone(), body);

    let dfa_int = nfa_int.determinize();
    println!("Integer DFA has {} states", dfa_int.states);
    assert!(dfa_int.accepts("123"));
    assert!(!dfa_int.accepts("12a"));

    // 4. Analyze a scenario:
    // Let's say we have a variable `x` that can be either an identifier OR an integer.
    // We want to compute the abstract state for `x`.
    println!("\nComputing Abstract State for (Identifier | Integer)...");

    let state_x = domain.join(&dfa_ident, &dfa_int);

    println!("Joined DFA has {} states", state_x.states);
    println!("- 'var1' accepted: {}", state_x.accepts("var1"));
    println!("- '99' accepted: {}", state_x.accepts("99"));
    println!("- '$invalid' accepted: {}", state_x.accepts("$invalid"));

    assert!(state_x.accepts("var1"), "Union should accept identifier 'var1'");
    assert!(state_x.accepts("99"), "Union should accept integer '99'");
    assert!(!state_x.accepts("$invalid"), "Union should reject invalid string '$invalid'");

    // 5. Intersection (Meet)
    // What strings are BOTH identifiers AND integers?
    // Ideally this should be empty because identifiers can't start with a digit,
    // and integers must consist only of digits.
    println!("\nComputing Intersection (Identifier & Integer)...");
    let intersection = domain.meet(&dfa_ident, &dfa_int);

    assert!(
        domain.is_bottom(&intersection),
        "Intersection of disjoint languages should be empty"
    );
    println!("Intersection is empty (Bottom) - Verified.");

    // 6. Subset Check (Le)
    println!("\nChecking Subset Relationships...");
    // "var1" is a specific identifier. Let's make a singleton DFA.
    let mut nfa_var1 = SymbolicNFA::new();
    let s0 = 0;
    let s1 = nfa_var1.add_state(false);
    let s2 = nfa_var1.add_state(false);
    let s3 = nfa_var1.add_state(false);
    let s4 = nfa_var1.add_state(true);

    nfa_var1.add_transition(s0, CharClass::single('v'), s1);
    nfa_var1.add_transition(s1, CharClass::single('a'), s2);
    nfa_var1.add_transition(s2, CharClass::single('r'), s3);
    nfa_var1.add_transition(s3, CharClass::single('1'), s4);

    let dfa_var1 = nfa_var1.determinize();

    let is_subset = domain.le(&dfa_var1, &dfa_ident);
    println!("Is 'var1' singleton a subset of Identifiers? {}", is_subset);
    assert!(is_subset);

    let is_subset_int = domain.le(&dfa_var1, &dfa_int);
    println!("Is 'var1' singleton a subset of Integers? {}", is_subset_int);
    assert!(!is_subset_int);

    println!("\nAnalysis Complete.");
}
