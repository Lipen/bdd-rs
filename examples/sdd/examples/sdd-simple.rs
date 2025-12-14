//! Simple SDD Example.
//!
//! Demonstrates the full range of SDD operations:
//! - Creating variables and formulas
//! - Boolean operations (AND, OR, XOR, IMPLIES, EQUIV, ITE)
//! - Satisfiability and validity checking
//! - Model counting
//! - Conditioning (restricting by literal)
//! - Quantification (existential and universal)
//! - Cubes and clauses
//! - DOT export for visualization
//!
//! Run with: `cargo run --example simple`

use sdd::SddManager;

fn main() {
    println!("═══ Sentential Decision Diagrams ═══\n");

    // Create an SDD manager with 4 variables.
    // The manager owns all SDD nodes and provides operations.
    let mgr = SddManager::new(4);

    // ────────────────────────────────────────────────────────────────────────
    // 1. VARIABLES
    // ────────────────────────────────────────────────────────────────────────

    println!("── 1. Variables ──\n");

    println!("Variables are 1-indexed: x₁, x₂, x₃, x₄");
    println!("Each var(i) returns an SddId — a lightweight handle to the SDD node.\n");

    let x1 = mgr.var(1);
    let x2 = mgr.var(2);
    let x3 = mgr.var(3);
    let x4 = mgr.var(4);

    println!("  x₁ = {}", mgr.display(x1));
    println!("  x₂ = {}", mgr.display(x2));
    println!("  x₃ = {}", mgr.display(x3));
    println!("  x₄ = {}", mgr.display(x4));
    println!();

    // ────────────────────────────────────────────────────────────────────────
    // 2. BOOLEAN OPERATIONS
    // ────────────────────────────────────────────────────────────────────────

    println!("── 2. Boolean Operations ──\n");

    println!("SDDs support all standard Boolean operations:\n");

    // Negation
    let not_x1 = mgr.neg(x1);
    println!("  ¬x₁           = {:16}  negation (O(1))", mgr.display(not_x1));

    // Conjunction
    let x1_and_x2 = mgr.and(x1, x2);
    println!("  x₁ ∧ x₂       = {:16}  conjunction", mgr.display(x1_and_x2));

    // Disjunction
    let x1_or_x2 = mgr.or(x1, x2);
    println!("  x₁ ∨ x₂       = {:16}  disjunction", mgr.display(x1_or_x2));

    // Exclusive OR
    let x1_xor_x2 = mgr.xor(x1, x2);
    println!("  x₁ ⊕ x₂       = {:16}  exclusive or", mgr.display(x1_xor_x2));

    // Implication
    let x1_impl_x2 = mgr.implies(x1, x2);
    println!("  x₁ → x₂       = {:16}  implication", mgr.display(x1_impl_x2));

    // Equivalence
    let x1_equiv_x2 = mgr.equiv(x1, x2);
    println!("  x₁ ↔ x₂       = {:16}  equivalence", mgr.display(x1_equiv_x2));

    // If-then-else
    let ite = mgr.ite(x1, x2, x3);
    println!("  ITE(x₁,x₂,x₃) = {:16}  if-then-else", mgr.display(ite));

    println!();

    // ────────────────────────────────────────────────────────────────────────
    // 3. COMPLEX FORMULA CONSTRUCTION
    // ────────────────────────────────────────────────────────────────────────

    println!("── 3. Complex Formula Construction ──\n");

    // Build f = (x₁ ∧ x₂) ∨ (x₃ ∧ x₄)
    let left = mgr.and(x1, x2);
    let right = mgr.and(x3, x4);
    let f = mgr.or(left, right);

    println!("Formula:  f = (x₁ ∧ x₂) ∨ (x₃ ∧ x₄)\n");
    println!("  SDD representation: {}", mgr.display(f));
    println!("  Size:               {} nodes", mgr.size(f));
    println!();

    // Using and_all and or_all for multiple operands
    println!("Using and_all/or_all for multiple operands:\n");

    let clause1 = mgr.clause([1, 2, 3]); // x₁ ∨ x₂ ∨ x₃
    let clause2 = mgr.clause([-1, -2, 4]); // ¬x₁ ∨ ¬x₂ ∨ x₄
    let cnf = mgr.and_all([clause1, clause2]);

    println!("  Clause 1: x₁ ∨ x₂ ∨ x₃");
    println!("  Clause 2: ¬x₁ ∨ ¬x₂ ∨ x₄");
    println!("  CNF = Clause1 ∧ Clause2");
    println!("  Size: {} nodes, #SAT: {}", mgr.size(cnf), mgr.model_count(cnf));
    println!();

    // ────────────────────────────────────────────────────────────────────────
    // 4. QUERIES: SAT, VALIDITY, MODEL COUNTING
    // ────────────────────────────────────────────────────────────────────────

    println!("── 4. Queries: Satisfiability, Validity, Model Counting ──\n");

    println!("Checking properties of f = (x₁ ∧ x₂) ∨ (x₃ ∧ x₄):\n");

    println!("  Property            Result");
    println!("  ──────────────────  ─────────");
    println!("  Satisfiable (SAT)   {}", yn(mgr.is_satisfiable(f)));
    println!("  Valid (tautology)   {}", yn(mgr.is_valid(f)));
    println!("  Unsatisfiable       {}", yn(mgr.is_false(f)));
    println!("  Model count         {}", mgr.model_count(f));
    println!();

    println!("Model count breakdown:");
    println!("  • x₁=1, x₂=1, any x₃,x₄       → 4 assignments");
    println!("  • x₁=0 or x₂=0, x₃=1, x₄=1   → 3 more assignments");
    println!("  • Total: 7 satisfying assignments out of 16");
    println!();

    // ────────────────────────────────────────────────────────────────────────
    // 5. SATISFYING ASSIGNMENTS
    // ────────────────────────────────────────────────────────────────────────

    println!("── 5. Finding Satisfying Assignments ──\n");

    println!("any_sat(f) finds one satisfying assignment:\n");

    if let Some(assignment) = mgr.any_sat(f) {
        print!("  Model: {{ ");
        for lit in &assignment {
            if *lit > 0 {
                print!("x{}=T ", lit);
            } else {
                print!("x{}=F ", -lit);
            }
        }
        println!("}}\n");

        // Verify this is indeed a model
        let model_sdd = mgr.cube(assignment.clone());
        let check = mgr.and(f, model_sdd);
        println!("  Verification: f ∧ model = {} ✓", yn(mgr.is_satisfiable(check)));
    }
    println!();

    // ────────────────────────────────────────────────────────────────────────
    // 6. CONDITIONING (RESTRICTION BY LITERAL)
    // ────────────────────────────────────────────────────────────────────────

    println!("── 6. Conditioning (Restriction) ──\n");

    println!("Conditioning restricts an SDD by setting a variable to T or F.\n");
    println!("f = (x₁ ∧ x₂) ∨ (x₃ ∧ x₄)\n");

    // Condition on x₁ = true
    let f_x1_true = mgr.condition(f, 1); // positive literal
    println!("  f|x₁=T = {}", mgr.display(f_x1_true));
    println!("         = x₂ ∨ (x₃ ∧ x₄)");
    println!("         #SAT = {}", mgr.model_count(f_x1_true));
    println!();

    // Condition on x₁ = false
    let f_x1_false = mgr.condition(f, -1); // negative literal
    println!("  f|x₁=F = {}", mgr.display(f_x1_false));
    println!("         = x₃ ∧ x₄");
    println!("         #SAT = {}", mgr.model_count(f_x1_false));
    println!();

    // Chain conditioning
    let f_x1t_x3t = mgr.condition(mgr.condition(f, 1), 3);
    println!("  f|x₁=T,x₃=T = {}", mgr.display(f_x1t_x3t));
    println!("              #SAT = {}", mgr.model_count(f_x1t_x3t));
    println!();

    // ────────────────────────────────────────────────────────────────────────
    // 7. QUANTIFICATION
    // ────────────────────────────────────────────────────────────────────────

    println!("── 7. Quantification (Existential & Universal) ──\n");

    println!("Existential: ∃x.f = f|x=T ∨ f|x=F  (is there an x that makes f true?)");
    println!("Universal:   ∀x.f = f|x=T ∧ f|x=F  (is f true for all x?)\n");

    println!("f = (x₁ ∧ x₂) ∨ (x₃ ∧ x₄)\n");

    // Existential quantification
    let exists_x1 = mgr.exists(f, 1);
    println!("  ∃x₁.f = {}", mgr.display(exists_x1));
    println!("        = x₂ ∨ (x₃ ∧ x₄)");
    println!("        #SAT = {} (over x₂,x₃,x₄)", mgr.model_count(exists_x1));
    println!();

    // Existentially quantify multiple variables
    let exists_x1_x2 = mgr.exists(mgr.exists(f, 1), 2);
    println!("  ∃x₁.∃x₂.f = {}", mgr.display(exists_x1_x2));
    println!("            = ⊤ ∨ (x₃ ∧ x₄) = ⊤");
    println!("            (if x₁=x₂=T, formula is true regardless of x₃,x₄)");
    println!();

    // Universal quantification
    let forall_x1 = mgr.forall(f, 1);
    println!("  ∀x₁.f = {}", mgr.display(forall_x1));
    println!("        = (x₂ ∧ (x₃ ∧ x₄))");
    println!("        (must satisfy both branches)");
    println!("        #SAT = {}", mgr.model_count(forall_x1));
    println!();

    // ────────────────────────────────────────────────────────────────────────
    // 8. CUBES AND CLAUSES
    // ────────────────────────────────────────────────────────────────────────

    println!("── 8. Cubes and Clauses ──\n");

    println!("Cube:   conjunction of literals (represents one or more assignments)");
    println!("Clause: disjunction of literals (constraint that must be satisfied)\n");

    // Cube example
    let cube = mgr.cube([1, -2, 3]);
    println!("  Cube [1,-2,3] = x₁ ∧ ¬x₂ ∧ x₃");
    println!("    Represents assignments where x₁=T, x₂=F, x₃=T, x₄ free");
    println!("    #SAT = {} (x₄ can be T or F)", mgr.model_count(cube));
    println!();

    // Clause example
    let clause = mgr.clause([1, -2, 3]);
    println!("  Clause [1,-2,3] = x₁ ∨ ¬x₂ ∨ x₃");
    println!("    Satisfied unless x₁=F, x₂=T, x₃=F");
    println!("    #SAT = {} (only 2 failing assignments × 2 for x₄)", mgr.model_count(clause));
    println!();

    // CNF formula (conjunction of clauses)
    let c1 = mgr.clause([1, 2]); // x₁ ∨ x₂
    let c2 = mgr.clause([-1, 3]); // ¬x₁ ∨ x₃
    let c3 = mgr.clause([-2, -3]); // ¬x₂ ∨ ¬x₃
    let cnf_formula = mgr.and_all([c1, c2, c3]);

    println!("  CNF: (x₁ ∨ x₂) ∧ (¬x₁ ∨ x₃) ∧ (¬x₂ ∨ ¬x₃)");
    println!("    #SAT = {}", mgr.model_count(cnf_formula));
    println!();

    // ────────────────────────────────────────────────────────────────────────
    // 9. TAUTOLOGIES AND CONTRADICTIONS
    // ────────────────────────────────────────────────────────────────────────

    println!("── 9. Boolean Laws: Tautologies and Contradictions ──\n");

    // Excluded middle: x ∨ ¬x = ⊤
    let excluded_middle = mgr.or(x1, mgr.neg(x1));
    println!("Law of Excluded Middle:");
    println!(
        "  x₁ ∨ ¬x₁ = {} {}",
        mgr.display(excluded_middle),
        check(mgr.is_true(excluded_middle))
    );
    println!();

    // Non-contradiction: x ∧ ¬x = ⊥
    let non_contradiction = mgr.and(x1, mgr.neg(x1));
    println!("Law of Non-Contradiction:");
    println!(
        "  x₁ ∧ ¬x₁ = {} {}",
        mgr.display(non_contradiction),
        check(mgr.is_false(non_contradiction))
    );
    println!();

    // De Morgan's laws
    let lhs1 = mgr.neg(mgr.and(x1, x2));
    let rhs1 = mgr.or(mgr.neg(x1), mgr.neg(x2));
    println!("De Morgan's Law 1:");
    println!("  ¬(x₁ ∧ x₂) ↔ (¬x₁ ∨ ¬x₂) {}", check(mgr.is_true(mgr.equiv(lhs1, rhs1))));
    println!();

    let lhs2 = mgr.neg(mgr.or(x1, x2));
    let rhs2 = mgr.and(mgr.neg(x1), mgr.neg(x2));
    println!("De Morgan's Law 2:");
    println!("  ¬(x₁ ∨ x₂) ↔ (¬x₁ ∧ ¬x₂) {}", check(mgr.is_true(mgr.equiv(lhs2, rhs2))));
    println!();

    // ────────────────────────────────────────────────────────────────────────
    // 10. DOT EXPORT FOR VISUALIZATION
    // ────────────────────────────────────────────────────────────────────────

    println!("── 10. Graphviz DOT Export ──\n");

    println!("SDDs can be exported to DOT format for visualization.\n");

    let simple = mgr.and(x1, mgr.or(x2, x3));
    let dot = mgr.to_dot(simple);

    println!("Formula: x₁ ∧ (x₂ ∨ x₃)\n");

    // Write DOT to temp file
    let dot_path = "/tmp/sdd_example.dot";
    std::fs::write(dot_path, &dot).expect("Failed to write DOT file");

    println!("DOT output written to: {}", dot_path);
    println!("  Lines: {}", dot.lines().count());
    println!();
    println!("Render with: dot -O -Tsvg {}", dot_path);
    println!();

    // ────────────────────────────────────────────────────────────────────────
    // 11. MANAGER STATISTICS
    // ────────────────────────────────────────────────────────────────────────

    println!("── 11. Manager Statistics ──\n");

    let stats = mgr.stats();
    let hit_rate = if stats.apply_calls > 0 {
        100.0 * stats.cache_hits as f64 / stats.apply_calls as f64
    } else {
        0.0
    };

    println!("Metric              Value");
    println!("──────────────────  ──────────");
    println!("Variables           {:>10}", stats.num_vars);
    println!("Total nodes         {:>10}", stats.num_nodes);
    println!("Apply operations    {:>10}", stats.apply_calls);
    println!("Cache hits          {:>10}", stats.cache_hits);
    println!("Cache hit rate      {:>9.1}%", hit_rate);
    println!();

    // ────────────────────────────────────────────────────────────────────────
    // SUMMARY
    // ────────────────────────────────────────────────────────────────────────

    println!("─── Summary ───\n");
    println!("SDDs provide:");
    println!("  • Canonical representation of Boolean functions");
    println!("  • Polynomial-time ∧, ∨, ¬, model counting");
    println!("  • Efficient conditioning and quantification");
    println!("  • Foundation for knowledge compilation");
    println!();

    println!("Done.");
}

// ─── Helpers ─────────────────────────────────────────────────────────────────

/// Helper: yes/no with checkmark.
fn yn(b: bool) -> &'static str {
    if b {
        "✓ yes"
    } else {
        "✗ no"
    }
}

/// Helper: checkmark or cross.
fn check(b: bool) -> &'static str {
    if b {
        "✓"
    } else {
        "✗"
    }
}
