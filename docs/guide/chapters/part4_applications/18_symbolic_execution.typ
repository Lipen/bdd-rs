#import "../../theme.typ": *

= Symbolic Execution and Program Analysis <ch-symbolic-execution>

Symbolic execution flips the script on program testing: instead of feeding concrete inputs and watching what happens, we feed *symbols* and track *all* possible behaviors at once.
The key challenge? A program with just 32 `if` statements has $2^(32)$ paths.

BDDs cut through this explosion.
By representing path conditions --- the Boolean constraints determining which paths are feasible --- as BDDs, we can reason about exponentially many paths without enumerating them.

== Path Conditions as BDDs

In symbolic execution, each program path has a *path condition*: a Boolean formula over input symbols that is satisfied exactly when execution takes that path.

#figure(
  cetz.canvas(length: 1cm, {
    import cetz.draw: *

    content((6, 8.5), text(weight: "bold", size: 1em)[Path Conditions in a Program])

    // Code block
    rect((0, 4), (4, 8), fill: colors.bg-code.lighten(20%), stroke: 1pt + colors.line, radius: 4pt)
    content((0.5, 7.5), text(size: 0.8em)[`if (x > 0)`], anchor: "west")
    content((0.5, 6.8), text(size: 0.8em)[`  if (y < 10)`], anchor: "west")
    content((0.5, 6.1), text(size: 0.8em)[`    ... Path A`], anchor: "west")
    content((0.5, 5.4), text(size: 0.8em)[`  else`], anchor: "west")
    content((0.5, 4.7), text(size: 0.8em)[`    ... Path B`], anchor: "west")

    // Path tree
    content((9, 7.8), text(size: 0.9em)[Entry], name: "entry")

    content((7, 6), text(size: 0.8em)[$x > 0$], name: "cond1")
    line((9, 7.5), (7.3, 6.3), stroke: 1pt + colors.line, mark: (end: ">"))

    content((11, 6), text(size: 0.7em, fill: colors.text-muted)[$x <= 0$], name: "false1")
    line((9, 7.5), (10.7, 6.3), stroke: 1pt + colors.text-muted.lighten(30%), mark: (end: ">"))

    content((6, 4.2), text(size: 0.8em)[$y < 10$], name: "cond2")
    line((7, 5.7), (6.3, 4.5), stroke: 1pt + colors.line, mark: (end: ">"))

    content((8, 4.2), text(size: 0.7em, fill: colors.text-muted)[$y >= 10$], name: "false2")
    line((7, 5.7), (7.7, 4.5), stroke: 1pt + colors.text-muted.lighten(30%), mark: (end: ">"))

    // Path conditions
    rect((4.5, 2), (7.5, 3.5), fill: colors.box-insight.lighten(30%), stroke: 1pt + colors.info, radius: 4pt)
    content((6, 3.1), text(size: 0.8em, weight: "semibold")[Path A])
    content((6, 2.5), text(size: 0.7em)[$x > 0 and y < 10$])

    rect(
      (8, 2),
      (11, 3.5),
      fill: colors.box-example.lighten(40%),
      stroke: 1pt + colors.success.lighten(20%),
      radius: 4pt,
    )
    content((9.5, 3.1), text(size: 0.8em, weight: "semibold")[Path B])
    content((9.5, 2.5), text(size: 0.7em)[$x > 0 and y >= 10$])

    line((6, 3.9), (6, 3.6), stroke: 1pt + colors.line, mark: (end: ">"))
  }),
  caption: [Each path through the program has a corresponding path condition.],
)

#insight-box[
  BDDs for path conditions enable:
  - *Feasibility checking*: Is a path reachable? (SAT check)
  - *Path merging*: Combine paths with same effect (OR)
  - *Condition refinement*: Add constraints along execution (AND)
  - *Complement paths*: What inputs avoid this path? (NOT)
]

== Control Flow Encoding

We encode program structure as Boolean constraints:

#example-box(title: "Boolean Program Encoding")[
  For each program point $p_i$ and branch condition $c_j$:
  - Variable $"at"_i$: "execution is at point $i$"
  - Transition: $"at"_(i+1) <-> "at"_i and c_j$ (if branch taken)

  The BDD $f$ satisfying $"at"_"error"$ represents all inputs reaching an error state.
]

#figure(
  cetz.canvas(length: 1cm, {
    import cetz.draw: *

    content((6, 7.5), text(weight: "bold", size: 1em)[Control Flow as BDD Constraints])

    // CFG nodes
    rect(
      (1, 5.5),
      (3, 6.5),
      fill: colors.box-definition.lighten(40%),
      stroke: 1pt + colors.primary.lighten(20%),
      radius: 4pt,
      name: "n1",
    )
    content((2, 6), text(size: 0.8em)[$p_1$: entry])

    rect((1, 3.5), (3, 4.5), fill: colors.bg-code, stroke: 1pt + colors.line, radius: 4pt, name: "n2")
    content((2, 4), text(size: 0.8em)[$p_2$: $x > 0$?])

    rect(
      (-0.5, 1.5),
      (1.5, 2.5),
      fill: colors.box-example.lighten(40%),
      stroke: 1pt + colors.success.lighten(20%),
      radius: 4pt,
      name: "n3",
    )
    content((0.5, 2), text(size: 0.8em)[$p_3$])

    rect(
      (2.5, 1.5),
      (4.5, 2.5),
      fill: colors.box-warning.lighten(40%),
      stroke: 1pt + colors.warning.lighten(20%),
      radius: 4pt,
      name: "n4",
    )
    content((3.5, 2), text(size: 0.8em)[$p_4$])

    line((2, 5.4), (2, 4.6), stroke: 1pt + colors.line, mark: (end: ">"))
    line((1.5, 3.4), (0.8, 2.6), stroke: 1pt + colors.success)
    content((0.5, 3.1), text(size: 0.7em, fill: colors.success)[T])
    line((2.5, 3.4), (3.2, 2.6), stroke: 1pt + colors.warning)
    content((3.5, 3.1), text(size: 0.7em, fill: colors.warning)[F])

    // BDD encoding
    rect((6, 2), (11.5, 7), fill: colors.bg-code.lighten(30%), stroke: 1pt + colors.line, radius: 4pt)
    content((8.75, 6.5), text(weight: "semibold", size: 0.9em)[BDD Constraints])
    content((8.75, 5.6), text(size: 0.8em)[`at_2 ↔ at_1`])
    content((8.75, 4.8), text(size: 0.8em)[`at_3 ↔ at_2 ∧ (x > 0)`])
    content((8.75, 4.0), text(size: 0.8em)[`at_4 ↔ at_2 ∧ ¬(x > 0)`])
    content((8.75, 3.0), text(size: 0.7em, fill: colors.text-muted)[Reachability = SAT(at_target)])
  }),
  caption: [Control flow graph encoded as BDD constraints.],
)

== Path Merging

A key advantage of BDD-based analysis: *merge* paths that reach the same point.

#figure(
  cetz.canvas(length: 1cm, {
    import cetz.draw: *

    content((6, 7), text(weight: "bold", size: 1em)[Path Explosion vs. Path Merging])

    // Left side: path explosion
    content((2, 6), text(size: 0.9em, weight: "semibold")[Enumerate Paths])

    for i in range(4) {
      let y = 4.5 - i * 0.8
      rect(
        (0.5, y - 0.25),
        (3.5, y + 0.25),
        fill: colors.box-warning.lighten(60%),
        stroke: 0.5pt + colors.warning.lighten(20%),
        radius: 2pt,
      )
      content((2, y), text(size: 0.7em)[Path #str(i + 1)])
    }
    content((2, 1.5), text(size: 0.7em, fill: colors.text-muted)[...exponential])
    content((2, 0.8), text(size: 1.5em, fill: colors.warning)[⚠])

    // Arrow
    content((5.5, 3.5), text(size: 1.5em)[→])

    // Right side: BDD merged
    content((9, 6), text(size: 0.9em, weight: "semibold")[BDD Merge])

    rect((7, 2), (11, 5), fill: colors.box-example.lighten(40%), stroke: 2pt + colors.success, radius: 4pt)
    content((9, 4.3), text(size: 0.8em, weight: "semibold")[Single BDD])
    content((9, 3.5), text(size: 0.8em)[Represents all])
    content((9, 2.8), text(size: 0.8em)[reachable states])
    content((9, 2.2), text(size: 1em, fill: colors.success)[✓])
  }),
  caption: [BDDs merge exponentially many paths into a single symbolic representation.],
)

#warning-box(title: "When Merging Loses Information")[
  Path merging is *sound* but may lose *precision*.
  If you need to distinguish paths (e.g., for debugging), track path conditions separately.
  The trade-off: precision vs. scalability.
]

== Abstract Interpretation with BDDs

BDDs serve as an *abstract domain* for path-sensitive analysis:

#definition(title: "BDD Abstract Domain")[
  A program state is abstracted as:
  - *Path condition* (BDD): Which inputs reach this point
  - *Value constraints* (another domain): What values variables hold

  Abstract operations:
  - *Branch*: Conjoin branch condition to path BDD
  - *Join*: Disjoin (OR) path BDDs at merge points
  - *Widen*: For loops, extrapolate to fixed point
]

#comparison-table(
  [*Analysis Type*],
  [*Path Sensitivity*],
  [*BDD Role*],
  [Flow-insensitive],
  [None],
  [Not needed],
  [Flow-sensitive],
  [Statement order],
  [Track reaching definitions],
  [Path-sensitive],
  [Branch conditions],
  [BDDs track full path conditions],
  [Context-sensitive],
  [Call sites],
  [BDDs encode calling context],
)

== Test Case Generation

BDDs enable systematic test generation:

```rust
// Generate test inputs from path condition BDD
fn generate_tests(bdd: &Bdd, path_condition: Ref, input_vars: &[Var]) -> Vec<TestInput> {
    let mut tests = Vec::new();

    // Each satisfying assignment is a test case
    for assignment in bdd.all_sat(path_condition) {
        let test = TestInput {
            values: input_vars.iter()
                .map(|&v| assignment[v])
                .collect(),
        };
        tests.push(test);
    }

    tests
}

// Incremental: find input for uncovered path
fn cover_new_path(bdd: &Bdd, uncovered: Ref, covered: Ref) -> Option<TestInput> {
    // Find path not yet covered
    let new_path = bdd.and(uncovered, bdd.not(covered));
    if bdd.is_zero(new_path) {
        return None;  // All paths covered!
    }

    // Get one satisfying assignment
    bdd.any_sat(new_path).map(|a| a.into())
}
```

#insight-box[
  For *path coverage*, generate one test per BDD path.
  For *branch coverage*, generate tests that flip each branch.
  BDDs make this systematic: enumerate paths, sample representative inputs.
]

== Concolic Testing

*Concolic* (concrete + symbolic) execution combines:
- *Concrete execution*: Run on actual inputs
- *Symbolic tracking*: Build path condition BDD

#algorithm(title: "Concolic Testing Loop")[
  ```
  ConcolisTest(program):
    worklist = {random_input}
    covered = ∅ (empty BDD)

    while worklist not empty:
      input = worklist.pop()
      (path_cond, _) = execute_symbolically(program, input)

      // Mark this path as covered
      covered = covered OR path_cond

      // Generate inputs for alternative branches
      for branch in path_cond.branches():
        // Negate this branch, keep prefix
        alt_cond = prefix(branch) AND NOT(branch)
        if alt_cond SAT:
          new_input = solve(alt_cond)
          worklist.add(new_input)
  ```
]

#figure(
  cetz.canvas(length: 1cm, {
    import cetz.draw: *

    content((6, 6.5), text(weight: "bold", size: 1em)[Concolic Testing: Negate and Explore])

    // Original path
    rect(
      (1, 4),
      (4, 5.5),
      fill: colors.box-definition.lighten(40%),
      stroke: 1pt + colors.primary.lighten(20%),
      radius: 4pt,
    )
    content((2.5, 5.1), text(size: 0.8em, weight: "semibold")[Original Path])
    content((2.5, 4.4), text(size: 0.7em)[$c_1 and c_2 and c_3$])

    // Negated paths
    rect(
      (6, 4.8),
      (10, 5.8),
      fill: colors.box-example.lighten(40%),
      stroke: 1pt + colors.success.lighten(20%),
      radius: 4pt,
    )
    content((8, 5.5), text(size: 0.8em)[$not c_1$])
    content((8, 5.1), text(size: 0.7em, fill: colors.text-muted)[Negate first])

    rect(
      (6, 3.3),
      (10, 4.3),
      fill: colors.box-example.lighten(40%),
      stroke: 1pt + colors.success.lighten(20%),
      radius: 4pt,
    )
    content((8, 4), text(size: 0.8em)[$c_1 and not c_2$])
    content((8, 3.6), text(size: 0.7em, fill: colors.text-muted)[Negate second])

    rect(
      (6, 1.8),
      (10, 2.8),
      fill: colors.box-example.lighten(40%),
      stroke: 1pt + colors.success.lighten(20%),
      radius: 4pt,
    )
    content((8, 2.5), text(size: 0.8em)[$c_1 and c_2 and not c_3$])
    content((8, 2.1), text(size: 0.7em, fill: colors.text-muted)[Negate third])

    // Arrows
    line((4.2, 5.3), (5.8, 5.5), stroke: 1pt + colors.line, mark: (end: ">"))
    line((4.2, 4.8), (5.8, 3.8), stroke: 1pt + colors.line, mark: (end: ">"))
    line((4.2, 4.3), (5.8, 2.3), stroke: 1pt + colors.line, mark: (end: ">"))
  }),
  caption: [Concolic testing systematically explores alternative paths by negating branch conditions.],
)

== Security Analysis

BDDs excel at security-relevant program analysis:

#example-box(title: "Taint Analysis with BDDs")[
  Track information flow from untrusted sources:
  - Variable $"tainted"_x$: "variable $x$ holds untrusted data"
  - Propagation: $"tainted"_y <- "tainted"_y or "tainted"_x$ (on `y = f(x)`)
  - Violation: $"tainted"_z and "sink"_z$ (tainted data reaches sensitive sink)

  The BDD for the violation condition represents all inputs causing a security bug.
]

#info-box(title: "Applications in Security")[
  - *SQL injection*: Taint user input, check query strings
  - *Buffer overflow*: Track array bounds symbolically
  - *Information leak*: Path condition reveals secret bits?
  - *Access control*: Encode policy, verify enforcement
]

== Practical Considerations

#comparison-table(
  [*Challenge*],
  [*Mitigation*],
  [BDD blowup on complex conditions],
  [Abstract predicates, simplify constraints],
  [Floating-point arithmetic],
  [Interval abstraction, not BDDs],
  [Pointer aliasing],
  [Points-to analysis pre-pass],
  [Loops],
  [Widening, bounded unrolling],
  [Scalability],
  [Modular analysis, summaries],
)

BDD-based symbolic execution shines when:
- Path conditions are Boolean or small integer comparisons
- You need *complete* coverage analysis (all paths)
- The same analysis runs on multiple inputs/programs
