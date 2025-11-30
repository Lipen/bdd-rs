#import "../../theme.typ": *

= BDD Definition and Structure <ch-bdd-definition>

In the previous chapter, we saw that Boolean functions can be represented in many ways.
Shannon expansion gives us a recursive decomposition, but naively applying it yields exponential-size decision trees.

The breakthrough insight of BDDs is simple yet profound: *share identical substructures*.
By merging duplicate subtrees, we transform an exponential tree into a compact directed acyclic graph (DAG).

== From Decision Trees to Decision Diagrams

Let's trace the evolution from trees to diagrams.
This progression reveals why BDDs have the properties they do.

=== Decision Trees

A *decision tree* for a Boolean function $f(x_1, ..., x_n)$ is a rooted binary tree where:
- Each *internal node* is labeled with a variable $x_i$
- Each internal node has two children: *low* (for $x_i = 0$) and *high* (for $x_i = 1$)
- Each *leaf* is labeled with a Boolean constant ($0$ or $1$)

To evaluate the function on an assignment, we start at the root and follow edges based on variable values until reaching a leaf.
The leaf's label gives the function value.

#example-box(title: "Decision Tree for Majority")[
  Consider the majority function $"Maj"(x, y, z) = (x and y) or (y and z) or (x and z)$, which outputs $1$ when at least two inputs are $1$.

  A decision tree testing variables in order $x, y, z$ has:
  - Root tests $x$
  - Second level tests $y$ (two nodes)
  - Third level tests $z$ (four nodes)
  - Eight leaves with values based on majority

  Even this simple function requires $2^3 - 1 = 7$ internal nodes plus $8$ leaves.
]

The problem is clear: a decision tree for $n$ variables has up to $2^n$ leaves.
This exponential growth makes decision trees impractical for functions with many variables.

=== The Key Insight: Structure Sharing

The breakthrough comes from observing that decision trees contain redundancy.
Many subtrees compute the *same* subfunction and could be merged.

Consider evaluating $"Maj"(x, y, z)$ when we have already fixed $x = 0$ and $y = 1$.
The remaining function is just $z$.
Now consider fixing $x = 1$ and $y = 0$ --- again, the remaining function is $z$.
These two subtrees are *isomorphic*; they compute the same thing.

#insight-box[
  By merging isomorphic subtrees, we transform a tree into a DAG.
  The more structure a function has, the more sharing is possible.
]

=== From Tree to DAG

The transformation from decision tree to decision diagram proceeds bottom-up:
+ Start with a decision tree
+ Identify leaves with the same value and merge them (yielding just two terminal nodes: $0$ and $1$)
+ Identify internal nodes with the same variable and same children --- merge them
+ Repeat until no more merging is possible

This process is called *reduction*, and the resulting structure is a Binary Decision Diagram.

== Binary Decision Diagrams

We now give the formal definition of BDDs and establish notation used throughout this guide.

#definition(title: "Binary Decision Diagram")[
  A *Binary Decision Diagram (BDD)* is a rooted directed acyclic graph $G = (V, E)$ where:
  - $V = V_T union V_D$ partitions into *terminal* and *decision* nodes
  - *Terminal nodes* $V_T = {0, 1}$ have no outgoing edges
  - Each *decision node* $v in V_D$ is labeled with variable $"var"(v) in {x_1, ..., x_n}$ and has exactly two outgoing edges:
    - $"low"(v) in V$: the *low child* (taken when $"var"(v) = 0$)
    - $"high"(v) in V$: the *high child* (taken when $"var"(v) = 1$)
  - There is a distinguished *root node* $r in V$
]

#definition(title: "Semantics of BDDs")[
  A BDD with root $r$ represents a Boolean function $f_r : BB^n -> BB$ defined recursively:
  $
    f_v (bold(x)) = cases(
      0 & "if" v = 0,
      1 & "if" v = 1,
      (overline(x_i) and f_("low"(v))(bold(x))) or (x_i and f_("high"(v))(bold(x))) & "if" "var"(v) = x_i
    )
  $
  This is precisely Shannon expansion: $f = overline(x_i) dot f|_(x_i=0) + x_i dot f|_(x_i=1)$.
]

=== Graphical Conventions

Throughout this guide, we draw BDDs using standard conventions:
- *Decision nodes*: Circles labeled with variable names
- *Terminal nodes*: Squares labeled $0$ or $1$ (sometimes drawn as $bot$ and $top$)
- *High edges*: Solid lines (taken when variable is $1$)
- *Low edges*: Dashed lines (taken when variable is $0$)
- Variables at the same *level* are drawn at the same vertical position

== Ordered BDDs (OBDDs)

BDDs become much more useful when we impose an ordering constraint on variables.

#definition(title: "Variable Ordering")[
  A *variable ordering* is a total order $pi$ on the variables ${x_1, ..., x_n}$.
  We write $x_i scripts(<)_pi x_j$ to mean $x_i$ comes before $x_j$ in the ordering.
]

#definition(title: "Ordered BDD")[
  A BDD is *ordered* (OBDD) with respect to variable ordering $pi$ if on every path from the root to a terminal, variables are encountered in increasing order according to $pi$.

  Formally: for every decision node $v$ with decision child $u$ (either low or high), if both are decision nodes, then $"var"(v) scripts(<)_pi "var"(u)$.
]

The ordering constraint has profound implications:
- Variables can be *skipped* on a path (if the function does not depend on them in that branch)
- Variables can *never repeat* on a path
- The *same* variable appears at the *same level* throughout the BDD

#info-box(title: "Why Ordering Matters")[
  Without ordering, two BDDs for the same function could have completely different structures, making comparison difficult.
  Ordering is the first step toward canonicity.
]

=== The Impact of Variable Ordering

Different orderings can yield dramatically different BDD sizes for the same function.

#example-box(title: "Ordering Impact")[
  Consider $f = (x_1 and y_1) or (x_2 and y_2)$, which is true when at least one $(x_i, y_i)$ pair is both true.

  With ordering $x_1 < y_1 < x_2 < y_2$ (interleaved), the BDD has *linear* size in the number of pairs.

  With ordering $x_1 < x_2 < y_1 < y_2$ (grouped), the BDD can have *exponential* size.

  The difference arises because interleaved ordering allows decisions about each pair to be made together, while grouped ordering requires remembering partial information across many levels.
]

This sensitivity to ordering is both a strength and a weakness of BDDs:
- *Strength*: A good ordering can yield very compact representations
- *Weakness*: Finding optimal orderings is itself NP-hard

We discuss variable ordering heuristics in detail in @ch-variable-ordering.

== Reduced BDDs (ROBDDs)

The final ingredient for canonicity is *reduction* --- eliminating all redundancy.

#definition(title: "Reduced Ordered BDD")[
  An OBDD is *reduced* (ROBDD) if it satisfies two properties:
  + *No redundant tests*: For every decision node $v$, we have $"low"(v) != "high"(v)$
  + *No duplicate nodes*: No two distinct nodes have the same variable, low child, and high child

  Equivalently: the BDD is maximally shared and contains no unnecessary nodes.
]

=== Reduction Rules

The two reduction properties correspond to two reduction rules:

*Rule 1: Eliminate Redundant Tests*

If a node $v$ has $"low"(v) = "high"(v) = u$, then $v$ is redundant.
The function computed by $v$ is $overline(x) dot f_u + x dot f_u = f_u$, independent of $x$.
We can redirect all edges pointing to $v$ to point to $u$ instead, then remove $v$.

*Rule 2: Merge Isomorphic Subgraphs*

If two distinct nodes $v$ and $w$ have the same variable and children:
$"var"(v) = "var"(w)$, $"low"(v) = "low"(w)$, $"high"(v) = "high"(w)$

Then they compute the same function and can be merged.
We keep one and redirect all edges to the other.

#algorithm(title: "Reduction Procedure")[
  To reduce an OBDD:
  + Process nodes bottom-up (from terminals toward root)
  + For each node $v$:
    - If $"low"(v) = "high"(v)$, replace $v$ with its child (Rule 1)
    - Otherwise, check if an equivalent node already exists; if so, merge (Rule 2)
  + The result is a reduced OBDD
]

=== The Unique Table

In practice, reduction is achieved by maintaining a *unique table* --- a hash table that maps $("var", "low", "high")$ triples to nodes.
When creating a node, we first check if it already exists.
This ensures duplicate nodes are never created in the first place.

The unique table is fundamental to BDD implementations and is covered in detail in @ch-unique-table.

== Visual Examples

Let us see these concepts in action with concrete examples.

=== Example: Conjunction ($x and y$)

The function $f(x, y) = x and y$ with ordering $x < y$:
- If $x = 0$: output is $0$ regardless of $y$
- If $x = 1$: output is $y$

#figure(
  cetz.canvas(length: 1cm, {
    import cetz.draw: *

    // Positions
    let x-pos = (3, 4)
    let y-pos = (4, 2.5)
    let zero-pos = (2, 0.8)
    let one-pos = (5, 0.8)

    // Draw nodes
    bdd-terminal-node(zero-pos, 0, name: "zero")
    bdd-terminal-node(one-pos, 1, name: "one")
    bdd-decision-node(x-pos, "x", name: "x")
    bdd-decision-node(y-pos, "y", name: "y")

    // Edges
    bdd-low-edge((x-pos.at(0) - 0.35, x-pos.at(1) - 0.35), (zero-pos.at(0) + 0.2, zero-pos.at(1) + 0.5))
    bdd-high-edge((x-pos.at(0) + 0.35, x-pos.at(1) - 0.35), (y-pos.at(0) - 0.2, y-pos.at(1) + 0.4))
    bdd-low-edge((y-pos.at(0) - 0.35, y-pos.at(1) - 0.35), (zero-pos.at(0) + 0.4, zero-pos.at(1) + 0.3))
    bdd-high-edge((y-pos.at(0) + 0.35, y-pos.at(1) - 0.35), (one-pos.at(0) - 0.2, one-pos.at(1) + 0.4))

    // Annotations
    content(
      (7, 3.5),
      align(left)[
        #set text(size: 0.8em)
        *Evaluation paths:*\
        $x=0$: $-> 0$ (short-circuit)\
        $x=1, y=0$: $-> 0$\
        $x=1, y=1$: $-> 1$ ✓
      ],
      anchor: "west",
    )
  }),
  caption: [ROBDD for $x and y$. The $y$-node is only reached when $x = 1$.],
)

Notice that the $y$-node is only reached when $x = 1$, reflecting short-circuit evaluation.
The BDD has just 2 decision nodes --- much smaller than the $2^2 = 4$ leaves of a decision tree.

=== Example: Exclusive Or ($x xor y$)

The function $f(x, y) = x xor y$ with ordering $x < y$:
- If $x = 0$: output is $y$
- If $x = 1$: output is $not y$

#figure(
  cetz.canvas(length: 1cm, {
    import cetz.draw: *

    // Positions
    let x-pos = (3.5, 4)
    let y1-pos = (2, 2.5)
    let y2-pos = (5, 2.5)
    let zero-pos = (2, 0.8)
    let one-pos = (5, 0.8)

    // Draw nodes
    bdd-terminal-node(zero-pos, 0, name: "zero")
    bdd-terminal-node(one-pos, 1, name: "one")
    bdd-decision-node(x-pos, "x", name: "x")
    bdd-decision-node(y1-pos, "y", name: "y1")
    bdd-decision-node(y2-pos, "y", name: "y2")

    // From x
    bdd-low-edge((x-pos.at(0) - 0.35, x-pos.at(1) - 0.35), (y1-pos.at(0) + 0.2, y1-pos.at(1) + 0.4))
    bdd-high-edge((x-pos.at(0) + 0.35, x-pos.at(1) - 0.35), (y2-pos.at(0) - 0.2, y2-pos.at(1) + 0.4))

    // From y1 (represents y when x=0)
    bdd-low-edge((y1-pos.at(0) - 0.3, y1-pos.at(1) - 0.4), (zero-pos.at(0) + 0.1, zero-pos.at(1) + 0.35))
    bdd-high-edge((y1-pos.at(0) + 0.35, y1-pos.at(1) - 0.35), (one-pos.at(0) - 0.4, one-pos.at(1) + 0.5))

    // From y2 (represents ¬y when x=1)
    bdd-low-edge((y2-pos.at(0) - 0.35, y2-pos.at(1) - 0.35), (one-pos.at(0) + 0.1, one-pos.at(1) + 0.35))
    bdd-high-edge((y2-pos.at(0) + 0.3, y2-pos.at(1) - 0.4), (zero-pos.at(0) + 0.5, zero-pos.at(1) + 0.5))

    // Labels
    content((0.5, 2.5), text(size: 0.8em, fill: colors.text-muted)[$y$ when $x=0$], anchor: "east")
    content((6.5, 2.5), text(size: 0.8em, fill: colors.text-muted)[$not y$ when $x=1$], anchor: "west")
  }),
  caption: [ROBDD for $x xor y$. Two $y$-nodes are needed because the subfunctions differ.],
)

The ROBDD requires two $y$-nodes because $y$ and $not y$ are different functions.
No reduction is possible here --- this is the minimal representation.

#info-box(title: "XOR and Complement Edges")[
  With *complement edges* (covered in @ch-complement-edges), XOR can share structure with equivalence.
  The left $y$-node becomes the right one with a complement marker, halving the size.
]

=== Example: Majority Function

The majority function $"Maj"(x, y, z)$ outputs 1 when at least two inputs are 1:

$ "Maj"(x, y, z) = (x and y) or (y and z) or (x and z) $

#figure(
  cetz.canvas(length: 1cm, {
    import cetz.draw: *

    // Positions for ordering x < y < z
    let x-pos = (4, 5.5)
    let y1-pos = (2.5, 4)
    let y2-pos = (5.5, 4)
    let z1-pos = (2, 2.5)
    let z2-pos = (5, 2.5)
    let zero-pos = (2.5, 0.8)
    let one-pos = (5.5, 0.8)

    // Draw terminals
    bdd-terminal-node(zero-pos, 0, name: "zero")
    bdd-terminal-node(one-pos, 1, name: "one")

    // Draw decision nodes
    bdd-decision-node(x-pos, "x", name: "x")
    bdd-decision-node(y1-pos, "y", name: "y1")
    bdd-decision-node(y2-pos, "y", name: "y2")
    bdd-decision-node(z1-pos, "z", name: "z1")
    bdd-decision-node(z2-pos, "z", name: "z2")

    // From x
    bdd-low-edge((x-pos.at(0) - 0.35, x-pos.at(1) - 0.35), (y1-pos.at(0) + 0.2, y1-pos.at(1) + 0.4))
    bdd-high-edge((x-pos.at(0) + 0.35, x-pos.at(1) - 0.35), (y2-pos.at(0) - 0.2, y2-pos.at(1) + 0.4))

    // From y1 (x=0 branch): need both y and z
    bdd-low-edge((y1-pos.at(0) - 0.3, y1-pos.at(1) - 0.4), (zero-pos.at(0) - 0.1, zero-pos.at(1) + 0.5))
    bdd-high-edge((y1-pos.at(0) + 0.2, y1-pos.at(1) - 0.4), (z1-pos.at(0) - 0.1, z1-pos.at(1) + 0.4))

    // From y2 (x=1 branch): need y or z
    bdd-low-edge((y2-pos.at(0) - 0.2, y2-pos.at(1) - 0.4), (z2-pos.at(0) + 0.1, z2-pos.at(1) + 0.4))
    bdd-high-edge((y2-pos.at(0) + 0.3, y2-pos.at(1) - 0.4), (one-pos.at(0) + 0.1, one-pos.at(1) + 0.5))

    // From z1 (x=0, y=1): output z
    bdd-low-edge((z1-pos.at(0) - 0.3, z1-pos.at(1) - 0.4), (zero-pos.at(0) - 0.2, zero-pos.at(1) + 0.3))
    bdd-high-edge((z1-pos.at(0) + 0.3, z1-pos.at(1) - 0.4), (one-pos.at(0) - 0.5, one-pos.at(1) + 0.5))

    // From z2 (x=1, y=0): output z
    bdd-low-edge((z2-pos.at(0) - 0.3, z2-pos.at(1) - 0.4), (zero-pos.at(0) + 0.3, zero-pos.at(1) + 0.3))
    bdd-high-edge((z2-pos.at(0) + 0.3, z2-pos.at(1) - 0.4), (one-pos.at(0) - 0.2, one-pos.at(1) + 0.3))

    // Annotation
    content(
      (8, 4),
      align(left)[
        #set text(size: 0.8em)
        *Subfunctions:*\
        $x=0$: need $y and z$\
        $x=1$: need $y or z$\
        \
        Both $z$-nodes share\
        the same terminals!
      ],
      anchor: "west",
    )
  }),
  caption: [ROBDD for majority function $"Maj"(x,y,z)$ with ordering $x < y < z$.],
)

Interestingly, both $z$-nodes output the same value: $z$ itself.
The only difference is which paths reach them.
With complement edges, further sharing would be possible.

== Graph Properties and Metrics

Several metrics characterize BDD complexity:

#definition(title: "BDD Size")[
  The *size* of a BDD is the number of nodes, typically counting decision nodes only (excluding terminals).
  We denote the size of BDD representing function $f$ as $|f|$ or $"size"(f)$.
]

#definition(title: "BDD Width")[
  The *width* at level $i$ is the number of nodes with variable $x_i$.
  The *maximum width* is the maximum over all levels.
]

#definition(title: "BDD Depth")[
  The *depth* (or height) is the length of the longest path from root to a terminal.
  For ROBDDs with $n$ variables, depth is at most $n$.
]

=== Size Bounds

The size of an ROBDD is bounded:
- *Lower bound*: $1$ (for constant functions $0$ or $1$)
- *Upper bound*: Depends on the function and ordering

For *any* function and *any* ordering, the ROBDD has at most $2^n$ nodes (one per possible subfunction).
However, many practical functions have polynomial-size BDDs with good orderings.

#theorem(title: "Size Hierarchy")[
  There exist functions with the following BDD sizes (for optimal orderings):
  - $O(1)$: Constant functions, single variables
  - $O(n)$: AND, OR, linear threshold functions, symmetric functions
  - $O(n^2)$: Addition, comparison
  - $O(2^n)$: Multiplication (output bits), hidden weighted bit

  The size can vary exponentially between different orderings for the same function.
]

== Summary

We have now established the formal foundation:

#info-box(title: "Key Definitions")[
  - *BDD*: A DAG with decision and terminal nodes representing a Boolean function via Shannon expansion
  - *OBDD*: A BDD where variables appear in consistent order on all paths
  - *ROBDD*: An OBDD with no redundant tests and no duplicate nodes

  ROBDDs are *canonical*: two ROBDDs with the same ordering represent the same function if and only if they are identical.
]

The canonicity theorem (proved in @ch-canonicity) makes ROBDDs uniquely powerful.
In the next chapter, we prove this theorem and explore its consequences for equivalence checking and other operations.
