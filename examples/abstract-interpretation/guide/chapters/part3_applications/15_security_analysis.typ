#import "../../theme.typ": *

= Security Analysis <ch-security>

#reading-path(path: "essential")

Security analysis is one of the most impactful applications of abstract interpretation.
By tracking the flow of information through a program, we can detect vulnerabilities like SQL injection, cross-site scripting (XSS), and information leaks.

== Taint Analysis

The core concept in security analysis is *taint tracking*.
Data coming from untrusted sources (user input, network) is marked as "tainted".
Data that is safe to use (constants, sanitized input) is "clean".

#definition(title: "Taint Domain")[
  The taint domain is a simple two-point lattice:
  $ D = \{ lbot, "Clean", "Tainted", ltop \} $
  where $"Clean" < "Tainted"$.
  - Sources (e.g., `read_input()`) return $"Tainted"$.
  - Sinks (e.g., `exec_sql()`) require $"Clean"$ arguments.
  - Sanitizers (e.g., `escape_sql()`) convert $"Tainted"$ to $"Clean"$.
]

== BDD-Guided Taint Analysis

Standard taint analysis is often path-insensitive, leading to false positives.
BDDs allow us to track *under what conditions* a variable is tainted.

#example-box(title: "Conditional Sanitization")[
  ```rust
  let x = read_user_input(); // x is Tainted
  if is_safe(x) {
      // On this path, x is Clean
      exec_sql(x); // Safe!
  } else {
      // On this path, x is still Tainted
      // exec_sql(x); // Would be an error
  }
  ```
]

In our framework, the abstract state is a map from variables to `Bdd -> Taint`.
This allows us to prove that `x` is clean *conditioned on* the path `is_safe(x)`.

== Implementation

See `examples/security_and_normalization.rs` for a complete implementation.
