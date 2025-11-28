#import "../../theme.typ": *

= Bibliography and Further Reading <appendix-bibliography>

// PLAN: Key references organized by topic.
// Target length: 3-4 pages

== Foundational Papers

+ *R. E. Bryant* (1986). "Graph-Based Algorithms for Boolean Function Manipulation." _IEEE Transactions on Computers_, C-35(8):677–691.

  _The seminal paper introducing ROBDDs with the canonicity theorem._

+ *C. Y. Lee* (1959). "Representation of Switching Circuits by Binary-Decision Programs." _Bell System Technical Journal_, 38:985–999.

  _Early work on binary decision programs._

+ *S. B. Akers* (1978). "Binary Decision Diagrams." _IEEE Transactions on Computers_, C-27(6):509–516.

  _Formalization of binary decision diagrams._

== Algorithms and Optimizations

+ *R. Rudell* (1993). "Dynamic Variable Ordering for Ordered Binary Decision Diagrams." _ICCAD '93_.

  _The sifting algorithm for dynamic reordering._

+ *K. S. Brace, R. L. Rudell, R. E. Bryant* (1990). "Efficient Implementation of a BDD Package." _DAC '90_.

  _Practical implementation techniques including complement edges._

+ *S. Minato* (1993). "Zero-Suppressed BDDs for Set Manipulation in Combinatorial Problems." _DAC '93_.

  _Introduction of ZDDs for sparse set families._

== Model Checking

+ *J. R. Burch, E. M. Clarke, K. L. McMillan, D. L. Dill, L. J. Hwang* (1992). "Symbolic Model Checking: 10^20 States and Beyond." _Information and Computation_, 98(2):142–170.

  _Landmark paper on symbolic model checking with BDDs._

+ *K. L. McMillan* (1993). _Symbolic Model Checking_. Kluwer Academic Publishers.

  _Comprehensive book on symbolic verification._

== Books and Surveys

+ *C. Meinel, T. Theobald* (1998). _Algorithms and Data Structures in VLSI Design: OBDD — Foundations and Applications_. Springer.

  _Thorough treatment of BDD theory and applications._

+ *D. E. Knuth* (2009). _The Art of Computer Programming, Volume 4A: Combinatorial Algorithms, Part 1_. Addison-Wesley.

  _Extensive coverage of BDDs and ZDDs with careful analysis._

+ *H. R. Andersen* (1999). "An Introduction to Binary Decision Diagrams." _Lecture Notes, IT University of Copenhagen_.

  _Excellent pedagogical introduction, freely available online._

== Software Libraries

- *CUDD*: Colorado University Decision Diagram Package (Fabio Somenzi)
- *BuDDy*: Binary Decision Diagram Library (Jørn Lind-Nielsen)
- *Sylvan*: Multi-core Decision Diagrams (Tom van Dijk)
- *bdd-rs*: Binary Decision Diagrams in Rust (this library)
