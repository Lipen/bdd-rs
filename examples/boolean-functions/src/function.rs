//! Boolean function representation and random generation.
//!
//! A Boolean function `f: {0,1}^n → {0,1}` is represented by its truth table,
//! a vector of `2^n` bits indexed by the input assignments.

use ananke_bdd::bdd::Bdd;
use ananke_bdd::reference::Ref;
use ananke_bdd::types::Var;
use num_bigint::BigUint;
use num_traits::{One, Zero};
use rand::Rng;

/// A truth table for a Boolean function on `n` variables.
///
/// The truth table is a `2^n`-bit vector where bit `i` is `f(b_{n-1}, ..., b_0)`
/// where `i = b_{n-1} * 2^{n-1} + ... + b_0`.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct TruthTable {
    /// Number of variables
    pub n: usize,
    /// The truth table as a big integer (2^n bits)
    pub bits: BigUint,
}

impl TruthTable {
    /// Create a new truth table from a big integer.
    pub fn new(n: usize, bits: BigUint) -> Self {
        Self { n, bits }
    }

    /// Create the constant zero function.
    pub fn zero(n: usize) -> Self {
        Self { n, bits: BigUint::zero() }
    }

    /// Create the constant one function.
    pub fn one(n: usize) -> Self {
        let bits = (BigUint::one() << (1usize << n)) - BigUint::one();
        Self { n, bits }
    }

    /// Create a function that is true only for input `i`.
    pub fn minterm(n: usize, i: usize) -> Self {
        assert!(i < (1 << n), "Minterm index out of range");
        Self {
            n,
            bits: BigUint::one() << i,
        }
    }

    /// Create the projection function for variable `var` (1-indexed).
    pub fn projection(n: usize, var: usize) -> Self {
        assert!(var >= 1 && var <= n, "Variable index out of range");
        // Variable `var` (1-indexed) corresponds to bit position (var-1) in the input
        // The projection x_var is true when bit (var-1) of the input is 1
        let mut bits = BigUint::zero();
        for i in 0..(1usize << n) {
            if (i >> (var - 1)) & 1 == 1 {
                bits |= BigUint::one() << i;
            }
        }
        Self { n, bits }
    }

    /// Generate a uniformly random Boolean function.
    pub fn random<R: Rng>(n: usize, rng: &mut R) -> Self {
        let num_bits = 1usize << n;
        let num_bytes = (num_bits + 7) / 8;
        let mut bytes = vec![0u8; num_bytes];
        rng.fill(&mut bytes[..]);

        // Mask off extra bits if num_bits is not a multiple of 8
        if num_bits % 8 != 0 {
            let mask = (1u8 << (num_bits % 8)) - 1;
            bytes[num_bytes - 1] &= mask;
        }

        Self {
            n,
            bits: BigUint::from_bytes_le(&bytes),
        }
    }

    /// Get the value of the function at input `i`.
    pub fn eval(&self, i: usize) -> bool {
        assert!(i < (1 << self.n), "Input index out of range");
        self.bits.bit(i as u64)
    }

    /// Set the value of the function at input `i`.
    pub fn set(&mut self, i: usize, value: bool) {
        assert!(i < (1 << self.n), "Input index out of range");
        if value {
            self.bits |= BigUint::one() << i;
        } else {
            // Clear the bit by XORing if it's set
            let mask = BigUint::one() << i;
            if self.bits.bit(i as u64) {
                self.bits ^= &mask;
            }
        }
    }

    /// Count the number of true outputs (Hamming weight).
    pub fn count_ones(&self) -> usize {
        self.bits.count_ones() as usize
    }

    /// Check if this is the constant zero function.
    pub fn is_zero(&self) -> bool {
        self.bits.is_zero()
    }

    /// Check if this is the constant one function.
    pub fn is_one(&self) -> bool {
        self.count_ones() == (1 << self.n)
    }

    /// Compute the complement (negation) of this function.
    pub fn complement(&self) -> Self {
        let all_ones = (BigUint::one() << (1usize << self.n)) - BigUint::one();
        Self {
            n: self.n,
            bits: all_ones ^ &self.bits,
        }
    }

    /// Compute the AND of two functions.
    pub fn and(&self, other: &Self) -> Self {
        assert_eq!(self.n, other.n, "Variable count mismatch");
        Self {
            n: self.n,
            bits: &self.bits & &other.bits,
        }
    }

    /// Compute the OR of two functions.
    pub fn or(&self, other: &Self) -> Self {
        assert_eq!(self.n, other.n, "Variable count mismatch");
        Self {
            n: self.n,
            bits: &self.bits | &other.bits,
        }
    }

    /// Compute the XOR of two functions.
    pub fn xor(&self, other: &Self) -> Self {
        assert_eq!(self.n, other.n, "Variable count mismatch");
        Self {
            n: self.n,
            bits: &self.bits ^ &other.bits,
        }
    }

    /// Get a canonical index for this function (its truth table as a number).
    pub fn index(&self) -> BigUint {
        self.bits.clone()
    }

    /// Create from a canonical index.
    pub fn from_index(n: usize, index: BigUint) -> Self {
        Self { n, bits: index }
    }

    /// Iterator over all functions with `n` variables.
    ///
    /// Warning: This is only practical for small `n` (≤ 4 or 5).
    pub fn all_functions(n: usize) -> impl Iterator<Item = TruthTable> {
        let total = BigUint::one() << (1usize << n);
        AllFunctionsIterator {
            n,
            current: BigUint::zero(),
            total,
        }
    }

    /// Total number of Boolean functions on `n` variables.
    pub fn total_count(n: usize) -> BigUint {
        BigUint::one() << (1usize << n)
    }
}

/// Iterator over all Boolean functions with `n` variables.
struct AllFunctionsIterator {
    n: usize,
    current: BigUint,
    total: BigUint,
}

impl Iterator for AllFunctionsIterator {
    type Item = TruthTable;

    fn next(&mut self) -> Option<Self::Item> {
        if self.current >= self.total {
            None
        } else {
            let result = TruthTable::new(self.n, self.current.clone());
            self.current += BigUint::one();
            Some(result)
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        // This may overflow for large n, but that's expected
        let remaining = &self.total - &self.current;
        match remaining.try_into() {
            Ok(n) => (n, Some(n)),
            Err(_) => (usize::MAX, None),
        }
    }
}

/// A Boolean function with its BDD representation.
#[derive(Debug)]
pub struct BooleanFunction {
    /// The truth table representation
    pub truth_table: TruthTable,
    /// The BDD reference (only valid with the manager that created it)
    pub bdd_ref: Ref,
    /// The BDD size (number of nodes)
    pub size: usize,
}

impl BooleanFunction {
    /// Build a BDD from a truth table.
    pub fn from_truth_table(bdd: &Bdd, tt: &TruthTable) -> Self {
        let bdd_ref = build_bdd_from_truth_table(bdd, tt);
        let size = bdd.size(bdd_ref) as usize;
        Self {
            truth_table: tt.clone(),
            bdd_ref,
            size,
        }
    }
}

/// Build a BDD from a truth table using Shannon expansion.
pub fn build_bdd_from_truth_table(bdd: &Bdd, tt: &TruthTable) -> Ref {
    if tt.n == 0 {
        return if tt.bits.is_zero() { bdd.zero() } else { bdd.one() };
    }

    // Use recursive Shannon expansion
    build_bdd_recursive(bdd, tt, tt.n, 0)
}

/// Recursive helper for BDD construction.
///
/// Builds BDD for sub-function at depth `var` (1-indexed) with base index `base`.
fn build_bdd_recursive(bdd: &Bdd, tt: &TruthTable, var: usize, base: usize) -> Ref {
    if var == 0 {
        // Base case: single bit
        return if tt.eval(base) { bdd.one() } else { bdd.zero() };
    }

    let half = 1 << (var - 1);

    // Low branch: var = 0
    let low = build_bdd_recursive(bdd, tt, var - 1, base);

    // High branch: var = 1
    let high = build_bdd_recursive(bdd, tt, var - 1, base + half);

    // Build the BDD node
    bdd.mk_node(Var::new(var as u32), low, high)
}

/// Generate a random Boolean function and build its BDD.
pub fn random_function_with_bdd<R: Rng>(bdd: &Bdd, n: usize, rng: &mut R) -> BooleanFunction {
    let tt = TruthTable::random(n, rng);
    BooleanFunction::from_truth_table(bdd, &tt)
}

#[cfg(test)]
mod tests {
    use rand::SeedableRng;
    use rand_chacha::ChaCha8Rng;

    use super::*;

    #[test]
    fn test_truth_table_constants() {
        let zero = TruthTable::zero(3);
        assert!(zero.is_zero());
        assert!(!zero.is_one());
        assert_eq!(zero.count_ones(), 0);

        let one = TruthTable::one(3);
        assert!(!one.is_zero());
        assert!(one.is_one());
        assert_eq!(one.count_ones(), 8);
    }

    #[test]
    fn test_truth_table_projection() {
        let n = 3;
        let x1 = TruthTable::projection(n, 1);
        let x2 = TruthTable::projection(n, 2);
        let x3 = TruthTable::projection(n, 3);

        // x1 is true for inputs 1, 3, 5, 7 (odd inputs)
        assert_eq!(x1.count_ones(), 4);
        assert!(!x1.eval(0));
        assert!(x1.eval(1));
        assert!(!x1.eval(2));
        assert!(x1.eval(3));

        // x2 is true for inputs 2, 3, 6, 7
        assert_eq!(x2.count_ones(), 4);
        assert!(!x2.eval(0));
        assert!(!x2.eval(1));
        assert!(x2.eval(2));
        assert!(x2.eval(3));

        // x3 is true for inputs 4, 5, 6, 7
        assert_eq!(x3.count_ones(), 4);
        for i in 0..4 {
            assert!(!x3.eval(i));
        }
        for i in 4..8 {
            assert!(x3.eval(i));
        }
    }

    #[test]
    fn test_truth_table_operations() {
        let n = 2;
        let x1 = TruthTable::projection(n, 1);
        let x2 = TruthTable::projection(n, 2);

        // x1 AND x2
        let and = x1.and(&x2);
        assert_eq!(and.count_ones(), 1); // Only input 3 (11)
        assert!(and.eval(3));

        // x1 OR x2
        let or = x1.or(&x2);
        assert_eq!(or.count_ones(), 3); // Inputs 1, 2, 3

        // x1 XOR x2
        let xor = x1.xor(&x2);
        assert_eq!(xor.count_ones(), 2); // Inputs 1, 2
    }

    #[test]
    fn test_all_functions() {
        let n = 2;
        let count: usize = TruthTable::all_functions(n).count();
        assert_eq!(count, 16); // 2^(2^2) = 16
    }

    #[test]
    fn test_bdd_construction() {
        let bdd = Bdd::default();

        // Test constant functions
        let zero_tt = TruthTable::zero(2);
        let zero_bdd = build_bdd_from_truth_table(&bdd, &zero_tt);
        assert!(bdd.is_zero(zero_bdd));

        let one_tt = TruthTable::one(2);
        let one_bdd = build_bdd_from_truth_table(&bdd, &one_tt);
        assert!(bdd.is_one(one_bdd));

        // Test projection: size includes terminal node, so single variable = 2
        let x1_tt = TruthTable::projection(2, 1);
        let x1_bdd = build_bdd_from_truth_table(&bdd, &x1_tt);
        assert_eq!(bdd.size(x1_bdd), 2); // One variable node + terminal
    }

    #[test]
    fn test_random_function() {
        let bdd = Bdd::default();
        let mut rng = ChaCha8Rng::seed_from_u64(42);

        for _ in 0..10 {
            let func = random_function_with_bdd(&bdd, 4, &mut rng);
            assert!(func.size <= (1 << 4) + 1); // At most 2^n + 1 nodes
        }
    }
}
