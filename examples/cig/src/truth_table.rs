//! Truth table representation for Boolean functions.
//!
//! A Boolean function f: {0,1}ⁿ → {0,1} is represented by its truth table,
//! a vector of 2ⁿ bits indexed by input assignments in lexicographic order.

use std::fmt;

use bitvec::prelude::*;

use crate::variable::{Var, VarSet};

/// A truth table for a Boolean function on n variables.
///
/// The truth table stores 2ⁿ bits where bit i corresponds to the function
/// value at input assignment i (interpreted as an n-bit binary number).
///
/// # Variable Ordering
///
/// Variables are numbered 1 to n. For input index i, variable xⱼ has value
/// (i >> (j-1)) & 1. This means x₁ is the least significant bit.
///
/// # Example
///
/// For n=2:
/// - Index 0 (binary 00): x₁=0, x₂=0
/// - Index 1 (binary 01): x₁=1, x₂=0
/// - Index 2 (binary 10): x₁=0, x₂=1
/// - Index 3 (binary 11): x₁=1, x₂=1
#[derive(Clone, PartialEq, Eq, Hash)]
pub struct TruthTable {
    /// Number of variables.
    n: u32,
    /// The truth table bits: 2ⁿ bits.
    bits: BitVec<u64, Lsb0>,
}

impl TruthTable {
    /// Create a truth table from an expression function.
    ///
    /// The function receives a slice of n Booleans and returns the output.
    /// Variables are passed as [x₁, x₂, ..., xₙ] (1-indexed in concept).
    ///
    /// # Example
    ///
    /// ```
    /// use cig::TruthTable;
    ///
    /// // f = x₁ ∧ x₂
    /// let f = TruthTable::from_expr(2, |x| x[0] && x[1]);
    /// assert!(f.eval(&[true, true]));
    /// assert!(!f.eval(&[true, false]));
    /// ```
    pub fn from_expr(n: u32, f: impl Fn(&[bool]) -> bool) -> Self {
        let size = 1usize << n;
        let mut bits = BitVec::with_capacity(size);
        let mut assignment = vec![false; n as usize];

        for i in 0..size {
            // Decode index i into assignment
            for (j, val) in assignment.iter_mut().enumerate() {
                *val = (i >> j) & 1 == 1;
            }
            bits.push(f(&assignment));
        }

        TruthTable { n, bits }
    }

    /// Create a truth table from raw bits.
    ///
    /// # Panics
    ///
    /// Panics if `bits.len() != 2^n`.
    pub fn from_bits(n: u32, bits: BitVec<u64, Lsb0>) -> Self {
        let expected = 1usize << n;
        assert_eq!(
            bits.len(),
            expected,
            "Expected {} bits for {} variables, got {}",
            expected,
            n,
            bits.len()
        );
        TruthTable { n, bits }
    }

    /// Create the constant zero function.
    pub fn zero(n: u32) -> Self {
        let size = 1usize << n;
        TruthTable {
            n,
            bits: bitvec![u64, Lsb0; 0; size],
        }
    }

    /// Create the constant one function.
    pub fn one(n: u32) -> Self {
        let size = 1usize << n;
        TruthTable {
            n,
            bits: bitvec![u64, Lsb0; 1; size],
        }
    }

    /// Create the projection function for variable xᵢ.
    ///
    /// Returns a function that outputs 1 iff xᵢ = 1.
    pub fn var(n: u32, var: Var) -> Self {
        assert!(var.index() <= n, "Variable {} out of range for {}-variable function", var, n);
        TruthTable::from_expr(n, move |x| x[var.position()])
    }

    /// Create the negated projection for variable xᵢ.
    pub fn not_var(n: u32, var: Var) -> Self {
        TruthTable::var(n, var).complement()
    }

    /// Get the number of variables.
    pub fn num_vars(&self) -> u32 {
        self.n
    }

    /// Get the size of the truth table (2ⁿ).
    pub fn size(&self) -> usize {
        self.bits.len()
    }

    /// Evaluate the function at a given input.
    ///
    /// Input is a slice of n Booleans [x₁, x₂, ..., xₙ].
    pub fn eval(&self, input: &[bool]) -> bool {
        assert_eq!(input.len(), self.n as usize, "Expected {} inputs, got {}", self.n, input.len());
        let index = input.iter().enumerate().fold(0usize, |acc, (i, &b)| acc | ((b as usize) << i));
        self.bits[index]
    }

    /// Evaluate the function at a given index.
    pub fn eval_index(&self, index: usize) -> bool {
        assert!(index < self.bits.len(), "Index out of range");
        self.bits[index]
    }

    /// Check if this is the constant zero function.
    pub fn is_zero(&self) -> bool {
        !self.bits.any()
    }

    /// Check if this is the constant one function.
    pub fn is_one(&self) -> bool {
        self.bits.all()
    }

    /// Check if this is a constant function.
    pub fn is_constant(&self) -> bool {
        self.is_zero() || self.is_one()
    }

    /// Count the number of satisfying assignments (Hamming weight).
    pub fn count_ones(&self) -> usize {
        self.bits.count_ones()
    }

    /// Compute the complement (negation) of this function.
    pub fn complement(&self) -> Self {
        TruthTable {
            n: self.n,
            bits: !self.bits.clone(),
        }
    }

    /// Compute the conjunction (AND) of two functions.
    pub fn and(&self, other: &Self) -> Self {
        assert_eq!(self.n, other.n, "Variable count mismatch");
        TruthTable {
            n: self.n,
            bits: self.bits.clone() & other.bits.clone(),
        }
    }

    /// Compute the disjunction (OR) of two functions.
    pub fn or(&self, other: &Self) -> Self {
        assert_eq!(self.n, other.n, "Variable count mismatch");
        TruthTable {
            n: self.n,
            bits: self.bits.clone() | other.bits.clone(),
        }
    }

    /// Compute the exclusive-or (XOR) of two functions.
    pub fn xor(&self, other: &Self) -> Self {
        assert_eq!(self.n, other.n, "Variable count mismatch");
        TruthTable {
            n: self.n,
            bits: self.bits.clone() ^ other.bits.clone(),
        }
    }

    /// Compute the Shannon cofactor f|_{xᵢ=b}.
    ///
    /// Returns a function on n-1 variables (renumbered).
    pub fn cofactor(&self, var: Var, value: bool) -> Self {
        assert!(var.index() <= self.n, "Variable {} out of range", var);

        if self.n == 1 {
            // Result is a constant
            let idx = if value { 1 } else { 0 };
            return if self.bits[idx] { TruthTable::one(0) } else { TruthTable::zero(0) };
        }

        let new_n = self.n - 1;
        let new_size = 1usize << new_n;
        let pos = var.position();
        let val_bit = if value { 1usize } else { 0 };

        let mut new_bits = BitVec::with_capacity(new_size);

        for i in 0..new_size {
            // Map index i (in new function) to index in original function
            // Insert the fixed bit at position `pos`
            let lower = i & ((1 << pos) - 1); // bits below pos
            let upper = i >> pos; // bits at pos and above (shifted)
            let orig_idx = lower | (val_bit << pos) | (upper << (pos + 1));
            new_bits.push(self.bits[orig_idx]);
        }

        TruthTable { n: new_n, bits: new_bits }
    }

    /// Restrict the function to a subset of variables.
    ///
    /// Returns a function only on the given variables, treating others
    /// as if they don't exist (projecting out the non-mentioned variables
    /// by restricting to their value 0).
    pub fn restrict(&self, vars: &VarSet) -> Self {
        let mut result = self.clone();
        for i in (1..=self.n).rev() {
            let var = Var(i);
            if !vars.contains(var) {
                result = result.cofactor(var, false);
            }
        }
        result
    }

    /// Check if a variable is essential (influential) for this function.
    ///
    /// A variable xᵢ is essential iff there exists an input where changing
    /// xᵢ changes the output.
    pub fn is_essential(&self, var: Var) -> bool {
        let f0 = self.cofactor(var, false);
        let f1 = self.cofactor(var, true);
        f0 != f1
    }

    /// Find all essential variables.
    pub fn essential_vars(&self) -> VarSet {
        let mut essential = VarSet::empty();
        let size = self.size();

        for var_idx in 0..self.n as usize {
            // A variable is essential if swapping its bit changes at least one output
            let step = 1usize << var_idx;

            for i in 0..size {
                // Compare f(x) with f(x with bit i flipped)
                let j = i ^ step;
                if i < j && self.bits[i] != self.bits[j] {
                    essential.insert(Var::new((var_idx + 1) as u32));
                    break;
                }
            }
        }

        essential
    }

    /// Get the raw bits as a slice.
    pub fn as_bits(&self) -> &BitSlice<u64, Lsb0> {
        &self.bits
    }

    /// Create a canonical hash for this truth table.
    pub fn canonical_hash(&self) -> u64 {
        use std::hash::{Hash, Hasher};
        let mut hasher = rustc_hash::FxHasher::default();
        self.n.hash(&mut hasher);
        // Hash the raw bytes of the bitvec
        for chunk in self.bits.as_raw_slice() {
            chunk.hash(&mut hasher);
        }
        hasher.finish()
    }
}

impl fmt::Debug for TruthTable {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "TruthTable({}, [", self.n)?;
        for (i, bit) in self.bits.iter().enumerate() {
            if i > 0 {
                write!(f, ", ")?;
            }
            write!(f, "{}", if *bit { 1 } else { 0 })?;
        }
        write!(f, "])")
    }
}

impl fmt::Display for TruthTable {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        // Display as a compact binary string
        for bit in self.bits.iter() {
            write!(f, "{}", if *bit { '1' } else { '0' })?;
        }
        Ok(())
    }
}

/// Named Boolean functions for testing and examples.
pub mod named {
    use super::*;

    /// AND of all variables: x₁ ∧ x₂ ∧ ... ∧ xₙ
    pub fn and_all(n: u32) -> TruthTable {
        TruthTable::from_expr(n, |x| x.iter().all(|&b| b))
    }

    /// OR of all variables: x₁ ∨ x₂ ∨ ... ∨ xₙ
    pub fn or_all(n: u32) -> TruthTable {
        TruthTable::from_expr(n, |x| x.iter().any(|&b| b))
    }

    /// XOR (parity) of all variables: x₁ ⊕ x₂ ⊕ ... ⊕ xₙ
    pub fn xor_all(n: u32) -> TruthTable {
        TruthTable::from_expr(n, |x| x.iter().filter(|&&b| b).count() % 2 == 1)
    }

    /// Majority function on 3 variables.
    pub fn majority3() -> TruthTable {
        TruthTable::from_expr(3, |x| {
            let count = x.iter().filter(|&&b| b).count();
            count >= 2
        })
    }

    /// Multiplexer: MUX(s, x, y) = (¬s ∧ x) ∨ (s ∧ y)
    /// Variables: s=x₁, x=x₂, y=x₃
    pub fn mux() -> TruthTable {
        TruthTable::from_expr(3, |v| {
            let s = v[0];
            let x = v[1];
            let y = v[2];
            (!s && x) || (s && y)
        })
    }

    /// Implies: x₁ → x₂
    pub fn implies() -> TruthTable {
        TruthTable::from_expr(2, |x| !x[0] || x[1])
    }

    /// Equivalence: x₁ ↔ x₂
    pub fn equiv() -> TruthTable {
        TruthTable::from_expr(2, |x| x[0] == x[1])
    }

    /// Half adder sum: x₁ ⊕ x₂
    pub fn half_adder_sum() -> TruthTable {
        TruthTable::from_expr(2, |x| x[0] ^ x[1])
    }

    /// Half adder carry: x₁ ∧ x₂
    pub fn half_adder_carry() -> TruthTable {
        TruthTable::from_expr(2, |x| x[0] && x[1])
    }

    /// Full adder sum: x₁ ⊕ x₂ ⊕ x₃
    pub fn full_adder_sum() -> TruthTable {
        TruthTable::from_expr(3, |x| (x[0] ^ x[1]) ^ x[2])
    }

    /// Full adder carry: (x₁ ∧ x₂) ∨ (x₂ ∧ x₃) ∨ (x₁ ∧ x₃)
    pub fn full_adder_carry() -> TruthTable {
        TruthTable::from_expr(3, |x| (x[0] && x[1]) || (x[1] && x[2]) || (x[0] && x[2]))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_constant_functions() {
        let zero = TruthTable::zero(3);
        let one = TruthTable::one(3);

        assert!(zero.is_zero());
        assert!(!zero.is_one());
        assert!(one.is_one());
        assert!(!one.is_zero());

        // Constants have no essential variables
        assert!(zero.essential_vars().is_empty());
        assert!(one.essential_vars().is_empty());
    }

    #[test]
    fn test_projection() {
        let x1 = TruthTable::var(3, Var(1));
        let x2 = TruthTable::var(3, Var(2));

        // x₁ is essential for projection x₁
        assert!(x1.is_essential(Var(1)));
        assert!(!x1.is_essential(Var(2)));
        assert!(!x1.is_essential(Var(3)));

        // x₂ is essential for projection x₂
        assert!(!x2.is_essential(Var(1)));
        assert!(x2.is_essential(Var(2)));
    }

    #[test]
    fn test_boolean_ops() {
        let x1 = TruthTable::var(2, Var(1));
        let x2 = TruthTable::var(2, Var(2));

        let and = x1.and(&x2);
        let or = x1.or(&x2);
        let xor = x1.xor(&x2);

        // AND: only (1,1) is true
        assert!(!and.eval(&[false, false]));
        assert!(!and.eval(&[true, false]));
        assert!(!and.eval(&[false, true]));
        assert!(and.eval(&[true, true]));

        // OR: only (0,0) is false
        assert!(!or.eval(&[false, false]));
        assert!(or.eval(&[true, false]));
        assert!(or.eval(&[false, true]));
        assert!(or.eval(&[true, true]));

        // XOR: true when inputs differ
        assert!(!xor.eval(&[false, false]));
        assert!(xor.eval(&[true, false]));
        assert!(xor.eval(&[false, true]));
        assert!(!xor.eval(&[true, true]));
    }

    #[test]
    fn test_cofactor() {
        let f = TruthTable::from_expr(2, |x| x[0] && x[1]); // x₁ ∧ x₂

        let f_x1_0 = f.cofactor(Var(1), false); // 0 ∧ x₂ = 0
        let f_x1_1 = f.cofactor(Var(1), true); // 1 ∧ x₂ = x₂

        assert!(f_x1_0.is_zero());
        assert!(!f_x1_1.is_zero());
        assert!(!f_x1_1.is_one());

        // f|_{x₁=1} should equal x₂ (as a 1-variable function)
        assert!(!f_x1_1.eval(&[false]));
        assert!(f_x1_1.eval(&[true]));
    }

    #[test]
    fn test_named_functions() {
        let maj = named::majority3();
        assert!(!maj.eval(&[false, false, false]));
        assert!(!maj.eval(&[true, false, false]));
        assert!(maj.eval(&[true, true, false]));
        assert!(maj.eval(&[true, true, true]));

        let parity = named::xor_all(3);
        assert!(!parity.eval(&[false, false, false]));
        assert!(parity.eval(&[true, false, false]));
        assert!(!parity.eval(&[true, true, false]));
        assert!(parity.eval(&[true, true, true]));
    }

    #[test]
    fn test_essential_vars() {
        // f = x₁ ∧ x₂ (both essential)
        let f = TruthTable::from_expr(3, |x| x[0] && x[1]);
        let ess = f.essential_vars();
        assert_eq!(ess.len(), 2);
        assert!(ess.contains(Var(1)));
        assert!(ess.contains(Var(2)));
        assert!(!ess.contains(Var(3)));
    }
}
