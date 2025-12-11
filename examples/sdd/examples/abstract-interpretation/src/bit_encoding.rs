//! Bit encoding for converting integer values to bit vectors
//!
//! Maps integers 0-7 to 3-bit binary representations for use in SDDs.
//! Each variable in the program becomes a 3-bit SDD variable.

use std::collections::HashMap;

use crate::language::Var;

/// A bit vector representing the bit values of a variable
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct BitVector {
    pub bits: [bool; 3], // 3 bits for values 0-7
}

impl BitVector {
    /// Create from integer value (0-7)
    pub fn from_value(val: i32) -> Self {
        let v = (val & 0x7) as u8; // Ensure 0-7 range
        BitVector {
            bits: [(v & 1) != 0, (v & 2) != 0, (v & 4) != 0],
        }
    }

    /// Convert back to integer value
    pub fn to_value(&self) -> i32 {
        let mut val = 0i32;
        if self.bits[0] {
            val |= 1;
        }
        if self.bits[1] {
            val |= 2;
        }
        if self.bits[2] {
            val |= 4;
        }
        val
    }

    /// Get individual bit (0, 1, or 2)
    pub fn bit(&self, index: usize) -> bool {
        self.bits[index]
    }
}

/// Maps program variables to SDD variable ranges
#[derive(Debug)]
pub struct BitEncoding {
    /// Map from program variable to its starting SDD variable index
    /// Each program variable gets 3 SDD variables for its bits
    var_to_sdd_start: HashMap<Var, usize>,
    /// Total number of SDD variables needed
    num_sdd_vars: usize,
}

impl BitEncoding {
    /// Create a bit encoding for program variables
    pub fn new(vars: &[Var]) -> Self {
        let mut var_to_sdd_start = HashMap::new();
        let mut num_sdd_vars = 0;

        for var in vars {
            var_to_sdd_start.insert(*var, num_sdd_vars);
            num_sdd_vars += 3; // Each variable uses 3 bits
        }

        BitEncoding {
            var_to_sdd_start,
            num_sdd_vars,
        }
    }

    /// Get SDD variable indices for a program variable
    pub fn sdd_vars_for(&self, var: Var) -> Vec<usize> {
        if let Some(&start) = self.var_to_sdd_start.get(&var) {
            vec![start, start + 1, start + 2]
        } else {
            vec![]
        }
    }

    /// Get program variable from SDD variable index
    pub fn var_from_sdd(&self, sdd_var: usize) -> Option<Var> {
        for (&pvar, &start) in &self.var_to_sdd_start {
            if sdd_var >= start && sdd_var < start + 3 {
                return Some(pvar);
            }
        }
        None
    }

    /// Get which bit (0, 1, or 2) this SDD variable represents
    pub fn bit_index_for_sdd(&self, sdd_var: usize) -> Option<usize> {
        for &start in self.var_to_sdd_start.values() {
            if sdd_var >= start && sdd_var < start + 3 {
                return Some(sdd_var - start);
            }
        }
        None
    }

    /// Total number of SDD variables needed
    pub fn num_sdd_vars(&self) -> usize {
        self.num_sdd_vars
    }

    /// Get all program variables in order
    pub fn program_vars(&self) -> Vec<Var> {
        let mut vars: Vec<_> = self.var_to_sdd_start.keys().copied().collect();
        vars.sort_unstable();
        vars
    }

    /// Create a mapping from variable assignment to SDD literals
    pub fn encode_assignment(&self, var: Var, value: i32) -> Vec<i32> {
        let bits = BitVector::from_value(value);
        let mut sdd_lits = Vec::new();

        if let Some(&start) = self.var_to_sdd_start.get(&var) {
            for i in 0..3 {
                let sdd_var = start + i + 1; // SDD variables are 1-indexed
                if bits.bits[i] {
                    sdd_lits.push(sdd_var as i32);
                } else {
                    sdd_lits.push(-(sdd_var as i32));
                }
            }
        }

        sdd_lits
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_bitvector() {
        assert_eq!(BitVector::from_value(0).to_value(), 0);
        assert_eq!(BitVector::from_value(5).to_value(), 5);
        assert_eq!(BitVector::from_value(7).to_value(), 7);
    }

    #[test]
    fn test_bit_encoding() {
        let vars = vec![Var::new(1), Var::new(2), Var::new(3)];
        let enc = BitEncoding::new(&vars);

        assert_eq!(enc.num_sdd_vars(), 9); // 3 variables * 3 bits each
        assert_eq!(enc.sdd_vars_for(Var::new(1)), vec![0, 1, 2]);
        assert_eq!(enc.sdd_vars_for(Var::new(2)), vec![3, 4, 5]);
        assert_eq!(enc.sdd_vars_for(Var::new(3)), vec![6, 7, 8]);
    }

    #[test]
    fn test_encode_assignment() {
        let vars = vec![Var::new(1)];
        let enc = BitEncoding::new(&vars);

        let lits = enc.encode_assignment(Var::new(1), 5);
        assert_eq!(lits.len(), 3);
        // 5 = 0b101, so bits [1, 0, 1]
        assert_eq!(lits[0], 1); // bit 0 set
        assert_eq!(lits[1], -2); // bit 1 not set
        assert_eq!(lits[2], 3); // bit 2 set
    }
}
