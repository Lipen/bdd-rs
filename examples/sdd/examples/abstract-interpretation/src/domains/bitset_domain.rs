//! Bitset abstract domain for comparison with SDD
//!
//! Tracks exact set of possible values for each variable (0-7 range)

use std::collections::HashMap;

use crate::language::Var;

/// Abstract state using bitset domain
#[derive(Debug, Clone)]
pub struct BitsetDomain {
    bitsets: HashMap<Var, u8>, // 8 bits for values 0-7
}

impl BitsetDomain {
    /// Create top state (all values possible)
    pub fn top() -> Self {
        BitsetDomain { bitsets: HashMap::new() }
    }

    /// Create bottom state (no values possible)
    pub fn bottom() -> Self {
        BitsetDomain {
            bitsets: {
                let mut map = HashMap::new();
                map.insert(Var::new(1), 0); // Mark as bottom with empty set
                map
            },
        }
    }

    /// Set possible values for variable
    pub fn set_values(&mut self, var: Var, bitset: u8) {
        self.bitsets.insert(var, bitset);
    }

    /// Get possible values for variable
    pub fn get_values(&self, var: Var) -> u8 {
        self.bitsets.get(&var).copied().unwrap_or(0xFF) // 0xFF = all values
    }

    /// Check if value is possible
    pub fn contains(&self, var: Var, value: i32) -> bool {
        let v = (value & 0x7) as u8;
        let bitset = self.get_values(var);
        (bitset & (1 << v)) != 0
    }

    /// Add value to possibility set
    pub fn add_value(&mut self, var: Var, value: i32) {
        let v = (value & 0x7) as u8;
        let bitset = self.get_values(var);
        self.bitsets.insert(var, bitset | (1 << v));
    }

    /// Remove value from possibility set
    pub fn remove_value(&mut self, var: Var, value: i32) {
        let v = (value & 0x7) as u8;
        let bitset = self.get_values(var);
        self.bitsets.insert(var, bitset & !(1 << v));
    }

    /// Check if bottom
    pub fn is_bottom(&self) -> bool {
        for &bitset in self.bitsets.values() {
            if bitset == 0 {
                return true;
            }
        }
        false
    }

    /// Join two bitset domains
    pub fn join(&self, other: &BitsetDomain) -> BitsetDomain {
        let mut result = BitsetDomain::top();

        let all_vars: std::collections::HashSet<_> = self.bitsets.keys().chain(other.bitsets.keys()).copied().collect();

        for var in all_vars {
            let bits1 = self.get_values(var);
            let bits2 = other.get_values(var);
            result.set_values(var, bits1 | bits2);
        }

        result
    }

    /// Size approximation (for comparison)
    pub fn approx_size(&self) -> usize {
        let mut size = 1;
        for &bitset in self.bitsets.values() {
            size *= bitset.count_ones() as usize;
        }
        size.max(1)
    }

    pub fn summary(&self) -> String {
        if self.is_bottom() {
            "⊥ (bottom)".to_string()
        } else if self.bitsets.is_empty() {
            "T (top)".to_string()
        } else {
            let mut parts = Vec::new();
            let mut vars: Vec<_> = self.bitsets.keys().collect();
            vars.sort();
            for var in vars {
                let bitset = self.bitsets[var];
                let mut values = Vec::new();
                for i in 0..8 {
                    if (bitset & (1 << i)) != 0 {
                        values.push(i.to_string());
                    }
                }
                if values.is_empty() {
                    parts.push(format!("{}=∅", var));
                } else if values.len() == 8 {
                    parts.push(format!("{}=*", var));
                } else {
                    parts.push(format!("{}∈{{{}}}", var, values.join(",")));
                }
            }
            parts.join(", ")
        }
    }
}
