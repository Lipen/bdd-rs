use std::fmt::{Debug, Display, Formatter};
use std::ops::Not;

#[derive(Copy, Clone, Eq, PartialEq, Hash)]
pub struct Signal(u32);

const MAGIC: u32 = 1 << 31; // 0x8000_0000

// Constructors
impl Signal {
    pub const fn zero() -> Self {
        Self(0)
    }

    pub const fn one() -> Self {
        Self(1)
    }

    pub(crate) const fn placeholder() -> Self {
        Self(MAGIC)
    }

    pub const fn from_index(index: u32) -> Self {
        // Note: index 0 is reserved for constant 0.
        Self(index << 1)
    }

    pub const fn from_var(var: u32) -> Self {
        Self::from_index(var + 1)
    }

    pub const fn from_input(input: u32) -> Self {
        Self::from_index(!input)
    }
}

// Getters
impl Signal {
    pub(crate) const fn raw(self) -> u32 {
        self.0
    }

    pub const fn index(&self) -> u32 {
        // Returns 0 for constant zero, else var+1.
        self.0 >> 1
    }

    pub const fn var(&self) -> u32 {
        assert!(self.is_var());
        self.index() - 1
    }

    pub const fn input(&self) -> u32 {
        assert!(self.is_input());
        !self.index() & !MAGIC
    }
}

// Checks
impl Signal {
    pub const fn is_const(&self) -> bool {
        self.index() == 0
    }

    pub const fn is_input(&self) -> bool {
        self.0 & MAGIC != 0
    }

    pub const fn is_var(&self) -> bool {
        !self.is_input() && !self.is_const()
    }

    pub const fn is_negated(&self) -> bool {
        // False for inputs, variables, zero.
        // True for complement, one.
        self.0 & 1 != 0
    }
}

impl From<bool> for Signal {
    fn from(b: bool) -> Self {
        if b {
            Self::one()
        } else {
            Self::zero()
        }
    }
}

impl Not for Signal {
    type Output = Self;

    fn not(self) -> Self::Output {
        Self(self.0 ^ 1)
    }
}

impl Not for &Signal {
    type Output = Signal;

    fn not(self) -> Self::Output {
        Signal(self.0 ^ 1)
    }
}

impl Display for Signal {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        if self.is_const() {
            let x = self.0 & 1;
            write!(f, "{}", x)
        } else {
            if self.is_negated() {
                write!(f, "!")?;
            }
            if *self == Signal::placeholder() {
                write!(f, "#")
            } else if self.is_input() {
                let i = self.input();
                write!(f, "i{}", i)
            } else {
                let v = self.var();
                write!(f, "v{}", v)
            }
        }
    }
}

impl Debug for Signal {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        Display::fmt(self, f)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_const() {
        let zero = Signal::zero();
        let one = Signal::one();

        assert!(zero.is_const());
        assert!(one.is_const());

        assert_eq!(zero, !one);
        assert_eq!(one, !zero);

        assert!(!zero.is_negated());
        assert!(one.is_negated());

        assert!(!zero.is_input());
        assert!(!zero.is_var());
        assert!(!one.is_input());
        assert!(!one.is_var());
    }
}
