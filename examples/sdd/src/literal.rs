//! Boolean literal representation.
//!
//! A literal is a variable or its negation. This module provides
//! a space-efficient representation using a single `i32`.

use std::fmt::{self, Display};
use std::ops::Neg;

/// A Boolean literal (variable or its negation).
///
/// Internally stored as a signed integer where:
/// - Positive values represent positive literals (variable)
/// - Negative values represent negative literals (negated variable)
/// - Zero is not a valid literal
///
/// # Examples
///
/// ```
/// use sdd::Literal;
///
/// let x = Literal::positive(1);  // x₁
/// let neg_x = Literal::negative(1);  // ¬x₁
///
/// assert_eq!(-x, neg_x);
/// assert_eq!(x.var(), 1);
/// assert!(x.is_positive());
/// assert!(neg_x.is_negative());
/// ```
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Literal(i32);

impl Literal {
    pub const ZERO: Self = Self(0);

    /// Creates a positive literal for the given variable.
    ///
    /// # Panics
    ///
    /// Panics if `var` is zero.
    #[inline]
    pub const fn positive(var: u32) -> Self {
        assert!(var > 0, "Variable must be positive (1-indexed)");
        Self(var as i32)
    }

    /// Creates a negative literal for the given variable.
    ///
    /// # Panics
    ///
    /// Panics if `var` is zero.
    #[inline]
    pub const fn negative(var: u32) -> Self {
        assert!(var > 0, "Variable must be positive (1-indexed)");
        Self(-(var as i32))
    }

    /// Creates a literal from a signed integer.
    ///
    /// Positive values create positive literals, negative values create negative literals.
    ///
    /// # Panics
    ///
    /// Panics if `lit` is zero.
    #[inline]
    pub const fn from_i32(lit: i32) -> Self {
        assert!(lit != 0, "Literal cannot be zero");
        Self(lit)
    }

    /// Returns the underlying variable (always positive).
    #[inline]
    pub const fn var(self) -> u32 {
        self.0.unsigned_abs()
    }

    /// Returns true if this is a positive literal.
    #[inline]
    pub const fn is_positive(self) -> bool {
        self.0 > 0
    }

    /// Returns true if this is a negative literal.
    #[inline]
    pub const fn is_negative(self) -> bool {
        self.0 < 0
    }

    /// Returns the polarity: `true` for positive, `false` for negative.
    #[inline]
    pub const fn polarity(self) -> bool {
        self.is_positive()
    }

    /// Returns the negation of this literal.
    #[inline]
    pub const fn negate(self) -> Self {
        Self(-self.0)
    }

    /// Returns the raw signed integer representation.
    #[inline]
    pub const fn raw(self) -> i32 {
        self.0
    }
}

// -Literal
impl Neg for Literal {
    type Output = Self;

    #[inline]
    fn neg(self) -> Self::Output {
        self.negate()
    }
}

impl From<i32> for Literal {
    fn from(lit: i32) -> Self {
        Self::from_i32(lit)
    }
}

// Into<i32> for Literal
impl From<Literal> for i32 {
    fn from(lit: Literal) -> Self {
        lit.0
    }
}

impl Display for Literal {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.is_positive() {
            write!(f, "x{}", self.var())
        } else {
            write!(f, "¬x{}", self.var())
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_positive_literal() {
        let lit = Literal::positive(3);
        assert_eq!(lit.var(), 3);
        assert!(lit.is_positive());
        assert!(!lit.is_negative());
        assert_eq!(lit.raw(), 3);
    }

    #[test]
    fn test_negative_literal() {
        let lit = Literal::negative(3);
        assert_eq!(lit.var(), 3);
        assert!(!lit.is_positive());
        assert!(lit.is_negative());
        assert_eq!(lit.raw(), -3);
    }

    #[test]
    fn test_negation() {
        let pos = Literal::positive(5);
        let neg = -pos;
        assert_eq!(neg, Literal::negative(5));
        assert_eq!(-neg, pos);
    }

    #[test]
    fn test_display() {
        assert_eq!(format!("{}", Literal::positive(1)), "x1");
        assert_eq!(format!("{}", Literal::negative(2)), "¬x2");
    }

    #[test]
    #[should_panic(expected = "Variable must be positive")]
    fn test_zero_var_positive() {
        Literal::positive(0);
    }

    #[test]
    #[should_panic(expected = "Literal cannot be zero")]
    fn test_zero_literal() {
        Literal::from_i32(0);
    }
}
