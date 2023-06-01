use std::fmt::{Display, Formatter};
use std::ops::Neg;

// TODO: refactor
#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash)]
pub struct Ref(i32);

impl Ref {
    pub const fn new(index: i32) -> Self {
        // assert_ne!(index, 0);
        Self(index)
    }

    pub const fn is_negated(&self) -> bool {
        self.0 < 0
    }

    pub const fn negate(self) -> Self {
        Self(-self.0)
    }

    /// Return the internal representation of the reference.
    pub const fn get(self) -> i32 {
        self.0
    }

    pub const fn abs(self) -> u32 {
        self.0.abs() as u32
    }

    /// Return the index of the reference.
    // TODO: change to return u32
    pub const fn index(self) -> usize {
        self.0.abs() as usize
    }

    // TODO: rename
    pub(crate) fn as_lit(self) -> u32 {
        ((self.0.abs() as u32) << 1) + (self.0 < 0) as u32
    }
}

impl Neg for Ref {
    type Output = Self;

    fn neg(self) -> Self::Output {
        self.negate()
    }
}

impl Display for Ref {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}@{}",
            if self.is_negated() { "~" } else { "" },
            self.abs()
        )
    }
}
