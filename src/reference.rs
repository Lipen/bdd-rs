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
        signed_to_lit(self.0)
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

pub(crate) fn signed_to_lit(value: i32) -> u32 {
    (value.unsigned_abs() << 1) + (value < 0) as u32
}
