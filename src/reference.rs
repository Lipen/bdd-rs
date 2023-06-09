use std::fmt::{Display, Formatter};
use std::ops::Neg;

#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash)]
pub struct Ref(i32);

impl Ref {
    pub const fn new(value: i32) -> Self {
        Self(value)
    }
    pub const fn positive(value: u32) -> Self {
        Self(value as i32)
    }
    pub const fn negative(value: u32) -> Self {
        Self(-(value as i32))
    }
    pub(crate) const fn zero() -> Self {
        Self(0)
    }

    pub const fn is_negated(&self) -> bool {
        self.0 < 0
    }

    pub const fn negate(self) -> Self {
        Self(-self.0)
    }

    pub const fn index(self) -> u32 {
        self.0.unsigned_abs()
    }
    pub const fn signed(self) -> i32 {
        self.0
    }
    pub const fn unsigned(self) -> u32 {
        self.index() + self.is_negated() as u32
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
            self.index()
        )
    }
}
