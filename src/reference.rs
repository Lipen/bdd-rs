use std::fmt::{Display, Formatter};
use std::ops::Neg;

#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash)]
pub struct Ref(u32);

impl Ref {
    pub const fn new(index: i32) -> Self {
        // assert_ne!(index, 0);
        Self((index.unsigned_abs() << 1) + (index < 0) as u32)
    }
    pub const fn positive(index: u32) -> Self {
        // assert_ne!(index, 0);
        Self(index << 1)
    }
    pub const fn negative(index: u32) -> Self {
        // assert_ne!(index, 0);
        Self((index << 1) + 1)
    }

    pub const fn is_negated(&self) -> bool {
        self.0 & 1 == 1
    }

    pub const fn negate(self) -> Self {
        Self(self.0 ^ 1)
    }

    pub const fn inner(self) -> u32 {
        self.0
    }
    pub const fn index(self) -> u32 {
        self.0 >> 1
    }
    pub const fn get(self) -> i32 {
        let value = self.index() as i32;
        if self.is_negated() {
            -value
        } else {
            value
        }
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
