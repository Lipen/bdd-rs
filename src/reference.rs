use std::fmt::{Display, Formatter};
use std::ops::Neg;

#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash)]
#[repr(transparent)]
pub struct Ref(u32);

impl Ref {
    pub const ZERO: Self = Self(0);

    pub const fn new(index: u32, negated: bool) -> Self {
        debug_assert!(index < 0x8000_0000, "Index is too large");
        debug_assert!(index != 0, "Index is zero, use Ref::ZERO instead");
        Self((index << 1) | (negated as u32))
    }
    pub const fn positive(index: u32) -> Self {
        Self::new(index, false)
    }
    pub const fn negative(index: u32) -> Self {
        Self::new(index, true)
    }
    pub const fn index(self) -> u32 {
        self.0 >> 1
    }
    pub const fn is_negated(self) -> bool {
        (self.0 & 1) != 0
    }

    pub(crate) const fn hashy(self) -> u64 {
        self.0 as u64
    }
}

// -Ref
impl Neg for Ref {
    type Output = Self;

    fn neg(self) -> Self::Output {
        Self(self.0 ^ 1)
    }
}

impl Display for Ref {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}@{}", if self.is_negated() { "~" } else { "" }, self.index())
    }
}
