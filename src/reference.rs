use std::fmt::{Display, Formatter};
use std::ops::Neg;

#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash)]
#[repr(transparent)]
pub struct Ref(i32);

//noinspection RsAssertEqual (see https://github.com/rust-lang/rust/issues/119826)
impl Ref {
    pub const ZERO: Self = Self(0);

    pub const fn new(value: i32) -> Self {
        assert!(value != 0, "Reference cannot be zero, use Ref::ZERO instead");
        Self(value)
    }
    pub const fn positive(value: u32) -> Self {
        assert!(value != 0, "Reference cannot be zero, use Ref::ZERO instead");
        Self(value as i32)
    }
    pub const fn negative(value: u32) -> Self {
        assert!(value != 0, "Reference cannot be zero, use Ref::ZERO instead");
        Self(-(value as i32))
    }

    pub const fn index(self) -> u32 {
        self.0.unsigned_abs()
    }
    pub const fn is_negated(self) -> bool {
        self.0 < 0
    }

    pub(crate) const fn hashy(self) -> u64 {
        (self.index() << 1) as u64 | self.is_negated() as u64
        // self.index() as u64
    }
}

// -Ref
impl Neg for Ref {
    type Output = Self;

    fn neg(self) -> Self::Output {
        Self(-self.0)
    }
}

impl Display for Ref {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}@{}", if self.is_negated() { "~" } else { "" }, self.index())
    }
}
