use std::ops::Neg;

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

    pub const fn get(self) -> i32 {
        self.0
    }

    pub const fn abs(self) -> u32 {
        self.0.abs() as u32
    }

    pub const fn index(self) -> usize {
        self.0.abs() as usize
    }
}

impl Neg for Ref {
    type Output = Self;

    fn neg(self) -> Self::Output {
        self.negate()
    }
}
