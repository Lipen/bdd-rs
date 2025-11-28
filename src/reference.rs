use std::fmt::{Display, Formatter};
use std::ops::Neg;

use crate::types::NodeId;

#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash)]
#[repr(transparent)]
pub struct Ref(u32);

impl Ref {
    /// Sentinel value representing an invalid/uninitialized reference.
    /// Uses maximum u32 value - we don't care about index/sign interpretation for sentinels.
    pub const INVALID: Self = Self(0xFFFF_FFFF);

    /// Creates a new reference with the given node ID and negation flag.
    pub fn new(id: impl Into<NodeId>, negated: bool) -> Self {
        Self((id.into().raw() << 1) | (negated as u32))
    }

    /// Creates a positive (non-negated) reference.
    pub fn positive(id: impl Into<NodeId>) -> Self {
        Self::new(id, false)
    }

    /// Creates a negative (negated) reference.
    pub fn negative(id: impl Into<NodeId>) -> Self {
        Self::new(id, true)
    }

    /// Returns the node ID this reference points to.
    #[inline]
    pub const fn id(self) -> NodeId {
        // SAFETY: The index is always < 0x7FFF_FFFF due to the check in `new`
        unsafe { NodeId::from_raw_unchecked(self.0 >> 1) }
    }

    /// Returns true if this reference is negated.
    #[inline]
    pub const fn is_negated(self) -> bool {
        (self.0 & 1) != 0
    }

    /// Returns the raw underlying value.
    #[inline]
    pub const fn raw(self) -> u32 {
        self.0
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
        if self.is_negated() {
            write!(f, "~{}", self.id())
        } else {
            write!(f, "{}", self.id())
        }
    }
}
