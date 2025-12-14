use std::fmt::{Display, Formatter};
use std::ops::Neg;

use crate::types::NodeId;

/// A reference to a BDD node, potentially negated.
///
/// Uses a 32-bit representation where the least significant bit indicates negation
/// and the remaining bits store the node ID.
#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash)]
#[repr(transparent)]
pub struct Ref(u32);

impl Ref {
    /// Sentinel value representing an invalid/uninitialized reference.
    /// Uses maximum u32 value - we don't care about index/sign interpretation for sentinels.
    pub const INVALID: Self = Self(0xFFFF_FFFF);

    /// Creates a new reference with the given node ID and negation flag.
    pub const fn new(id: NodeId, negated: bool) -> Self {
        Self((id.raw() << 1) | (negated as u32))
    }

    /// Creates a positive (non-negated) reference.
    pub const fn positive(id: NodeId) -> Self {
        Self::new(id, false)
    }

    /// Creates a negative (negated) reference.
    pub const fn negative(id: NodeId) -> Self {
        Self::new(id, true)
    }

    pub fn positive_from(id: impl Into<NodeId>) -> Self {
        Self::new(id.into(), false)
    }

    pub fn negative_from(id: impl Into<NodeId>) -> Self {
        Self::new(id.into(), true)
    }

    /// Returns the node ID this reference points to.
    #[inline]
    pub const fn id(self) -> NodeId {
        // SAFETY: The index is always < 0x7FFF_FFFF due to the check in `NodeId::new`.
        // Note: Ref::INVALID (0xFFFF_FFFF) becomes NodeId::INVALID (0x7FFF_FFFF) here,
        //       which is acceptable.
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

impl Default for Ref {
    fn default() -> Self {
        Self::INVALID
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_ref_positive_negative() {
        let id = NodeId::new(42);

        let pos = Ref::positive(id);
        assert_eq!(pos.id(), id);
        assert!(!pos.is_negated());

        let neg = Ref::negative(id);
        assert_eq!(neg.id(), id);
        assert!(neg.is_negated());

        // Same ID, different polarity
        assert_eq!(pos.id(), neg.id());
        assert_ne!(pos, neg);
    }

    #[test]
    fn test_ref_new() {
        let id = NodeId::new(123);

        let pos = Ref::new(id, false);
        assert_eq!(pos.id(), id);
        assert!(!pos.is_negated());

        let neg = Ref::new(id, true);
        assert_eq!(neg.id(), id);
        assert!(neg.is_negated());
    }

    #[test]
    fn test_ref_from_helpers() {
        let pos = Ref::positive_from(10u32);
        assert_eq!(pos.id(), NodeId::new(10));
        assert!(!pos.is_negated());

        let neg = Ref::negative_from(20u32);
        assert_eq!(neg.id(), NodeId::new(20));
        assert!(neg.is_negated());
    }

    #[test]
    fn test_ref_negation() {
        let id = NodeId::new(5);
        let pos = Ref::positive(id);
        let neg = Ref::negative(id);

        // Negating positive gives negative
        assert_eq!(-pos, neg);
        // Negating negative gives positive
        assert_eq!(-neg, pos);
        // Double negation is identity
        assert_eq!(-(-pos), pos);
        assert_eq!(-(-neg), neg);
    }

    #[test]
    fn test_ref_raw() {
        // Raw encoding: (id << 1) | negated
        let id = NodeId::new(100);

        let pos = Ref::positive(id);
        assert_eq!(pos.raw(), 100 << 1); // 200

        let neg = Ref::negative(id);
        assert_eq!(neg.raw(), (100 << 1) | 1); // 201
    }

    #[test]
    fn test_ref_display() {
        let id = NodeId::new(42);

        let pos = Ref::positive(id);
        assert_eq!(format!("{}", pos), "@42");

        let neg = Ref::negative(id);
        assert_eq!(format!("{}", neg), "~@42");
    }

    #[test]
    fn test_ref_equality() {
        let id1 = NodeId::new(10);
        let id2 = NodeId::new(20);

        let r1 = Ref::positive(id1);
        let r2 = Ref::positive(id1);
        let r3 = Ref::negative(id1);
        let r4 = Ref::positive(id2);

        // Same node, same polarity
        assert_eq!(r1, r2);
        // Same node, different polarity
        assert_ne!(r1, r3);
        // Different node
        assert_ne!(r1, r4);
    }

    #[test]
    fn test_ref_hash() {
        use std::collections::HashSet;

        let mut set = HashSet::new();
        let id = NodeId::new(7);

        let pos = Ref::positive(id);
        let neg = Ref::negative(id);

        set.insert(pos);
        assert!(set.contains(&pos));
        assert!(!set.contains(&neg));

        set.insert(neg);
        assert!(set.contains(&pos));
        assert!(set.contains(&neg));
        assert_eq!(set.len(), 2);
    }

    #[test]
    fn test_ref_copy_clone() {
        let r = Ref::positive(NodeId::new(99));
        let copied = r; // Copy
        let cloned = r.clone(); // Clone

        assert_eq!(r, copied);
        assert_eq!(r, cloned);
    }

    #[test]
    fn test_ref_debug() {
        let r = Ref::positive(NodeId::new(5));
        let debug_str = format!("{:?}", r);
        assert!(debug_str.contains("Ref"));
    }

    #[test]
    fn test_ref_large_id() {
        // Test with a large but valid node ID
        let large_id = NodeId::new(0x3FFF_FFFF); // Max valid ID
        let pos = Ref::positive(large_id);
        let neg = Ref::negative(large_id);

        assert_eq!(pos.id(), large_id);
        assert_eq!(neg.id(), large_id);
        assert!(!pos.is_negated());
        assert!(neg.is_negated());
        assert_eq!(-pos, neg);
    }
}
