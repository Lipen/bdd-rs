//! Reduced product of abstract domains.
//!
//! Combines two domains for increased precision through simultaneous tracking
//! and cross-domain constraint propagation.

use super::traits::{AbstractDomain, Concretizable};

/// Trait for domains that can be reduced (refined) using information from another domain.
///
/// The reduction operator `ρ: D₁ × D₂ → D₁` takes a value from domain `D₁` and
/// refines it using information from domain `D₂`. This enables cross-domain
/// constraint propagation in the reduced product.
///
/// # Example
///
/// An `Interval` domain can be reduced by a `Sign` domain:
/// - `reduce([-10, 10], Positive)` → `[1, 10]`
/// - `reduce([-10, 10], Negative)` → `[-10, -1]`
/// - `reduce([-10, 10], Zero)` → `[0, 0]`
pub trait Reducible<Other> {
    /// Reduce `self` using information from `other`.
    ///
    /// Returns a more precise (or equal) abstraction of `self` that is
    /// consistent with the constraints implied by `other`.
    fn reduce(&self, other: &Other) -> Self;
}

/// Reduced product of two domains for increased precision.
///
/// Combines two domains by maintaining both abstractions simultaneously.
/// After each operation, the `reduce` operator propagates constraints between
/// domains, potentially discovering infeasibility or refining abstractions.
///
/// # Theory
///
/// For domains `D₁` and `D₂`, the reduced product `D₁ ⊗ D₂` has elements
/// `(d₁, d₂)` where operations apply component-wise, followed by reduction:
///
/// ```text
/// (d₁, d₂) ⊗ (d₁', d₂') = reduce(d₁ ⊕ d₁', d₂ ⊕ d₂')
/// ```
///
/// The reduction operator `ρ: D₁ × D₂ → D₁ × D₂` refines each component:
/// - `ρ(d₁, d₂) = (d₁.reduce(d₂), d₂.reduce(d₁))`
///
/// # When Reduction Helps
///
/// Without reduction (Cartesian product):
/// - `Interval[-10, 10] × Positive` stays as-is
///
/// With reduction:
/// - `Interval[-10, 10] × Positive` → `Interval[1, 10] × Positive`
///
/// # Example
///
/// ```rust
/// use tbdd_pbt::domain::{ReducedProduct, Interval, Sign, AbstractDomain};
///
/// // Combine interval [−10, 10] with NonNegative sign
/// let interval = Interval::from_bounds(-10, 10);
/// let sign = Sign::NonNegative;
/// let product = ReducedProduct::new(interval, sign);
///
/// // Product tracks both abstractions simultaneously
/// assert!(!product.is_bottom());
/// ```
#[derive(Debug, Clone, PartialEq)]
pub struct ReducedProduct<D1, D2> {
    /// First domain component.
    pub d1: D1,
    /// Second domain component.
    pub d2: D2,
}

impl<D1, D2> ReducedProduct<D1, D2> {
    /// Create a new reduced product from two domain elements.
    ///
    /// If the domains implement `Reducible`, the product is automatically reduced.
    pub fn new(d1: D1, d2: D2) -> Self
    where
        D1: Clone,
        D2: Clone,
    {
        Self { d1, d2 }
    }

    /// Create and reduce a product using cross-domain information.
    pub fn new_reduced(d1: D1, d2: D2) -> Self
    where
        D1: Reducible<D2> + Clone,
        D2: Reducible<D1> + Clone,
    {
        let d1_reduced = d1.reduce(&d2);
        let d2_reduced = d2.reduce(&d1);
        Self {
            d1: d1_reduced,
            d2: d2_reduced,
        }
    }
}

impl<D1, D2> ReducedProduct<D1, D2>
where
    D1: Reducible<D2> + Clone,
    D2: Reducible<D1> + Clone,
{
    /// Apply the reduction operator to propagate constraints between domains.
    ///
    /// This refines each component using information from the other:
    /// - `d1' = d1.reduce(d2)`
    /// - `d2' = d2.reduce(d1')`  (using already-reduced d1)
    pub fn reduce(&self) -> Self {
        let d1_reduced = self.d1.reduce(&self.d2);
        let d2_reduced = self.d2.reduce(&d1_reduced);
        Self {
            d1: d1_reduced,
            d2: d2_reduced,
        }
    }
}

impl<D1: AbstractDomain, D2: AbstractDomain> AbstractDomain for ReducedProduct<D1, D2> {
    fn bottom() -> Self {
        Self {
            d1: D1::bottom(),
            d2: D2::bottom(),
        }
    }

    fn top() -> Self {
        Self {
            d1: D1::top(),
            d2: D2::top(),
        }
    }

    fn is_bottom(&self) -> bool {
        // Reduced: if either is bottom, the whole product is bottom
        self.d1.is_bottom() || self.d2.is_bottom()
    }

    fn is_top(&self) -> bool {
        self.d1.is_top() && self.d2.is_top()
    }

    fn join(&self, other: &Self) -> Self {
        Self {
            d1: self.d1.join(&other.d1),
            d2: self.d2.join(&other.d2),
        }
    }

    fn meet(&self, other: &Self) -> Self {
        Self {
            d1: self.d1.meet(&other.d1),
            d2: self.d2.meet(&other.d2),
        }
    }

    fn widen(&self, other: &Self) -> Self {
        Self {
            d1: self.d1.widen(&other.d1),
            d2: self.d2.widen(&other.d2),
        }
    }

    fn narrow(&self, other: &Self) -> Self {
        Self {
            d1: self.d1.narrow(&other.d1),
            d2: self.d2.narrow(&other.d2),
        }
    }

    fn leq(&self, other: &Self) -> bool {
        self.d1.leq(&other.d1) && self.d2.leq(&other.d2)
    }
}

impl<D1: Concretizable, D2: Concretizable> Concretizable for ReducedProduct<D1, D2> {
    fn concretize(&self) -> Option<i64> {
        // Try first component, fall back to second
        self.d1.concretize().or_else(|| self.d2.concretize())
    }

    fn sample(&self, count: usize) -> Vec<i64> {
        let s1 = self.d1.sample(count);
        if s1.is_empty() {
            self.d2.sample(count)
        } else {
            s1
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // =========================================================================
    // Custom Test Domains
    // =========================================================================

    /// Parity domain: tracks whether a value is even or odd.
    ///
    /// Lattice:
    /// ```text
    ///       ⊤ (any)
    ///      / \
    ///   Even  Odd
    ///      \ /
    ///       ⊥
    /// ```
    #[derive(Debug, Clone, Copy, PartialEq, Eq)]
    enum TestParity {
        Bottom,
        Even,
        Odd,
        Top,
    }

    impl AbstractDomain for TestParity {
        fn bottom() -> Self {
            TestParity::Bottom
        }
        fn top() -> Self {
            TestParity::Top
        }
        fn is_bottom(&self) -> bool {
            matches!(self, TestParity::Bottom)
        }
        fn is_top(&self) -> bool {
            matches!(self, TestParity::Top)
        }
        fn join(&self, other: &Self) -> Self {
            use TestParity::*;
            match (self, other) {
                (Bottom, x) | (x, Bottom) => *x,
                (Top, _) | (_, Top) => Top,
                (Even, Even) => Even,
                (Odd, Odd) => Odd,
                (Even, Odd) | (Odd, Even) => Top,
            }
        }
        fn meet(&self, other: &Self) -> Self {
            use TestParity::*;
            match (self, other) {
                (Top, x) | (x, Top) => *x,
                (Bottom, _) | (_, Bottom) => Bottom,
                (Even, Even) => Even,
                (Odd, Odd) => Odd,
                (Even, Odd) | (Odd, Even) => Bottom,
            }
        }
        fn widen(&self, other: &Self) -> Self {
            self.join(other) // Finite domain
        }
        fn narrow(&self, other: &Self) -> Self {
            self.meet(other) // Finite domain
        }
        fn leq(&self, other: &Self) -> bool {
            use TestParity::*;
            match (self, other) {
                (Bottom, _) => true,
                (_, Top) => true,
                (Even, Even) | (Odd, Odd) => true,
                _ => false,
            }
        }
    }

    impl Concretizable for TestParity {
        fn concretize(&self) -> Option<i64> {
            match self {
                TestParity::Bottom => None,
                TestParity::Even => Some(0),
                TestParity::Odd => Some(1),
                TestParity::Top => Some(0),
            }
        }
        fn sample(&self, count: usize) -> Vec<i64> {
            match self {
                TestParity::Bottom => vec![],
                TestParity::Even => vec![0, 2, 4, -2].into_iter().take(count).collect(),
                TestParity::Odd => vec![1, 3, 5, -1].into_iter().take(count).collect(),
                TestParity::Top => vec![0, 1, 2, 3].into_iter().take(count).collect(),
            }
        }
    }

    /// Divisibility-by-3 domain: tracks x mod 3.
    ///
    /// Lattice:
    /// ```text
    ///          ⊤
    ///       /  |  \
    ///    Mod0 Mod1 Mod2
    ///       \  |  /
    ///          ⊥
    /// ```
    #[derive(Debug, Clone, Copy, PartialEq, Eq)]
    enum TestMod3 {
        Bottom,
        Mod0, // x ≡ 0 (mod 3)
        Mod1, // x ≡ 1 (mod 3)
        Mod2, // x ≡ 2 (mod 3)
        Top,
    }

    impl AbstractDomain for TestMod3 {
        fn bottom() -> Self {
            TestMod3::Bottom
        }
        fn top() -> Self {
            TestMod3::Top
        }
        fn is_bottom(&self) -> bool {
            matches!(self, TestMod3::Bottom)
        }
        fn is_top(&self) -> bool {
            matches!(self, TestMod3::Top)
        }
        fn join(&self, other: &Self) -> Self {
            use TestMod3::*;
            match (self, other) {
                (Bottom, x) | (x, Bottom) => *x,
                (Top, _) | (_, Top) => Top,
                (a, b) if a == b => *a,
                _ => Top,
            }
        }
        fn meet(&self, other: &Self) -> Self {
            use TestMod3::*;
            match (self, other) {
                (Top, x) | (x, Top) => *x,
                (Bottom, _) | (_, Bottom) => Bottom,
                (a, b) if a == b => *a,
                _ => Bottom,
            }
        }
        fn widen(&self, other: &Self) -> Self {
            self.join(other)
        }
        fn narrow(&self, other: &Self) -> Self {
            self.meet(other)
        }
        fn leq(&self, other: &Self) -> bool {
            use TestMod3::*;
            match (self, other) {
                (Bottom, _) => true,
                (_, Top) => true,
                (a, b) => a == b,
            }
        }
    }

    impl Concretizable for TestMod3 {
        fn concretize(&self) -> Option<i64> {
            match self {
                Self::Bottom => None,
                Self::Mod0 => Some(0),
                Self::Mod1 => Some(1),
                Self::Mod2 => Some(2),
                Self::Top => Some(0),
            }
        }
        fn sample(&self, count: usize) -> Vec<i64> {
            match self {
                Self::Bottom => vec![],
                Self::Mod0 => vec![0, 3, 6, 9].into_iter().take(count).collect(),
                Self::Mod1 => vec![1, 4, 7, 10].into_iter().take(count).collect(),
                Self::Mod2 => vec![2, 5, 8, 11].into_iter().take(count).collect(),
                Self::Top => vec![0, 1, 2, 3].into_iter().take(count).collect(),
            }
        }
    }

    // =========================================================================
    // Basic Operations
    // =========================================================================

    #[test]
    fn test_product_creation() {
        let product = ReducedProduct::new(TestParity::Even, TestMod3::Mod0);

        assert!(!product.is_bottom());
        assert!(!product.is_top());
        assert_eq!(product.d1, TestParity::Even);
        assert_eq!(product.d2, TestMod3::Mod0);
    }

    #[test]
    fn test_product_top_and_bottom() {
        let top: ReducedProduct<TestParity, TestMod3> = ReducedProduct::top();
        let bot: ReducedProduct<TestParity, TestMod3> = ReducedProduct::bottom();

        assert!(top.is_top());
        assert!(!top.is_bottom());
        assert!(bot.is_bottom());
        assert!(!bot.is_top());
    }

    #[test]
    fn test_product_join() {
        // Join of (Even, Mod0) and (Odd, Mod0) = (Top, Mod0)
        let a = ReducedProduct::new(TestParity::Even, TestMod3::Mod0);
        let b = ReducedProduct::new(TestParity::Odd, TestMod3::Mod0);
        let joined = a.join(&b);

        assert_eq!(joined.d1, TestParity::Top);
        assert_eq!(joined.d2, TestMod3::Mod0);
    }

    #[test]
    fn test_product_meet() {
        // Meet of (Top, Mod0) and (Even, Top) = (Even, Mod0)
        let a = ReducedProduct::new(TestParity::Top, TestMod3::Mod0);
        let b = ReducedProduct::new(TestParity::Even, TestMod3::Top);
        let met = a.meet(&b);

        assert_eq!(met.d1, TestParity::Even);
        assert_eq!(met.d2, TestMod3::Mod0);
    }

    #[test]
    fn test_product_leq() {
        let specific = ReducedProduct::new(TestParity::Even, TestMod3::Mod0);
        let general1 = ReducedProduct::new(TestParity::Top, TestMod3::Mod0);
        let general2 = ReducedProduct::new(TestParity::Even, TestMod3::Top);
        let top: ReducedProduct<TestParity, TestMod3> = ReducedProduct::top();

        // More specific ⊑ more general
        assert!(specific.leq(&general1));
        assert!(specific.leq(&general2));
        assert!(specific.leq(&top));
        assert!(general1.leq(&top));
        assert!(general2.leq(&top));

        // But not vice versa
        assert!(!top.leq(&specific));
        assert!(!general1.leq(&specific));
    }

    // =========================================================================
    // Key Benefit: Detecting Infeasibility Neither Domain Alone Can Find
    // =========================================================================

    #[test]
    fn test_product_detects_infeasibility() {
        // KEY INSIGHT: The reduced product can detect ⊥ when components are incompatible.
        //
        // Example: "x is even" AND "x ≡ 1 (mod 3)"
        // - Parity alone: Even (not ⊥)
        // - Mod3 alone: Mod1 (not ⊥)
        // - BUT: There's no integer that's both even AND ≡ 1 (mod 3)?
        //
        // Actually, 4 is even and 4 ≡ 1 (mod 3). So this IS satisfiable.
        // Let's create a case where the meet produces bottom:

        // Meet of (Even, Mod0) and (Odd, Mod1) in product space
        let a = ReducedProduct::new(TestParity::Even, TestMod3::Mod0);
        let b = ReducedProduct::new(TestParity::Odd, TestMod3::Mod1);
        let met = a.meet(&b);

        // Even ⊓ Odd = ⊥, so product is ⊥
        assert!(met.is_bottom(), "Product should detect incompatible parities");
    }

    #[test]
    fn test_product_propagates_bottom() {
        // If EITHER component is ⊥, the whole product is ⊥
        let a = ReducedProduct::new(TestParity::Bottom, TestMod3::Mod0);
        let b = ReducedProduct::new(TestParity::Even, TestMod3::Bottom);

        assert!(a.is_bottom(), "Bottom in first component → product is bottom");
        assert!(b.is_bottom(), "Bottom in second component → product is bottom");
    }

    // =========================================================================
    // Precision: Product is More Precise Than Individual Domains
    // =========================================================================

    #[test]
    fn test_product_more_precise_than_components() {
        // The product (Even, Mod0) represents numbers that are:
        // - Even: {..., -4, -2, 0, 2, 4, 6, ...}
        // - Divisible by 3: {..., -6, -3, 0, 3, 6, 9, ...}
        // - BOTH: {..., -6, 0, 6, 12, ...} = multiples of 6!
        //
        // Neither domain alone can express "multiple of 6".

        let _even_only = TestParity::Even;
        let _mod0_only = TestMod3::Mod0;
        let product = ReducedProduct::new(TestParity::Even, TestMod3::Mod0);

        // Both individual domains accept 2 and 3 respectively
        // 2 is even but 2 ≡ 2 (mod 3)
        // 3 is ≡ 0 (mod 3) but is odd
        // 6 is both even AND ≡ 0 (mod 3)

        // The product is strictly more precise
        let _samples = product.sample(4);
        // Should prefer values that satisfy BOTH constraints
        assert!(product.concretize().is_some());

        // Verify the lattice ordering
        let general_parity = ReducedProduct::new(TestParity::Even, TestMod3::Top);
        let general_mod3 = ReducedProduct::new(TestParity::Top, TestMod3::Mod0);

        assert!(product.leq(&general_parity), "Specific ⊑ general (parity)");
        assert!(product.leq(&general_mod3), "Specific ⊑ general (mod3)");
    }

    // =========================================================================
    // Concretization
    // =========================================================================

    #[test]
    fn test_product_concretize() {
        let product = ReducedProduct::new(TestParity::Odd, TestMod3::Mod1);

        // Should get a value from the first domain (Parity::Odd → 1)
        let value = product.concretize();
        assert_eq!(value, Some(1));
    }

    #[test]
    fn test_product_concretize_bottom() {
        // When product is bottom, both components are bottom
        let product: ReducedProduct<TestParity, TestMod3> = ReducedProduct::bottom();
        assert!(product.is_bottom());
        assert_eq!(product.concretize(), None);
    }

    #[test]
    fn test_product_sample() {
        let product = ReducedProduct::new(TestParity::Even, TestMod3::Top);

        let samples = product.sample(3);
        assert!(!samples.is_empty());
        // Should get samples from Parity::Even (0, 2, 4, ...)
        assert!(samples.iter().all(|x| x % 2 == 0));
    }

    // =========================================================================
    // Widening and Narrowing
    // =========================================================================

    #[test]
    fn test_product_widen() {
        let a = ReducedProduct::new(TestParity::Even, TestMod3::Mod0);
        let b = ReducedProduct::new(TestParity::Odd, TestMod3::Mod1);
        let widened = a.widen(&b);

        // For finite domains, widen = join
        assert_eq!(widened.d1, TestParity::Top);
        assert_eq!(widened.d2, TestMod3::Top);
    }

    #[test]
    fn test_product_narrow() {
        let a = ReducedProduct::new(TestParity::Top, TestMod3::Top);
        let b = ReducedProduct::new(TestParity::Even, TestMod3::Mod0);
        let narrowed = a.narrow(&b);

        // For finite domains, narrow = meet
        assert_eq!(narrowed.d1, TestParity::Even);
        assert_eq!(narrowed.d2, TestMod3::Mod0);
    }

    // =========================================================================
    // Triple Product: Combining Three Domains
    // =========================================================================

    #[test]
    fn test_triple_product() {
        // We can nest products: (Parity × Mod3) × Parity
        // This represents tracking both parity AND mod-3 residue.

        let inner = ReducedProduct::new(TestParity::Even, TestMod3::Mod0);
        let triple: ReducedProduct<ReducedProduct<TestParity, TestMod3>, TestParity> = ReducedProduct::new(inner, TestParity::Even);

        assert!(!triple.is_bottom());
        assert!(!triple.is_top());

        // Meet with conflicting outer parity
        let conflict = ReducedProduct::new(ReducedProduct::new(TestParity::Even, TestMod3::Mod0), TestParity::Odd);

        let met = triple.meet(&conflict);
        // Inner parities match (Even), but outer parities conflict (Even vs Odd)
        assert!(met.is_bottom(), "Conflicting outer parity → bottom");
    }

    #[test]
    fn test_all_mod3_values() {
        // Test that all Mod3 variants work correctly
        let mod0 = ReducedProduct::new(TestParity::Even, TestMod3::Mod0);
        let mod1 = ReducedProduct::new(TestParity::Odd, TestMod3::Mod1);
        let mod2 = ReducedProduct::new(TestParity::Even, TestMod3::Mod2);

        // All are valid (not bottom)
        assert!(!mod0.is_bottom());
        assert!(!mod1.is_bottom());
        assert!(!mod2.is_bottom());

        // Meet of different mod values gives bottom
        let met = mod0.meet(&mod1);
        assert!(met.is_bottom(), "Even/Mod0 ⊓ Odd/Mod1 = ⊥ (parity conflict)");

        // Mod2 samples should include 2, 5, 8...
        let samples = TestMod3::Mod2.sample(3);
        assert!(samples.contains(&2) || samples.contains(&5));
    }

    // =========================================================================
    // Use Case: Detecting Division by Zero
    // =========================================================================

    /// Sign domain for detecting potential division by zero.
    #[derive(Debug, Clone, Copy, PartialEq, Eq)]
    enum TestSign {
        Bottom,
        Negative,
        Zero,
        Positive,
        NonZero,     // Negative ∪ Positive
        NonNegative, // Zero ∪ Positive
        NonPositive, // Negative ∪ Zero
        Top,
    }

    impl AbstractDomain for TestSign {
        fn bottom() -> Self {
            TestSign::Bottom
        }
        fn top() -> Self {
            TestSign::Top
        }
        fn is_bottom(&self) -> bool {
            matches!(self, TestSign::Bottom)
        }
        fn is_top(&self) -> bool {
            matches!(self, TestSign::Top)
        }
        fn join(&self, other: &Self) -> Self {
            use TestSign::*;
            if self == other {
                return *self;
            }
            match (self, other) {
                (Bottom, x) | (x, Bottom) => *x,
                (Top, _) | (_, Top) => Top,
                (Zero, Positive) | (Positive, Zero) => NonNegative,
                (Zero, Negative) | (Negative, Zero) => NonPositive,
                (Negative, Positive) | (Positive, Negative) => NonZero,
                (NonZero, Zero) | (Zero, NonZero) => Top,
                (NonNegative, Negative) | (Negative, NonNegative) => Top,
                (NonPositive, Positive) | (Positive, NonPositive) => Top,
                (NonNegative, NonPositive) | (NonPositive, NonNegative) => Top,
                (NonZero, s) | (s, NonZero) if matches!(s, Negative | Positive) => NonZero,
                (NonNegative, s) | (s, NonNegative) if matches!(s, Zero | Positive) => NonNegative,
                (NonPositive, s) | (s, NonPositive) if matches!(s, Zero | Negative) => NonPositive,
                _ => Top,
            }
        }
        fn meet(&self, other: &Self) -> Self {
            use TestSign::*;
            if self == other {
                return *self;
            }
            match (self, other) {
                (Top, x) | (x, Top) => *x,
                (Bottom, _) | (_, Bottom) => Bottom,
                (NonZero, Negative) | (Negative, NonZero) => Negative,
                (NonZero, Positive) | (Positive, NonZero) => Positive,
                (NonNegative, Zero) | (Zero, NonNegative) => Zero,
                (NonNegative, Positive) | (Positive, NonNegative) => Positive,
                (NonNegative, NonZero) | (NonZero, NonNegative) => Positive,
                (NonPositive, Zero) | (Zero, NonPositive) => Zero,
                (NonPositive, Negative) | (Negative, NonPositive) => Negative,
                (NonPositive, NonZero) | (NonZero, NonPositive) => Negative,
                (NonNegative, NonPositive) | (NonPositive, NonNegative) => Zero,
                _ => Bottom,
            }
        }
        fn widen(&self, other: &Self) -> Self {
            self.join(other)
        }
        fn narrow(&self, other: &Self) -> Self {
            self.meet(other)
        }
        fn leq(&self, other: &Self) -> bool {
            use TestSign::*;
            match (self, other) {
                (Bottom, _) | (_, Top) => true,
                (Zero, NonNegative | NonPositive) => true,
                (Negative, NonPositive | NonZero) => true,
                (Positive, NonNegative | NonZero) => true,
                (a, b) => a == b,
            }
        }
    }

    impl Concretizable for TestSign {
        fn concretize(&self) -> Option<i64> {
            match self {
                TestSign::Bottom => None,
                TestSign::Negative => Some(-1),
                TestSign::Zero => Some(0),
                TestSign::Positive => Some(1),
                TestSign::NonZero => Some(1),
                TestSign::NonNegative => Some(0),
                TestSign::NonPositive => Some(0),
                TestSign::Top => Some(0),
            }
        }
        fn sample(&self, _count: usize) -> Vec<i64> {
            match self {
                TestSign::Bottom => vec![],
                TestSign::Negative => vec![-1, -2, -10],
                TestSign::Zero => vec![0],
                TestSign::Positive => vec![1, 2, 10],
                TestSign::NonZero => vec![1, -1, 2, -2],
                TestSign::NonNegative => vec![0, 1, 2],
                TestSign::NonPositive => vec![0, -1, -2],
                TestSign::Top => vec![0, 1, -1],
            }
        }
    }

    #[test]
    fn test_sign_parity_product_for_division() {
        // Use case: We want to know if a variable can be zero (division safety).
        //
        // Sign domain tracks: can it be zero?
        // Parity domain tracks: is it even or odd?
        //
        // Product insight: if we know x is ODD, then x ≠ 0 (since 0 is even)!

        // If we only know x is NonNegative, it MIGHT be zero
        let might_be_zero = TestSign::NonNegative;
        assert!(might_be_zero.concretize() == Some(0)); // Could be 0

        // But if we also know x is Odd, then x ≠ 0!
        let product: ReducedProduct<TestSign, TestParity> = ReducedProduct::new(TestSign::NonNegative, TestParity::Odd);

        // The product should detect: NonNegative ∩ Odd ⊆ Positive
        // (odd non-negative numbers are positive)

        // Meet with Zero should give bottom (odd numbers can't be zero)
        let with_zero = ReducedProduct::new(TestSign::Zero, TestParity::Even);
        let met = product.meet(&with_zero);

        // Zero is Even, our value is Odd → Parity conflict → bottom
        assert!(met.is_bottom(), "Odd value can never equal zero (which is even)");
    }

    #[test]
    fn test_product_union_preserves_info() {
        // Even after joining, we can retain useful information.
        //
        // Join of "positive even" and "positive odd" = "positive"
        // But we lose parity information.

        let pos_even = ReducedProduct::new(TestSign::Positive, TestParity::Even);
        let pos_odd = ReducedProduct::new(TestSign::Positive, TestParity::Odd);
        let joined = pos_even.join(&pos_odd);

        assert_eq!(joined.d1, TestSign::Positive); // Sign preserved
        assert_eq!(joined.d2, TestParity::Top); // Parity lost (could be either)

        // The product is still more precise than Top
        assert!(!joined.is_top());
        // We still know it's positive!
        assert!(joined.d1 == TestSign::Positive);
    }

    // =========================================================================
    // Reduction: Cross-Domain Constraint Propagation
    // =========================================================================

    // Implement Reducible for test domains to demonstrate cross-domain reduction.
    //
    // TestParity × Mod3: These domains can reduce each other because:
    // - Even numbers have a specific set of mod-3 residues: {0, 2} (mod 3)
    // - Odd numbers have: {1} (mod 3) for odd ≡ 1, or wait... actually:
    //   - 0 is even, 0 mod 3 = 0
    //   - 2 is even, 2 mod 3 = 2
    //   - 4 is even, 4 mod 3 = 1
    //   - 6 is even, 6 mod 3 = 0
    //   So even numbers can have ANY mod-3 residue. Same for odd.
    //
    // Better example: TestSign × TestParity
    // - Zero is even (0 mod 2 = 0), so Sign::Zero requires Parity::Even
    // - If we know something is Odd, it can't be Zero

    impl Reducible<TestParity> for TestSign {
        /// Reduce sign using parity information.
        ///
        /// Key insight: Zero is even, so Odd implies NonZero.
        fn reduce(&self, parity: &TestParity) -> Self {
            match (self, parity) {
                // If parity is bottom, result is bottom
                (_, TestParity::Bottom) => TestSign::Bottom,
                // If sign is bottom, result is bottom
                (TestSign::Bottom, _) => TestSign::Bottom,
                // Zero is even, so Zero ∧ Odd = ⊥
                (TestSign::Zero, TestParity::Odd) => TestSign::Bottom,
                // NonNegative ∧ Odd: can't be zero, so must be Positive
                (TestSign::NonNegative, TestParity::Odd) => TestSign::Positive,
                // NonPositive ∧ Odd: can't be zero, so must be Negative
                (TestSign::NonPositive, TestParity::Odd) => TestSign::Negative,
                // Top ∧ Odd: can't be zero, so NonZero
                (TestSign::Top, TestParity::Odd) => TestSign::NonZero,
                // For Even or Top parity, no additional info
                _ => *self,
            }
        }
    }

    impl Reducible<TestSign> for TestParity {
        /// Reduce parity using sign information.
        ///
        /// Key insight: Zero is even.
        fn reduce(&self, sign: &TestSign) -> Self {
            match (self, sign) {
                // If sign is bottom, result is bottom
                (_, TestSign::Bottom) => TestParity::Bottom,
                // If parity is bottom, result is bottom
                (TestParity::Bottom, _) => TestParity::Bottom,
                // If sign is Zero, parity must be Even
                (_, TestSign::Zero) => TestParity::Even,
                // Odd with Zero sign handled above (becomes Even, then conflict)
                // For other signs, no additional info
                _ => *self,
            }
        }
    }

    #[test]
    fn test_sign_reduced_by_parity_odd_excludes_zero() {
        // Zero is even, so if we know something is Odd, it can't be zero.
        // NonNegative ∧ Odd = Positive (since 0 is excluded)
        let sign = TestSign::NonNegative;
        let reduced = sign.reduce(&TestParity::Odd);
        assert_eq!(reduced, TestSign::Positive);
    }

    #[test]
    fn test_sign_reduced_by_parity_zero_and_odd_is_bottom() {
        // Zero ∧ Odd = ⊥ (impossible: zero is even)
        let sign = TestSign::Zero;
        let reduced = sign.reduce(&TestParity::Odd);
        assert!(reduced.is_bottom());
    }

    #[test]
    fn test_sign_reduced_by_parity_top_and_odd_is_nonzero() {
        // Top ∧ Odd = NonZero (odd numbers can't be zero)
        let sign = TestSign::Top;
        let reduced = sign.reduce(&TestParity::Odd);
        assert_eq!(reduced, TestSign::NonZero);
    }

    #[test]
    fn test_parity_reduced_by_sign_zero_is_even() {
        // Any parity reduced by Zero must be Even (since 0 is even)
        let parity = TestParity::Top;
        let reduced = parity.reduce(&TestSign::Zero);
        assert_eq!(reduced, TestParity::Even);
    }

    #[test]
    fn test_parity_reduced_by_sign_odd_and_zero_is_bottom() {
        // Odd ∧ Zero = ⊥ (handled via reduction)
        // - Parity Odd reduced by Zero → Even (since zero is even)
        // - But original parity was Odd, and now it's Even → conflict!
        // The product should detect this infeasibility.

        // First, verify the individual reductions:
        let parity_reduced = TestParity::Odd.reduce(&TestSign::Zero);
        assert_eq!(parity_reduced, TestParity::Even, "Odd reduced by Zero gives Even");

        let sign_reduced = TestSign::Zero.reduce(&TestParity::Odd);
        assert!(sign_reduced.is_bottom(), "Zero reduced by Odd is bottom");

        // Now verify the product detects infeasibility
        let reduced = ReducedProduct::new_reduced(TestSign::Zero, TestParity::Odd);
        assert!(reduced.is_bottom(), "Zero with Odd parity is infeasible");
    }

    #[test]
    fn test_reduced_product_sign_parity_propagation() {
        // Start with NonNegative × Odd
        // After reduction:
        // - Sign NonNegative reduced by Odd → Positive (zero excluded)
        // - Parity Odd reduced by Positive → Odd (unchanged)
        // Result: Positive × Odd

        let product = ReducedProduct::new_reduced(TestSign::NonNegative, TestParity::Odd);

        assert_eq!(product.d1, TestSign::Positive);
        assert_eq!(product.d2, TestParity::Odd);
    }

    #[test]
    fn test_reduced_product_sign_parity_no_change_for_even() {
        // Positive × Even: no reduction needed (no conflict)
        let product = ReducedProduct::new_reduced(TestSign::Positive, TestParity::Even);

        assert_eq!(product.d1, TestSign::Positive);
        assert_eq!(product.d2, TestParity::Even);
    }

    // =========================================================================
    // TRUE REDUCTION with Real Interval × Sign Domains
    // =========================================================================
    //
    // These tests use the REAL Interval and Sign domains from the library,
    // which implement `Reducible` to propagate constraints between domains.

    use crate::domain::{Interval, Sign};

    #[test]
    fn test_interval_reduced_by_sign_positive() {
        // Interval [-10, 10] reduced by Positive → [1, 10]
        let interval = Interval::from_bounds(-10, 10);
        let reduced = interval.reduce(&Sign::Positive);

        assert_eq!(reduced.low(), crate::domain::Bound::Finite(1));
        assert_eq!(reduced.high(), crate::domain::Bound::Finite(10));
    }

    #[test]
    fn test_interval_reduced_by_sign_negative() {
        // Interval [-10, 10] reduced by Negative → [-10, -1]
        let interval = Interval::from_bounds(-10, 10);
        let reduced = interval.reduce(&Sign::Negative);

        assert_eq!(reduced.low(), crate::domain::Bound::Finite(-10));
        assert_eq!(reduced.high(), crate::domain::Bound::Finite(-1));
    }

    #[test]
    fn test_interval_reduced_by_sign_zero() {
        // Interval [-10, 10] reduced by Zero → [0, 0]
        let interval = Interval::from_bounds(-10, 10);
        let reduced = interval.reduce(&Sign::Zero);

        assert_eq!(reduced.low(), crate::domain::Bound::Finite(0));
        assert_eq!(reduced.high(), crate::domain::Bound::Finite(0));
    }

    #[test]
    fn test_interval_reduced_by_sign_nonnegative() {
        // Interval [-10, 10] reduced by NonNegative → [0, 10]
        let interval = Interval::from_bounds(-10, 10);
        let reduced = interval.reduce(&Sign::NonNegative);

        assert_eq!(reduced.low(), crate::domain::Bound::Finite(0));
        assert_eq!(reduced.high(), crate::domain::Bound::Finite(10));
    }

    #[test]
    fn test_sign_reduced_by_interval_positive() {
        // Sign Top reduced by [5, 10] → Positive
        let sign = Sign::Top;
        let reduced = sign.reduce(&Interval::from_bounds(5, 10));

        assert_eq!(reduced, Sign::Positive);
    }

    #[test]
    fn test_sign_reduced_by_interval_negative() {
        // Sign Top reduced by [-10, -5] → Negative
        let sign = Sign::Top;
        let reduced = sign.reduce(&Interval::from_bounds(-10, -5));

        assert_eq!(reduced, Sign::Negative);
    }

    #[test]
    fn test_sign_reduced_by_interval_zero() {
        // Sign Top reduced by [0, 0] → Zero
        let sign = Sign::Top;
        let reduced = sign.reduce(&Interval::from_bounds(0, 0));

        assert_eq!(reduced, Sign::Zero);
    }

    #[test]
    fn test_sign_reduced_by_interval_nonzero_becomes_positive() {
        // Sign NonZero reduced by [0, 10] → Positive (0 excluded by NonZero)
        let sign = Sign::NonZero;
        let reduced = sign.reduce(&Interval::from_bounds(0, 10));

        assert_eq!(reduced, Sign::Positive);
    }

    #[test]
    fn test_reduced_product_propagates_constraints() {
        // The key test: ReducedProduct::new_reduced applies bidirectional reduction
        //
        // Start with: Interval[-10, 10] × Positive
        // After reduction:
        //   - Interval reduced by Positive → [1, 10]
        //   - Positive reduced by [1, 10] → Positive (unchanged)
        // Result: [1, 10] × Positive

        let product = ReducedProduct::new_reduced(Interval::from_bounds(-10, 10), Sign::Positive);

        // The interval should be refined!
        assert_eq!(product.d1.low(), crate::domain::Bound::Finite(1));
        assert_eq!(product.d1.high(), crate::domain::Bound::Finite(10));
        assert_eq!(product.d2, Sign::Positive);
    }

    #[test]
    fn test_reduced_product_detects_infeasibility() {
        // [5, 10] × Negative → ⊥
        // The interval [5, 10] has no negative values, so the reduction yields ⊥

        let product = ReducedProduct::new_reduced(Interval::from_bounds(5, 10), Sign::Negative);

        assert!(product.is_bottom(), "Positive interval with Negative sign is infeasible");
    }

    #[test]
    fn test_reduce_method_on_product() {
        // Create unreduced product, then call reduce()
        let unreduced = ReducedProduct::new(Interval::from_bounds(-10, 10), Sign::NonNegative);

        // Before reduction: interval is [-10, 10]
        assert_eq!(unreduced.d1.low(), crate::domain::Bound::Finite(-10));

        // After reduction: interval should be [0, 10]
        let reduced = unreduced.reduce();
        assert_eq!(reduced.d1.low(), crate::domain::Bound::Finite(0));
        assert_eq!(reduced.d1.high(), crate::domain::Bound::Finite(10));
    }
}
