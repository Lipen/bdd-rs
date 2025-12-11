//! Classical abstract domains for comparison with SDD-based domain
//!
//! Implementations:
//! - Interval domain: tracks [min, max] per variable
//! - Bitset domain: tracks exact set of possible values per variable

pub mod bitset_domain;
pub mod interval_domain;

pub use bitset_domain::BitsetDomain;
pub use interval_domain::IntervalDomain;
