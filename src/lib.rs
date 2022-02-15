// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License in the LICENSE-APACHE file or at:
//     https://www.apache.org/licenses/LICENSE-2.0

//! Type conversion, success expected
//!
//! This library exists to make fallible numeric type conversions easy, without
//! resorting to the `as` keyword.
//!
//! -   [`Conv`] is like [`From`], but supports fallible conversions
//! -   [`Cast`] is to [`Conv`] what [`Into`] is to [`From`]
//! -   [`ConvApprox`] and [`CastApprox`] support fallible, approximate conversion
//! -   [`ConvFloat`] and [`CastFloat`] are similar, providing precise control over rounding
//!
//! If you are wondering "why not just use `as`", there are a few reasons:
//!
//! -   integer conversions may silently truncate or sign-extend which does not
//!     preserve value
//! -   prior to Rust 1.45.0 float-to-int conversions were not fully defined;
//!     since this version they use saturating conversion (NaN converts to 0)
//! -   you want some assurance (at least in debug builds) that the conversion
//!     will preserve values correctly
//!
//! Why might you *not* want to use this library?
//!
//! -   You want saturating / truncating / other non-value-preserving conversion
//! -   You want to convert non-numeric types ([`From`] supports a lot more
//!     conversions than [`Conv`] does)!
//! -   You want a thoroughly tested library (we're not quite there yet)
//!
//! ## Error handling
//!
//! All traits support two methods:
//!
//! -   `try_*` methods return a `Result` and always fail if the correct
//!     conversion is not possible
//! -   other methods may panic or return incorrect results
//!
//! In debug builds, methods not returning `Result` must panic on failure. As
//! with the overflow checks on Rust's standard integer arithmetic, this is
//! considered a tool for finding logic errors. In release builds, these methods
//! are permitted to return defined but incorrect results similar to the `as`
//! keyword.
//!
//! If the `always_assert` feature flag is set, assertions will be turned on in
//! all builds. Some additional feature flags are available for finer-grained
//! control (see `Cargo.toml`).
//!
//! ## no_std support
//!
//! When the crate's default features are disabled (and `std` is not enabled)
//! then the library supports `no_std`. In this case, [`ConvFloat`] and
//! [`CastFloat`] are only available if the `libm` optional dependency is
//! enabled.
//!
//! [`TryFrom`]: core::convert::TryFrom
//! [`TryInto`]: core::convert::TryInto

#![deny(missing_docs)]
#![cfg_attr(not(feature = "std"), no_std)]
#![cfg_attr(doc_cfg, feature(doc_cfg))]

mod impl_basic;
mod impl_float;
mod impl_int;

pub mod traits;

#[doc(inline)]
pub use traits::*;

/// Error types for conversions
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Error {
    /// Source value lies outside of target type's range
    Range,
    /// Loss of precision and/or outside of target type's range
    Inexact,
}

impl core::fmt::Display for Error {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Error::Range => write!(f, "source value not in target range"),
            Error::Inexact => write!(f, "loss of precision or range error"),
        }
    }
}

#[cfg(feature = "std")]
impl std::error::Error for Error {}

/// Result enum with bound [`Error`] type
pub type Result<T> = core::result::Result<T, Error>;
