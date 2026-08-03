// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License in the LICENSE-APACHE file or at:
//     https://www.apache.org/licenses/LICENSE-2.0

//! Type conversion, success expected
//!
//! ## Converting values
//!
//! This library exists to make fallible numeric type conversions easy, without
//! resorting to the `as` keyword.
//!
//! -   Use [`Cast`] and [`Conv`] instead of [`Into`] and [`From`] for exact
//!     conversions
//! -   Use [`CastApprox`] and [`ConvApprox`] for approximate conversions
//!     (rounding mode is implementation-defined just like `as`)
//! -   Use [`ConvTo`] and [`CastTo`] with an explicit rounding mode
//!     ([`Trunc`], [`Nearest`], [`Floor`], [`Ceil`]) for conversions with a
//!     specified rounding mode
//!
//! ### Error handling
//!
//! All trait methods have two variants:
//!
//! -   A `try_` variant (e.g. `try_cast`) which returns a `Result` and fails if
//!     the requested conversion is not possible.
//! -   A "plain" variant (e.g. `cast`) which returns the same result on success
//!     but may return a different result on error (see below).
//!
//! In debug builds, methods not returning `Result` must panic on failure. As
//! with the overflow checks on Rust's standard integer arithmetic, this is
//! considered a tool for finding logic errors. In release builds, these methods
//! are permitted to return a different (implementation-defined) result, usually
//! matching the behaviour of [`as` numeric casts].
//!
//! If the `always_assert` feature flag is set, assertions will be turned on in
//! all builds (i.e. "plain" variants will panic on failure). Some additional
//! feature flags are available for finer-grained control (see `Cargo.toml`).
//!
//! ### Example
//!
//! ```
//! use easy_cast::traits::*;
//! use easy_cast::{ConvTo, Nearest};
//!
//! fn nth_root<X: CastApprox<f64>>(x: X, n: u32) {
//!     let x = x.cast_approx();    // Into-like approximate conversion
//!     if x < 0.0 && n % 2 == 0 {
//!         println!("Imaginary values not supported!");
//!         return;
//!     }
//!
//!     let power = -i32::conv(n);  // From-like exact conversion
//!     let root = x.powi(power);
//!
//!     println!("The {n}-th root of {x} is {root}");
//!
//!     // TryFrom-like approximate (nearest) conversion
//!     if let Ok(nearest) = isize::try_conv_to(Nearest, root) {
//!         println!("Nearest integer: {nearest}");
//!     }
//! }
//! ```
//!
//! ## Implementing traits
//!
//! It is recommended to implement conversions which cannot be inexact using
//! [`ConvExact`] and other conversions using [`ConvTo`]. The latter trait may
//! be implemented for multiple [`Rounding`] modes.
//!
//! [`TryFrom`]: core::convert::TryFrom
//! [`TryInto`]: core::convert::TryInto
//! [`as` numeric casts]: https://doc.rust-lang.org/reference/expressions/operator-expr.html#r-expr.as.numeric

#![deny(missing_docs)]
#![cfg_attr(not(feature = "std"), no_std)]

mod impl_basic;
mod impl_float;
mod impl_int;
mod impl_num;
mod impl_ops;
mod impl_range;
mod rounding;

pub mod traits;

use core::convert::Infallible;

#[doc(inline)]
pub use rounding::*;

#[doc(inline)]
pub use traits::*;

/// Source value lies outside of target type's range
///
/// More precisely, all values of the target type's domain are either
/// incomparable to the source value or are closer to another value within
/// the target type's domain than to the source value.
#[derive(Clone, Copy, Debug, Default, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct RangeError;

impl From<Infallible> for RangeError {
    #[inline]
    fn from(error: Infallible) -> Self {
        match error {}
    }
}

impl core::fmt::Display for RangeError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "source value not in target range")
    }
}

impl core::error::Error for RangeError {}

/// Error types for conversions
#[derive(Clone, Copy, Debug, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub enum Error {
    /// Source value lies outside of target type's range
    ///
    /// More precisely, all values of the target type's domain are either
    /// incomparable to the source value or are closer to another value within
    /// the target type's domain than to the source value.
    Range,
    /// Loss of precision and/or outside of target type's range
    Inexact,
}

impl From<Infallible> for Error {
    #[inline]
    fn from(error: Infallible) -> Self {
        match error {}
    }
}

impl From<RangeError> for Error {
    #[inline]
    fn from(_: RangeError) -> Self {
        Self::Range
    }
}

impl core::fmt::Display for Error {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Error::Range => write!(f, "source value not in target range"),
            Error::Inexact => write!(f, "loss of precision"),
        }
    }
}

impl core::error::Error for Error {}
