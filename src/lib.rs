// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License in the LICENSE-APACHE file or at:
//     https://www.apache.org/licenses/LICENSE-2.0

//! # Converting values
//!
//! This library exists to make numeric type conversions easy and generic
//! without resorting to the `as` keyword.
//!
//! -   Use [`Cast`] and [`Conv`] instead of [`Into`] and [`From`] for exact
//!     conversions
//! -   Use [`CastApprox`] and [`ConvApprox`] for approximate conversions
//!     (rounding mode is implementation-defined just like `as`)
//! -   Use [`CastTo`] and [`ConvTo`] for conversions with a specific rounding
//!     mode (see [§ Rounding modes](#rounding-modes)).
//!
//! If this sounds like a lot of traits, consider the above are all essentially
//! syntactic sugar for [`ConvTo`] (see
//! [§ Implementing traits](#implementing-traits)).
//!
//! ### Quick example
//!
//! ```
//! use easy_cast::{Cast, Conv, CastApprox, CastTo, Nearest};
//! let _: i32 = 15_usize.cast();           // exact conversion
//! let _ = usize::conv(20_u32);            // exact conversion
//! let _: f32 = u32::MAX.cast_approx();    // approximates to 2^32
//! let _: i32 = 11.9_f32.cast_to(Nearest); // rounds to 12
//! ```
//!
//! ## Rounding modes
//!
//! The [`Rounding`] trait (used with [`CastTo`] and [`ConvTo`]) supports
//! genericity over rounding modes:
//!
//! -   [`Exact`] specifies that no rounding is allowed (loss of precision is an
//!     error)
//! -   [`Approx`] specifies that rounding is allowed. The rounding mode used is
//!     a property of the implementation, but usually aligns with
//!     [`as` numeric casts].
//! -   [`Trunc`], [`Floor`], [`Ceil`] and [`Nearest`] allow more precise
//!     control over rounding
//!
//! All rounding modes require that the result is close to the input value. For
//! a more precise definition, see
//! [`§ Limits of approximation`](Approx#limits-of-approximation).
//!
//! ## Error handling
//!
//! Unlike [`From`] or [`TryFrom`], this library's traits are implemented
//! regardless of fallibility. All conversion traits have an associated `Error`
//! type which is expected to be one of:
//!
//! -   [`std::convert::Infallible`] for infallible conversions
//! -   [`RangeError`] for conversions which may fail due to domain errors
//! -   [`Error`] for conversions which may fail due to domain or
//!     loss-of-precision errors.
//!
//! Further, all traits have two methods:
//!
//! -   A `try_` method (e.g. [`Cast::try_cast`]) which returns a [`Result`]
//! -   A "derived" method (e.g. [`Cast::cast`]) with
//!     [§ Fallback behaviour](#fallback-behaviour)
//!
//! ### Fallback behaviour
//!
//! In debug builds, the "derived" method must panic on failure. This is also
//! the case if the `always_assert` feature flag is enabled (for this library's
//! implementations).
//!
//! Otherwise (in release builds without extra assertions enabled), more
//! flexible behaviour of the "derived" methods is allowed. The implementations
//! provided by `easy-cast` mostly reduce to [`as` numeric casts] (with extra
//! rounding where required).
//!
//! ## Implementing traits
//!
//! Implement conversions which cannot lose precision using [`ConvExact`].
//! Implement all other conversions using [`ConvTo`] for one or several
//! [`Rounding`] modes.
//!
//! [`TryFrom`]: core::convert::TryFrom
//! [`TryInto`]: core::convert::TryInto
//! [`as` numeric casts]: https://doc.rust-lang.org/reference/expressions/operator-expr.html#r-expr.as.numeric

#![deny(missing_docs)]
#![cfg_attr(not(feature = "std"), no_std)]
#![cfg_attr(docsrs, feature(doc_cfg))]

mod impl_basic;
mod impl_float;
mod impl_int;
mod impl_num;
mod impl_ops;
mod impl_range;
mod rounding;

pub mod traits;

#[doc(inline)]
pub use rounding::*;
#[doc(inline)]
pub use traits::*;

use core::convert::Infallible;

/// Source value lies outside of target type's range
///
/// This error indicates that the input value is outside the range (domain) of
/// the target type. This error type is used for both conversions where
/// loss-of-precision is impossible and those where rounding is intended.
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
    /// This error indicates that the input value is outside the range (domain)
    /// of the target type.
    /// More precisely, all values of the target type's domain are either
    /// incomparable to the source value or are closer to another value within
    /// the target type's domain than to the source value.
    ///
    /// As typical example, attempting to convert `-1_i8` to `u8` results in a
    /// `Range` error. A special case is [`f32::NAN`] which, being (literally)
    /// "Not a Number" is outside the domain of the target type and thus a
    /// `Range` error (even where the target type has its own `NAN` value).
    Range,
    /// Loss of precision
    ///
    /// This error indicates that, though the input value is inside the range
    /// (domain) of the target type, conversion without loss of precision is
    /// impossible.
    ///
    /// For example, attempting to convert `2.1_f32` to `i32` without rounding
    /// results in an `Inexact` error.
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
