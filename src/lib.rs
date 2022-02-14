// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License in the LICENSE-APACHE file or at:
//     https://www.apache.org/licenses/LICENSE-2.0

//! Type conversion, success expected
//!
//! This library is written to make numeric type conversions easy. Such
//! conversions usually fall into one of the following cases:
//!
//! -   the conversion must preserve values exactly (use [`From`] or [`Into`]
//!     or [`Conv`] or [`Cast`])
//! -   the conversion is expected to preserve values exactly, though this is
//!     not ensured by the types in question (use [`Conv`] or [`Cast`])
//! -   the conversion could fail and must be checked at run-time (use
//!     [`TryFrom`] or [`TryInto`] or [`Conv::try_conv`] or [`Cast::try_cast`])
//! -   the conversion is from floating point values to integers and should
//!     round to the "nearest" integer (use [`ConvFloat`] or [`CastFloat`])
//! -   the conversion is from `f32` to `f64` or vice-versa; in this case use of
//!     `as f32` / `as f64` is likely acceptable since `f32` has special
//!     representations for non-finite values and conversion to `f64` is exact
//! -   truncating conversion (modular arithmetic) is desired; in this case `as`
//!     probably does exactly what you want
//! -   saturating conversion is desired (less common; not supported here)
//!
//! If you are wondering "why not just use `as`", there are a few reasons:
//!
//! -   integer conversions may silently truncate
//! -   integer conversions to/from signed types silently reinterpret
//! -   prior to Rust 1.45.0 float-to-int conversions were not fully defined;
//!     since this version they use saturating conversion (NaN converts to 0)
//! -   you want some assurance (at least in debug builds) that the conversion
//!     will preserve values correctly without having to proof-read code
//!
//! When should you *not* use this library?
//!
//! -   Only numeric conversions are supported
//! -   Conversions from floats do not provide fine control of rounding modes
//! -   This library has not been thoroughly tested correctness
//!
//! ## Assertions
//!
//! All type conversions which are potentially fallible assert on failure in
//! debug builds. In release builds assertions may be omitted, thus making
//! incorrect conversions possible.
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

use core::mem::size_of;

/// Error types for conversions
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Error {
    /// Source value lies outside of target type's range
    Range,
    /// Loss of precision and/or outside of target type's range
    Inexact,
}

#[cfg(feature = "std")]
impl std::fmt::Display for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Error::Range => write!(f, "source value not in target range"),
            Error::Inexact => write!(f, "loss of precision or range error"),
        }
    }
}

#[cfg(feature = "std")]
impl std::error::Error for Error {}

/// Like [`From`], but supports fallible conversions
///
/// This trait is intented to be an extension over [`From`], also supporting
/// fallible conversions of numeric types.
/// Since Rust does not yet have stable support for handling conflicting
/// implementations (specialization or otherwise), only conversions between
/// the most important numeric types are supported for now.
///
/// The sister-trait [`Cast`] may be easier to use (as with [`Into`]).
pub trait Conv<T>: Sized {
    /// Try converting from `T` to `Self`
    ///
    /// This method must fail on inexact conversions.
    fn try_conv(v: T) -> Result<Self, Error>;

    /// Convert from `T` to `Self`
    ///
    /// This method must return the same result as [`Self::try_conv`] where that
    /// method succeeds, but differs in the handling of errors:
    ///
    /// -   In debug builds the method panics on error
    /// -   Otherwise, the method may panic or may return a different value,
    ///     but like with the `as` keyword all results must be well-defined and
    ///     *safe*.
    ///
    /// Default implementations use [`Self::try_conv`] and panic on error.
    /// Implementations provided by this library will panic in debug builds
    /// or if the `always_assert` feature flag is used, and otherwise will
    /// behave identically to the `as` keyword.
    ///
    /// This mirrors the behaviour of Rust's overflow checks on integer
    /// arithmetic in that it is a tool for diagnosing logic errors where
    /// success is expected.
    fn conv(v: T) -> Self {
        Self::try_conv(v).unwrap_or_else(|e| panic!("Conv::conv(_) failed: {}", e))
    }
}

/// Like [`Into`], but for [`Conv`]
///
/// This trait is automatically implemented for every implementation of
/// [`Conv`].
pub trait Cast<T> {
    /// Try converting from `Self` to `T`
    ///
    /// Use this method to explicitly handle errors.
    fn try_cast(self) -> Result<T, Error>;

    /// Cast from `Self` to `T`
    ///
    /// Use this method *only* where success is expected: implementations are
    /// permitted to panic or silently return a different (safe, defined) value
    /// on error.
    ///
    /// In debug builds, implementations must panic.
    ///
    /// Implementations by this library will panic in debug builds or if the
    /// `always_assert` feature flag is used, otherwise conversions have the
    /// same behaviour as the `as` keyword.
    fn cast(self) -> T;
}

impl<S, T: Conv<S>> Cast<T> for S {
    #[inline]
    fn cast(self) -> T {
        T::conv(self)
    }
    #[inline]
    fn try_cast(self) -> Result<T, Error> {
        T::try_conv(self)
    }
}

/// Like [`From`], but for approximate numerical conversions
///
/// This trait is implemented for all conversions supported by [`ConvFloat`].
/// Prefer to use [`ConvFloat`] or [`CastFloat`] where precise control over
/// rounding is required.
///
/// The sister-trait [`CastApprox`] may be easier to use (as with [`Into`]).
pub trait ConvApprox<T>: Sized {
    /// Try converting from `T` to `Self`, allowing approximation of value
    ///
    /// This method should allow approximate conversion, but fail on input not
    /// (approximately) in the target's range.
    fn try_conv_approx(x: T) -> Result<Self, Error>;

    /// Converting from `T` to `Self`, allowing approximation of value
    ///
    /// This method must return the same result as [`Self::try_conv_approx`]
    /// where that method succeeds, but differs in the handling of errors:
    ///
    /// -   In debug builds the method panics on error
    /// -   Otherwise, the method may panic or may return a different value,
    ///     but like with the `as` keyword all results must be well-defined and
    ///     *safe*.
    ///
    /// Default implementations use [`Self::try_conv_approx`] and panic on error.
    /// Implementations provided by this library will panic in debug builds
    /// or if the `always_assert` feature flag is used, and otherwise will
    /// behave identically to the `as` keyword.
    ///
    /// This mirrors the behaviour of Rust's overflow checks on integer
    /// arithmetic in that it is a tool for diagnosing logic errors where
    /// success is expected.
    #[inline]
    fn conv_approx(x: T) -> Self {
        Self::try_conv_approx(x)
            .unwrap_or_else(|e| panic!("ConvApprox::conv_approx(_) failed: {}", e))
    }
}

// TODO(specialization): implement also where T: Conv<S>
impl<S, T: ConvFloat<S>> ConvApprox<S> for T {
    #[inline]
    fn try_conv_approx(x: S) -> Result<Self, Error> {
        T::try_conv_trunc(x)
    }
    #[inline]
    fn conv_approx(x: S) -> Self {
        T::conv_trunc(x)
    }
}

/// Like [`Into`], but for [`ConvApprox`]
///
/// This trait is automatically implemented for every implementation of
/// [`ConvApprox`].
pub trait CastApprox<T> {
    /// Try approximate conversion from `Self` to `T`
    ///
    /// Use this method to explicitly handle errors.
    fn try_cast_approx(self) -> Result<T, Error>;

    /// Cast approximately from `Self` to `T`
    ///
    /// Use this method *only* where success is expected: implementations are
    /// permitted to panic or silently return a different (safe, defined) value
    /// on error.
    ///
    /// In debug builds, implementations must panic.
    ///
    /// Implementations by this library will panic in debug builds or if the
    /// `always_assert` feature flag is used, otherwise conversions have the
    /// same behaviour as the `as` keyword.
    fn cast_approx(self) -> T;
}

impl<S, T: ConvApprox<S>> CastApprox<T> for S {
    #[inline]
    fn try_cast_approx(self) -> Result<T, Error> {
        T::try_conv_approx(self)
    }
    #[inline]
    fn cast_approx(self) -> T {
        T::conv_approx(self)
    }
}

/// Nearest / floor / ceiling conversions from floating point types
///
/// This trait is explicitly for conversions from floating-point values to
/// integers, supporting four rounding modes.
///
/// As with [`Conv`], the `try_conv_*` methods must be implemented and must fail
/// if conversion to the expected value is not possible. If the source is non-
/// finite (`inf` or `NaN`), then `Error::Range` should be returned.
///
/// The `conv_*` methods each have a default implementation over the `try_..`
/// variant which panics on failure. Implementations handle errors as follows:
///
/// -   In debug builds, the methods must panic
/// -   Otherwise, the method may panic or may return a different value; all
///     results must be well-defined and *safe*.
/// -   Implementations provided by this library will also panic if the
///     `always_assert` or `assert_float` feature flag is used.
///
/// The sister-trait [`CastFloat`] may be easier to use (as with [`Into`]).
#[cfg(any(feature = "std", feature = "libm"))]
#[cfg_attr(doc_cfg, doc(cfg(any(feature = "std", feature = "libm"))))]
pub trait ConvFloat<T>: Sized {
    /// Try converting to integer with truncation
    ///
    /// Rounds towards zero (same as `as`).
    fn try_conv_trunc(x: T) -> Result<Self, Error>;
    /// Try converting to the nearest integer
    ///
    /// Half-way cases are rounded away from `0`.
    fn try_conv_nearest(x: T) -> Result<Self, Error>;
    /// Try converting the floor to an integer
    ///
    /// Returns the largest integer less than or equal to `x`.
    fn try_conv_floor(x: T) -> Result<Self, Error>;
    /// Try convert the ceiling to an integer
    ///
    /// Returns the smallest integer greater than or equal to `x`.
    fn try_conv_ceil(x: T) -> Result<Self, Error>;

    /// Convert to integer with truncatation
    ///
    /// Rounds towards zero (same as `as`).
    fn conv_trunc(x: T) -> Self {
        Self::try_conv_trunc(x).unwrap_or_else(|e| panic!("ConvFloat::conv_trunc(_) failed: {}", e))
    }
    /// Convert to the nearest integer
    ///
    /// Half-way cases are rounded away from `0`.
    fn conv_nearest(x: T) -> Self {
        Self::try_conv_nearest(x)
            .unwrap_or_else(|e| panic!("ConvFloat::conv_nearest(_) failed: {}", e))
    }
    /// Convert the floor to an integer
    ///
    /// Returns the largest integer less than or equal to `x`.
    fn conv_floor(x: T) -> Self {
        Self::try_conv_floor(x).unwrap_or_else(|e| panic!("ConvFloat::conv_floor(_) failed: {}", e))
    }
    /// Convert the ceiling to an integer
    ///
    /// Returns the smallest integer greater than or equal to `x`.
    fn conv_ceil(x: T) -> Self {
        Self::try_conv_ceil(x).unwrap_or_else(|e| panic!("ConvFloat::conv_ceil(_) failed: {}", e))
    }
}

/// Like [`Into`], but for [`ConvFloat`]
///
/// Use:
///
/// -   `try_cast_*` methods to explicitly handle errors
/// -   `cast_*` methods *only* where success is expected. Implementations are
///     permitted to panic or silently return a different (safe, defined) value
///     on error.
///
///     In debug builds, implementations must panic.
///
///     Implementations by this library will panic in debug builds or if the
///     `always_assert` or `assert_float` feature flag is used, otherwise
///     conversions have similar behaviour to the `as` keyword.
///
/// This trait is automatically implemented for every implementation of
/// [`ConvFloat`].
#[cfg(any(feature = "std", feature = "libm"))]
#[cfg_attr(doc_cfg, doc(cfg(any(feature = "std", feature = "libm"))))]
pub trait CastFloat<T> {
    /// Cast to integer, truncating
    ///
    /// Rounds towards zero (same as `as`).
    fn cast_trunc(self) -> T;
    /// Cast to the nearest integer
    ///
    /// Half-way cases are rounded away from `0`.
    fn cast_nearest(self) -> T;
    /// Cast the floor to an integer
    ///
    /// Returns the largest integer less than or equal to `self`.
    fn cast_floor(self) -> T;
    /// Cast the ceiling to an integer
    ///
    /// Returns the smallest integer greater than or equal to `self`.
    fn cast_ceil(self) -> T;

    /// Try converting to integer with truncation
    ///
    /// Rounds towards zero (same as `as`).
    fn try_cast_trunc(self) -> Result<T, Error>;
    /// Try converting to the nearest integer
    ///
    /// Half-way cases are rounded away from `0`.
    fn try_cast_nearest(self) -> Result<T, Error>;
    /// Try converting the floor to an integer
    ///
    /// Returns the largest integer less than or equal to `x`.
    fn try_cast_floor(self) -> Result<T, Error>;
    /// Try convert the ceiling to an integer
    ///
    /// Returns the smallest integer greater than or equal to `x`.
    fn try_cast_ceil(self) -> Result<T, Error>;
}

#[cfg(any(feature = "std", feature = "libm"))]
impl<S, T: ConvFloat<S>> CastFloat<T> for S {
    #[inline]
    fn cast_trunc(self) -> T {
        T::conv_trunc(self)
    }
    #[inline]
    fn cast_nearest(self) -> T {
        T::conv_nearest(self)
    }
    #[inline]
    fn cast_floor(self) -> T {
        T::conv_floor(self)
    }
    #[inline]
    fn cast_ceil(self) -> T {
        T::conv_ceil(self)
    }

    #[inline]
    fn try_cast_trunc(self) -> Result<T, Error> {
        T::try_conv_trunc(self)
    }
    #[inline]
    fn try_cast_nearest(self) -> Result<T, Error> {
        T::try_conv_nearest(self)
    }
    #[inline]
    fn try_cast_floor(self) -> Result<T, Error> {
        T::try_conv_floor(self)
    }
    #[inline]
    fn try_cast_ceil(self) -> Result<T, Error> {
        T::try_conv_ceil(self)
    }
}
