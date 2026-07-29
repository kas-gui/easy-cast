// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License in the LICENSE-APACHE file or at:
//     https://www.apache.org/licenses/LICENSE-2.0

//! Traits
//!
//! This module only contains traits, allowing relatively safe glob-import:
//! ```
//! use easy_cast::{Cast, ConvTo, generic::Nearest};
//!
//! # fn main() {
//! let x = i32::conv_to(Nearest, 8.5f32);
//! let y: f32 = 12.cast();
//! # }
//! ```

use crate::generic::{Approx, Convert, Exact, Rounding};
use crate::{Error, RangeError};

/// Like [`From`], but supports fallible conversions
///
/// This trait is similar to [`From`], but limited to numeric conversions:
/// -   Like [`TryFrom`] (unlike [`From`]), conversions may be *fallible*.
///     Unlike [`TryFrom`], precisely two failure modes are allowed:
///     domain ([`Error::Range`]) and loss-of-precision ([`Error::Inexact`]).
/// -   Like [`From`], conversions must be *lossless*. For example, `Conv<f64>`
///     is not implemented for `f32` since `f64` carries more precision; use
///     [`ConvApprox`] instead for cases where loss-of-precision is intended.
/// -   Like [`From`], conversions must be *value-preserving*. For example,
///     `-1_i8` and `-1_i32` are conceptually the same value while `255_u8` is
///     conceptually a different value, thus while `Conv<i8>` is implemented for
///     both `i32` and `u8`, attempting to convert `-1` to `u8` will fail with
///     [`RangeError`].
///
/// The sister-trait [`Cast`] supports "into" style usage.
///
/// It is recommended not to implement this trait directly but to instead
/// implement one of the [`generic`](crate::generic) traits.
pub trait Conv<S>: Sized {
    /// Conversion error type
    type Error: Into<Error> + core::error::Error;

    /// Try converting from `S` to `Self`
    ///
    /// This method must fail on inexact conversions.
    fn try_conv(s: S) -> Result<Self, Self::Error>;

    /// Convert from `S` to `Self`
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
    fn conv(s: S) -> Self {
        Self::try_conv(s).unwrap_or_else(|e| {
            panic!("Conv::conv(_) failed: {}", e);
        })
    }
}

impl<S, T: Convert<S, Exact>> Conv<S> for T {
    type Error = T::Error;

    #[inline]
    fn try_conv(s: S) -> Result<Self, Self::Error> {
        T::try_convert(s)
    }

    #[inline]
    fn conv(s: S) -> Self {
        T::convert(s)
    }
}

/// Like [`Into`], but for [`Conv`]
///
/// This trait is automatically implemented for every implementation of
/// [`Conv`].
pub trait Cast<T> {
    /// Conversion error type
    type Error: Into<Error> + core::error::Error;

    /// Try converting from `Self` to `T`
    ///
    /// Use this method to explicitly handle errors.
    fn try_cast(self) -> Result<T, Self::Error>;

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
    type Error = T::Error;

    #[inline]
    fn cast(self) -> T {
        T::conv(self)
    }
    #[inline]
    fn try_cast(self) -> Result<T, Self::Error> {
        T::try_conv(self)
    }
}

/// Like [`From`], but for approximate numerical conversions
///
/// Unlike [`Conv`], conversions are permitted to lose precision provided that
/// the result is close to the input value. More precisely, the difference
/// between the input and output values should be less than the difference
/// between the two closest representable values in the target type.
/// For example, one may have `i32::conv_approx(1.9f32) = 1` or
/// `f32::conv_approx(1f64 + (f32::EPSILON as f64) / 2.0) = 1.0`.
///
/// Only one failure mode is allowed: domain ([`RangeError`]).
///
/// The rounding mode is implementation-defined, usually aligning with the
/// behavior of [`as` numeric casts]. Use [`ConvTo`] or [`CastTo`] with
/// an explicit rounding mode (e.g. [`generic::Nearest`](crate::generic::Nearest))
/// instead where control over rounding is required.
///
/// The sister-trait [`CastApprox`] supports "into" style usage.
///
/// It is recommended not to implement this trait directly but to instead
/// implement one of the [`generic`](crate::generic) traits.
///
/// [`as` numeric casts]: https://doc.rust-lang.org/reference/expressions/operator-expr.html#r-expr.as.numeric
pub trait ConvApprox<S>: Sized {
    /// Conversion error type
    type Error: Into<RangeError> + core::error::Error;

    /// Try converting from `S` to `Self`, allowing approximation of value
    ///
    /// This conversion may truncate excess precision not supported by the
    /// target type, so long as the *value* is approximately equal, from the
    /// point of view of precision of the target type.
    ///
    /// This method should allow approximate conversion, but fail on input not
    /// (approximately) in the target's range.
    fn try_conv_approx(s: S) -> Result<Self, Self::Error>;

    /// Converting from `S` to `Self`, allowing approximation of value
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
    fn conv_approx(s: S) -> Self {
        Self::try_conv_approx(s).unwrap_or_else(|e| {
            panic!("ConvApprox::conv_approx(_) failed: {}", e);
        })
    }
}

impl<S, T: Convert<S, Approx>> ConvApprox<S> for T {
    type Error = T::Error;

    #[inline]
    fn try_conv_approx(s: S) -> Result<Self, Self::Error> {
        T::try_convert(s)
    }

    #[inline]
    fn conv_approx(s: S) -> Self {
        T::convert(s)
    }
}

/// Like [`Into`], but for [`ConvApprox`]
///
/// Unlike [`Cast`], conversions are permitted to lose precision provided that
/// the result is close to the input value. More precisely, the difference
/// between the input and output values should be less than the difference
/// between the two closest representable values in the target type.
/// For example, one may have `i32::conv_approx(1.9f32) = 1` or
/// `f32::conv_approx(1f64 + (f32::EPSILON as f64) / 2.0) = 1.0`.
///
/// The rounding mode is implementation-defined, usually aligning with the
/// behavior of [`as` numeric casts]. Use [`ConvTo`] or [`CastTo`] with
/// an explicit rounding mode (e.g. [`generic::Nearest`](crate::generic::Nearest))
/// instead where control over rounding is required.
///
/// This trait is automatically implemented for every implementation of
/// [`ConvApprox`].
pub trait CastApprox<T> {
    /// Conversion error type
    type Error: Into<RangeError> + core::error::Error;

    /// Try approximate conversion from `Self` to `T`
    ///
    /// Use this method to explicitly handle errors.
    fn try_cast_approx(self) -> Result<T, Self::Error>;

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
    type Error = T::Error;

    #[inline]
    fn try_cast_approx(self) -> Result<T, Self::Error> {
        T::try_conv_approx(self)
    }
    #[inline]
    fn cast_approx(self) -> T {
        T::conv_approx(self)
    }
}

/// Generic "from" conversion trait with specified rounding mode
///
/// This trait is like [`From`] but for [`Convert`]. It is similar to
/// [`Conv`] but provides control over the rounding mode used.
///
/// The [`Rounding`] mode must be specified when calling this trait's methods,
/// for example `f32::try_conv_to(Exact, x)` or `i32::conv_to(Approx, y)`.
pub trait ConvTo<S, R: Rounding>: Sized {
    /// Conversion error type
    type Error: Into<R::MaximumError> + core::error::Error;

    /// Try converting from `S` to `Self`
    fn try_conv_to(mode: R, s: S) -> Result<Self, Self::Error>;

    /// Convert from `S` to `Self`
    ///
    /// This method must return the same result as [`Self::try_conv_to`] where
    /// that method succeeds, but differs in the handling of errors:
    ///
    /// -   In debug builds the method must panic on error
    /// -   In release builds the method may return a different value so long as
    ///     the behaviour is well defined. This allows implementations to
    ///     optimize to [`as` numeric casts].
    ///
    /// [`as` numeric casts]: https://doc.rust-lang.org/reference/expressions/operator-expr.html#r-expr.as.numeric
    fn conv_to(mode: R, s: S) -> Self;
}

impl<R: Rounding, S, T: Convert<S, R>> ConvTo<S, R> for T {
    type Error = T::Error;

    fn try_conv_to(_: R, s: S) -> Result<Self, Self::Error> {
        T::try_convert(s)
    }

    fn conv_to(_: R, s: S) -> Self {
        T::convert(s)
    }
}

/// Generic "into" conversion trait with specified rounding mode
///
/// This trait is like [`Into`] but for [`ConvTo`]. It is similar to
/// [`Cast`] but provides control over rounding modes.
///
/// The [`Rounding`] mode must be specified when calling this trait's methods,
/// for example `x.try_cast_to(Exact)` or `y.cast_to(Approx)`. In generic code
/// (where `R: Rounding`), `z.try_cast_to(R::default())` may be used.
pub trait CastTo<T, R: Rounding>: Sized {
    /// Conversion error type
    type Error: Into<R::MaximumError> + core::error::Error;

    /// Try converting from `Self` to `T`
    fn try_cast_to(self, mode: R) -> Result<T, Self::Error>;

    /// Convert from `Self` to `T`
    ///
    /// This method must return the same result as [`Self::try_cast_to`] where
    /// that method succeeds, but differs in the handling of errors:
    ///
    /// -   In debug builds the method must panic on error
    /// -   In release builds the method may return a different value so long as
    ///     the behaviour is well defined. This allows implementations to
    ///     optimize to [`as` numeric casts].
    ///
    /// [`as` numeric casts]: https://doc.rust-lang.org/reference/expressions/operator-expr.html#r-expr.as.numeric
    fn cast_to(self, mode: R) -> T;
}

impl<R: Rounding, S, T: Convert<S, R>> CastTo<T, R> for S {
    type Error = T::Error;

    fn try_cast_to(self, _: R) -> Result<T, Self::Error> {
        T::try_convert(self)
    }

    fn cast_to(self, _: R) -> T {
        T::convert(self)
    }
}
