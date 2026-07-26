// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License in the LICENSE-APACHE file or at:
//     https://www.apache.org/licenses/LICENSE-2.0

//! Traits
//!
//! This module only contains traits, allowing relatively safe glob-import:
//! ```
//! use easy_cast::traits::*;
//!
//! # fn main() {
//! let x = i32::conv_nearest(8.5);
//! let y: f32 = 12.cast();
//! # }
//! ```

use crate::generic::{Approx, Convert, Exact, Rounding};
use crate::{Error, RangeError};

/// Like [`From`], but supports fallible conversions
///
/// This trait is similar to [`From`], but limited to numeric conversions:
/// -   Like [`TryFrom`] (unlike [`From`]), conversions may be *fallible*.
///     Unlike [`TryFrom`], the [`Error`] type is fixed with precisely two
///     variants: [`Error::Range`] and [`Error::Inexact`].
/// -   Like [`From`], conversions must be *lossless*. For example, `Conv<f64>`
///     is not implemented for `f32` since `f64` carries more precision; use
///     [`ConvApprox`] instead for cases where loss-of-precision is intended.
/// -   Like [`From`], conversions must be *value-preserving*. For example,
///     `-1_i8` and `-1_i32` are conceptually the same value while `255_u8` is
///     conceptually a different value, thus while `Conv<i8>` is implemented for
///     both `i32` and `u8`, attempting to convert `-1` to `u8` will fail with
///     [`Error::Range`].
///
/// The sister-trait [`Cast`] supports "into" style usage.
///
/// It is recommended not to implement this trait directly but to instead
/// implement one of the [`generic`](crate::generic) traits.
pub trait Conv<S>: Sized {
    /// Try converting from `S` to `Self`
    ///
    /// This method must fail on inexact conversions.
    fn try_conv(s: S) -> Result<Self, Error>;

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
    #[inline]
    fn try_conv(s: S) -> Result<Self, Error> {
        T::try_convert(s).map_err(Into::into)
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
/// Unlike [`Conv`], conversions are permitted to lose precision provided that
/// the result is close to the input value. More precisely, the difference
/// between the input and output values should be less than the difference
/// between the two closest representable values in the target type.
/// For example, one may have `i32::conv_approx(1.9f32) = 1` or
/// `f32::conv_approx(1f64 + (f32::EPSILON as f64) / 2.0) = 1.0`.
///
/// The rounding mode is implementation-defined, usually aligning with the
/// behavior of [`as` numeric casts]. Use [`ConvFloat`] instead where control
/// over rounding modes is required.
///
/// The sister-trait [`CastApprox`] supports "into" style usage.
///
/// It is recommended not to implement this trait directly but to instead
/// implement one of the [`generic`](crate::generic) traits.
///
/// [`as` numeric casts]: https://doc.rust-lang.org/reference/expressions/operator-expr.html#type-cast-expressions
pub trait ConvApprox<S>: Sized {
    /// Try converting from `S` to `Self`, allowing approximation of value
    ///
    /// This conversion may truncate excess precision not supported by the
    /// target type, so long as the *value* is approximately equal, from the
    /// point of view of precision of the target type.
    ///
    /// This method should allow approximate conversion, but fail on input not
    /// (approximately) in the target's range.
    fn try_conv_approx(s: S) -> Result<Self, RangeError>;

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
    #[inline]
    fn try_conv_approx(s: S) -> Result<Self, RangeError> {
        T::try_convert(s).map_err(Into::into)
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
/// behavior of [`as` numeric casts]. Use [`CastFloat`] instead where control
/// over rounding modes is required.
///
/// This trait is automatically implemented for every implementation of
/// [`ConvApprox`].
pub trait CastApprox<T> {
    /// Try approximate conversion from `Self` to `T`
    ///
    /// Use this method to explicitly handle errors.
    fn try_cast_approx(self) -> Result<T, RangeError>;

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
    fn try_cast_approx(self) -> Result<T, RangeError> {
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
/// The sister-trait [`CastFloat`] supports "into" style usage.
#[cfg(any(feature = "std", feature = "libm"))]
pub trait ConvFloat<T>: Sized {
    /// Try converting to integer with truncation
    ///
    /// Rounds towards zero (same as `as`).
    fn try_conv_trunc(x: T) -> Result<Self, RangeError>;
    /// Try converting to the nearest integer
    ///
    /// Half-way cases are rounded away from `0`.
    fn try_conv_nearest(x: T) -> Result<Self, RangeError>;
    /// Try converting the floor to an integer
    ///
    /// Returns the largest integer less than or equal to `x`.
    fn try_conv_floor(x: T) -> Result<Self, RangeError>;
    /// Try convert the ceiling to an integer
    ///
    /// Returns the smallest integer greater than or equal to `x`.
    fn try_conv_ceil(x: T) -> Result<Self, RangeError>;

    /// Convert to integer with truncatation
    ///
    /// Rounds towards zero (same as `as`).
    #[inline]
    fn conv_trunc(x: T) -> Self {
        Self::try_conv_trunc(x).unwrap_or_else(|e| panic!("ConvFloat::conv_trunc(_) failed: {}", e))
    }
    /// Convert to the nearest integer
    ///
    /// Half-way cases are rounded away from `0`.
    #[inline]
    fn conv_nearest(x: T) -> Self {
        Self::try_conv_nearest(x)
            .unwrap_or_else(|e| panic!("ConvFloat::conv_nearest(_) failed: {}", e))
    }
    /// Convert the floor to an integer
    ///
    /// Returns the largest integer less than or equal to `x`.
    #[inline]
    fn conv_floor(x: T) -> Self {
        Self::try_conv_floor(x).unwrap_or_else(|e| panic!("ConvFloat::conv_floor(_) failed: {}", e))
    }
    /// Convert the ceiling to an integer
    ///
    /// Returns the smallest integer greater than or equal to `x`.
    #[inline]
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
    fn try_cast_trunc(self) -> Result<T, RangeError>;
    /// Try converting to the nearest integer
    ///
    /// Half-way cases are rounded away from `0`.
    fn try_cast_nearest(self) -> Result<T, RangeError>;
    /// Try converting the floor to an integer
    ///
    /// Returns the largest integer less than or equal to `x`.
    fn try_cast_floor(self) -> Result<T, RangeError>;
    /// Try convert the ceiling to an integer
    ///
    /// Returns the smallest integer greater than or equal to `x`.
    fn try_cast_ceil(self) -> Result<T, RangeError>;
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
    fn try_cast_trunc(self) -> Result<T, RangeError> {
        T::try_conv_trunc(self)
    }
    #[inline]
    fn try_cast_nearest(self) -> Result<T, RangeError> {
        T::try_conv_nearest(self)
    }
    #[inline]
    fn try_cast_floor(self) -> Result<T, RangeError> {
        T::try_conv_floor(self)
    }
    #[inline]
    fn try_cast_ceil(self) -> Result<T, RangeError> {
        T::try_conv_ceil(self)
    }
}

/// Generic "into" conversion trait
///
/// This trait is like [`Into`] but for [`Convert`].
///
/// The [`Rounding`] mode must be specified when calling this trait's methods,
/// for example `x.try_round(Exact)` or `y.round(Approx)`. In generic code
/// (where `R: Rounding`), `z.try_round(R::default())` may be used.
pub trait RoundInto<T, R: Rounding>: Sized {
    /// Conversion error type
    type Error: Into<R::MaximumError> + core::error::Error;

    /// Try converting from `Self` to `T`
    fn try_round(self, mode: R) -> Result<T, Self::Error>;

    /// Convert from `Self` to `T`
    ///
    /// This method must return the same result as [`Self::try_round`] where
    /// that method succeeds, but differs in the handling of errors:
    ///
    /// -   In debug builds the method must panic on error
    /// -   In release builds the method may return a different value so long as
    ///     the behaviour is well defined. This allows implementations to
    ///     optimize to [`as` numeric casts].
    ///
    /// [`as` numeric casts]: https://doc.rust-lang.org/reference/expressions/operator-expr.html#type-cast-expressions
    fn round(self, mode: R) -> T;
}

impl<R: Rounding, S, T: Convert<S, R>> RoundInto<T, R> for S {
    type Error = T::Error;

    fn try_round(self, _: R) -> Result<T, Self::Error> {
        T::try_convert(self)
    }

    fn round(self, _: R) -> T {
        T::convert(self)
    }
}
