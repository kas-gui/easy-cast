// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License in the LICENSE-APACHE file or at:
//     https://www.apache.org/licenses/LICENSE-2.0

//! Generic conversion support
//!
//! The [`Convert`] trait is generic over rounding modes. This is provided as a
//! tool to facilitate writing conversions; [other traits](crate::traits) may be
//! easier to use to convert values.

use crate::{Error, RangeError};
use core::convert::Infallible;

/// Rounding mode
pub trait Rounding: Copy + Default {
    /// Maximum error type
    type MaximumError: From<Infallible> + Into<Error> + core::error::Error;
}

/// Exact conversion only
///
/// Successful conversions using this "rounding" mode must preserve value
/// exactly.
///
/// Example: `2.0_f32` may convert to `2_i32`. `2.1_f32` is not convertible to
/// `i32`.
#[derive(Clone, Copy, Debug, Default)]
pub struct Exact;
impl Rounding for Exact {
    type MaximumError = Error;
}

/// Approximate conversion
///
/// Conversions may apply implementation-defined rounding when converting. The
/// result must be close to the input value; more specifically the distance
/// between the result and the input value should be less than the distance
/// between the closest two representable values to the input value.
///
/// Example: `2.1_f32` may convert to `2_i32` or to `3_i32` (either
/// implementation is valid so long as the behaviour is well-defined).
#[derive(Clone, Copy, Debug, Default)]
pub struct Approx;
impl Rounding for Approx {
    type MaximumError = RangeError;
}

/// Generic "from" conversion trait for exact conversions
///
/// Implement this trait instead of [`Convert`] where conversions can never be
/// inexact. This allows impls of `Convert<S, R>` to be derived for all
/// `R: Rounding` modes.
pub trait ConvertExact<S>: Sized {
    /// Conversion error type
    ///
    /// This is either [`Infallible`] or [`RangeError`].
    type Error: Into<RangeError> + Into<crate::Error> + core::error::Error;

    /// Try converting from `S` to `Self`
    fn try_convert(s: S) -> Result<Self, Self::Error>;

    /// Convert from `S` to `Self`
    ///
    /// This method must return the same result as [`Self::try_convert`] where
    /// that method succeeds, but differs in the handling of errors:
    ///
    /// -   In debug builds the method must panic on error
    /// -   In release builds the method may return a different value so long as
    ///     the behaviour is well defined. This allows implementations to
    ///     optimize to [`as` numeric casts].
    ///
    /// [`as` numeric casts]: https://doc.rust-lang.org/reference/expressions/operator-expr.html#type-cast-expressions
    #[inline]
    fn convert(s: S) -> Self {
        Self::try_convert(s).unwrap_or_else(|e| {
            panic!("Convert::convert(_) failed: {}", e);
        })
    }
}

/// Generic "from" conversion trait
///
/// This trait is an extension over [`From`] and [`TryFrom`] for numeric casts.
pub trait Convert<S, R: Rounding>: Sized {
    /// Conversion error type
    type Error: Into<R::MaximumError> + core::error::Error;

    /// Try converting from `S` to `Self`
    fn try_convert(s: S) -> Result<Self, Self::Error>;

    /// Convert from `S` to `Self`
    ///
    /// This method must return the same result as [`Self::try_convert`] where
    /// that method succeeds, but differs in the handling of errors:
    ///
    /// -   In debug builds the method must panic on error
    /// -   In release builds the method may return a different value so long as
    ///     the behaviour is well defined. This allows implementations to
    ///     optimize to [`as` numeric casts].
    ///
    /// [`as` numeric casts]: https://doc.rust-lang.org/reference/expression
    #[inline]
    fn convert(s: S) -> Self {
        Self::try_convert(s).unwrap_or_else(|e| {
            panic!("Convert::convert(_) failed: {}", e);
        })
    }
}

impl<S, T: ConvertExact<S>> Convert<S, Exact> for T {
    type Error = T::Error;

    #[inline]
    fn try_convert(s: S) -> Result<Self, Self::Error> {
        T::try_convert(s)
    }

    #[inline]
    fn convert(s: S) -> Self {
        T::convert(s)
    }
}

impl<S, T: ConvertExact<S>> Convert<S, Approx> for T {
    type Error = T::Error;

    #[inline]
    fn try_convert(s: S) -> Result<Self, Self::Error> {
        T::try_convert(s)
    }

    #[inline]
    fn convert(s: S) -> Self {
        T::convert(s)
    }
}

/// Generic "into" conversion trait
///
/// This trait is like [`Into`] but for [`Convert`].
///
/// The [`Rounding`] mode must be specified when calling this trait's methods,
/// for example `x.try_convert(Exact)` or `y.convert(Approx)`. In generic code
/// (where `R: Rounding`), `z.try_convert(R::default())` may be used.
pub trait ConvertInto<T, R: Rounding>: Sized {
    /// Conversion error type
    type Error: Into<R::MaximumError> + core::error::Error;

    /// Try converting from `Self` to `T`
    fn try_convert(self, mode: R) -> Result<T, Self::Error>;

    /// Convert from `Self` to `T`
    ///
    /// This method must return the same result as [`Self::try_convert`] where
    /// that method succeeds, but differs in the handling of errors:
    ///
    /// -   In debug builds the method must panic on error
    /// -   In release builds the method may return a different value so long as
    ///     the behaviour is well defined. This allows implementations to
    ///     optimize to [`as` numeric casts].
    ///
    /// [`as` numeric casts]: https://doc.rust-lang.org/reference/expression
    fn convert(self, mode: R) -> T;
}

impl<R: Rounding, S, T: Convert<S, R>> ConvertInto<T, R> for S {
    type Error = T::Error;

    fn try_convert(self, _: R) -> Result<T, Self::Error> {
        T::try_convert(self)
    }

    fn convert(self, _: R) -> T {
        T::convert(self)
    }
}
