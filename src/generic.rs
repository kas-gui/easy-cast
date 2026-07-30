// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License in the LICENSE-APACHE file or at:
//     https://www.apache.org/licenses/LICENSE-2.0

//! Generic conversion support
//!
//! The traits of this module are more generic than the
//! [other traits](crate::traits) provided by `easy-cast`; in particular, these
//! traits support generality over [`Rounding`] modes and more precise error
//! types as associated types.
//!
//! [`CastTo`] and [`ConvTo`] may be used instead of
//! [`Cast`](crate::Cast) and [`Conv`](crate::Conv) where genericity over
//! [`Rounding`] modes is required.
//!
//! Conversions which can never be inexact should be implemented using
//! [`ConvExact`].
//!
//! Conversions which may apply rounding or may reject inputs not precisely
//! representable by the target type should be implemented using [`Convert`].
//! It is permissible to implement such conversions for multiple [`Rounding`]
//! modes, for example an [`Approx`] conversion (which rounds inputs where
//! required) and an [`Exact`] conversion (which rejects these inputs).
//!
//! [`CastTo`]: crate::CastTo
//! [`ConvTo`]: crate::ConvTo

use crate::ConvExact;
use crate::rounding::*;

/// Generic "from" conversion trait with specified rounding mode
///
/// This trait is similar to [`TryFrom`] but for numeric conversions with a
/// specified rounding mode. Usage with rounding mode [`Exact`] is equivalent to
/// [`Conv`](crate::Conv).
///
/// The [`Rounding`] mode must be specified:
/// ```
/// # use easy_cast::{generic::Convert, Exact, Nearest};
/// assert_eq!(i32::convert(Nearest, 7.6f32), 8);
/// assert_eq!(f32::convert(Exact, 20), 20.0);
/// ```
pub trait Convert<S, R: Rounding>: Sized {
    /// Conversion error type
    type Error: Into<R::MaximumError> + core::error::Error;

    /// Try converting from `S` to `Self`
    fn try_convert(mode: R, s: S) -> Result<Self, Self::Error>;

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
    /// [`as` numeric casts]: https://doc.rust-lang.org/reference/expressions/operator-expr.html#r-expr.as.numeric
    #[inline]
    fn convert(mode: R, s: S) -> Self {
        Self::try_convert(mode, s).unwrap_or_else(|e| panic!("Convert::convert(_) failed: {e}"))
    }
}

impl<S, T: ConvExact<S>> Convert<S, Exact> for T {
    type Error = T::Error;

    #[inline]
    fn try_convert(_: Exact, s: S) -> Result<Self, Self::Error> {
        T::try_conv_exact(s)
    }

    #[inline]
    fn convert(_: Exact, s: S) -> Self {
        T::conv_exact(s)
    }
}

impl<S, T: ConvExact<S>> Convert<S, Approx> for T {
    type Error = T::Error;

    #[inline]
    fn try_convert(_: Approx, s: S) -> Result<Self, Self::Error> {
        T::try_conv_exact(s)
    }

    #[inline]
    fn convert(_: Approx, s: S) -> Self {
        T::conv_exact(s)
    }
}

#[cfg(any(feature = "std", feature = "libm"))]
impl<S, T: ConvExact<S>> Convert<S, Trunc> for T {
    type Error = T::Error;

    #[inline]
    fn try_convert(_: Trunc, s: S) -> Result<Self, Self::Error> {
        T::try_conv_exact(s)
    }

    #[inline]
    fn convert(_: Trunc, s: S) -> Self {
        T::conv_exact(s)
    }
}

#[cfg(any(feature = "std", feature = "libm"))]
impl<S, T: ConvExact<S>> Convert<S, Nearest> for T {
    type Error = T::Error;

    #[inline]
    fn try_convert(_: Nearest, s: S) -> Result<Self, Self::Error> {
        T::try_conv_exact(s)
    }

    #[inline]
    fn convert(_: Nearest, s: S) -> Self {
        T::conv_exact(s)
    }
}

#[cfg(any(feature = "std", feature = "libm"))]
impl<S, T: ConvExact<S>> Convert<S, Floor> for T {
    type Error = T::Error;

    #[inline]
    fn try_convert(_: Floor, s: S) -> Result<Self, Self::Error> {
        T::try_conv_exact(s)
    }

    #[inline]
    fn convert(_: Floor, s: S) -> Self {
        T::conv_exact(s)
    }
}

#[cfg(any(feature = "std", feature = "libm"))]
impl<S, T: ConvExact<S>> Convert<S, Ceil> for T {
    type Error = T::Error;

    #[inline]
    fn try_convert(_: Ceil, s: S) -> Result<Self, Self::Error> {
        T::try_conv_exact(s)
    }

    #[inline]
    fn convert(_: Ceil, s: S) -> Self {
        T::conv_exact(s)
    }
}
