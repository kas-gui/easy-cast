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
//! [`RoundInto`] and [`RoundFrom`] may be used instead of
//! [`Cast`](crate::Cast) and [`Conv`](crate::Conv) where genericity over
//! [`Rounding`] modes is required.
//!
//! Conversions which can never be inexact should be implemented using
//! [`ConvertExact`].
//!
//! Conversions which may apply rounding or may reject inputs not precisely
//! representable by the target type should be implemented using [`Convert`].
//! It is permissible to implement such conversions for multiple [`Rounding`]
//! modes, for example an [`Approx`] conversion (which rounds inputs where
//! required) and an [`Exact`] conversion (which rejects these inputs).
//!
//! [`RoundInto`]: crate::RoundInto
//! [`RoundFrom`]: crate::RoundFrom

use crate::RangeError;

#[doc(inline)]
pub use crate::rounding::*;

/// Generic "from" conversion trait for exact conversions
///
/// Implement this trait instead of [`Convert`] where conversions can never be
/// inexact. This allows impls of `Convert<S, R>` to be derived for all
/// `R: Rounding` modes.
pub trait ConvertExact<S>: Sized {
    /// Conversion error type
    ///
    /// This is either [`Infallible`] or [`RangeError`].
    ///
    /// [`Infallible`]: std::convert::Infallible
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
    /// [`as` numeric casts]: https://doc.rust-lang.org/reference/expressions/operator-expr.html#r-expr.as.numeric
    #[inline]
    fn convert(s: S) -> Self {
        Self::try_convert(s).unwrap_or_else(|e| {
            panic!("ConvertExact::convert(_) failed: {}", e);
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
    /// [`as` numeric casts]: https://doc.rust-lang.org/reference/expressions/operator-expr.html#r-expr.as.numeric
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

#[cfg(any(feature = "std", feature = "libm"))]
impl<S, T: ConvertExact<S>> Convert<S, Trunc> for T {
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

#[cfg(any(feature = "std", feature = "libm"))]
impl<S, T: ConvertExact<S>> Convert<S, Nearest> for T {
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

#[cfg(any(feature = "std", feature = "libm"))]
impl<S, T: ConvertExact<S>> Convert<S, Floor> for T {
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

#[cfg(any(feature = "std", feature = "libm"))]
impl<S, T: ConvertExact<S>> Convert<S, Ceil> for T {
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
