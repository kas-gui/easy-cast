// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License in the LICENSE-APACHE file or at:
//     https://www.apache.org/licenses/LICENSE-2.0

//! Traits
//!
//! This module only contains traits, allowing relatively safe glob-import:
//! ```
//! use easy_cast::{Nearest, traits::*};
//!
//! fn nth_power<X: CastApprox<f64>>(x: X, n: u32) {
//!     let x = x.cast_approx();    // Into-like approximate conversion
//!
//!     let power = i32::conv(n);  // From-like exact conversion
//!     let z = x.powi(power);
//!     println!("The {n}-th power of {x} is {z}");
//!
//!     // TryFrom-like approximate (nearest) conversion
//!     if let Ok(nearest) = isize::try_conv_to(Nearest, z) {
//!         println!("Nearest integer: {nearest}");
//!     }
//! }
//! ```
//!

use crate::{Approx, Error, Exact, RangeError, Rounding};
#[allow(unused)]
use core::convert::Infallible;

/// Generic "from" conversion trait for exact conversions
///
/// This trait is provided as an implementation aid only, hence there is no
/// `CastExact` (in most cases you can just use [`Cast`]).
///
/// ## Implementing exact conversions
///
/// Implement conversions which cannot lose precision using this trait.
/// Implementations of <code>[ConvTo]&lt;S, R&gt;</code> are implied for all
/// <code>R: [Rounding]</code> modes provided by this crate (see
/// [§ Implied implementations](Rounding#implied-implementations)).
///
/// ### Example
///
/// ```
/// use easy_cast::ConvExact;
/// use std::convert::Infallible;
///
/// struct MyBigInt { /* details */ }
///
/// // Support conversion from i32:
/// impl ConvExact<i32> for MyBigInt {
///     type Error = Infallible;
///
///     fn try_conv_exact(i: i32) -> Result<Self, Infallible> {
///         Ok(todo!())
///     }
///
///     // optionally also impl fn conv_exact
/// }
/// ```
///
/// Note that in practice you'll probably want to support conversion from many
/// integer types using `macro_rules!`. Or you could "cheat" with a generic
/// `impl<S: Into<i128>> ConvExact<S> for MyBigInt { ... }`.
//
// TODO(specialization): impl<T> ConvExact<T> for T
pub trait ConvExact<S>: Sized {
    /// Conversion error type
    ///
    /// This should be either [`Infallible`] or [`RangeError`].
    type Error: Into<RangeError> + Into<crate::Error> + core::error::Error;

    /// Try converting from `S` to `Self`
    fn try_conv_exact(s: S) -> Result<Self, Self::Error>;

    /// Convert from `S` to `Self`
    ///
    /// Use this method only when success is expected. On error, this method may
    /// panic or may exhibit [§ Fallback behaviour](crate#fallback-behaviour).
    ///
    /// # Implementing
    ///
    /// Implementing this method directly (with fallback behaviour) is optional.
    /// In debug builds, this method must panic on error.
    #[inline]
    fn conv_exact(s: S) -> Self {
        Self::try_conv_exact(s).unwrap_or_else(|e| {
            panic!("ConvExact::conv_exact(_) failed: {}", e);
        })
    }
}

/// Like [`From`], but supports fallible conversions
///
/// This trait has similarities to [`From`] and [`TryFrom`], but is limited to
/// numeric conversions:
/// -   Conversions may be *fallible*, like [`TryFrom`].
/// -   Conversions must be *lossless*, like [`From`]; this corresponds to the
///     [`Exact`] "rounding" mode. (See also [`ConvApprox`].)
/// -   Conversions must be *value-preserving*, like [`From`]. For example,
///     `-1_i8` and `-1_i32` are conceptually the same value while `255_u8` is
///     conceptually a different value.
///
/// The sister-trait [`Cast`] supports "into" style usage.
///
/// This trait should not be implemented directly; instead implement either
/// [`ConvExact`] or [`ConvTo`].
pub trait Conv<S>: Sized {
    /// Conversion error type
    ///
    /// This should be one of [`Infallible`], [`RangeError`] or [`Error`].
    type Error: Into<Error> + core::error::Error;

    /// Try converting from `S` to `Self`
    fn try_conv(s: S) -> Result<Self, Self::Error>;

    /// Convert from `S` to `Self`
    ///
    /// Use this method only when success is expected. On error, this method may
    /// panic or may exhibit [§ Fallback behaviour](crate#fallback-behaviour).
    fn conv(s: S) -> Self {
        Self::try_conv(s).unwrap_or_else(|e| {
            panic!("Conv::conv(_) failed: {}", e);
        })
    }
}

impl<S, T: ConvTo<S, Exact>> Conv<S> for T {
    type Error = T::Error;

    #[inline]
    fn try_conv(s: S) -> Result<Self, Self::Error> {
        T::try_conv_to(Exact, s)
    }

    #[inline]
    fn conv(s: S) -> Self {
        T::conv_to(Exact, s)
    }
}

/// Like [`Into`], but for [`Conv`]
///
/// This trait has similarities to [`Into`] and [`TryInto`], but limited to
/// numeric conversions:
/// -   Conversions may be *fallible*, like [`TryInto`].
/// -   Conversions must be *lossless*, like [`Into`]; this corresponds to the
///     [`Exact`] "rounding" mode. (See also [`CastApprox`].)
/// -   Conversions must be *value-preserving*, like [`Into`]. For example,
///     `-1_i8` and `-1_i32` are conceptually the same value while `255_u8` is
///     conceptually a different value.
///
/// This trait is automatically implemented for every implementation of
/// [`Conv`].
pub trait Cast<T> {
    /// Conversion error type
    ///
    /// This should be one of [`Infallible`], [`RangeError`] or [`Error`].
    type Error: Into<Error> + core::error::Error;

    /// Try converting from `Self` to `T`
    fn try_cast(self) -> Result<T, Self::Error>;

    /// Cast from `Self` to `T`
    ///
    /// Use this method only when success is expected. On error, this method may
    /// panic or may exhibit [§ Fallback behaviour](crate#fallback-behaviour).
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
/// This trait supports [`From`]- and [`TryFrom`]-like conversions, but allowing
/// approximation:
/// -   Conversions may be *fallible*, like [`TryFrom`].
/// -   Conversions may be *lossy*, provided that the result is close to the
///     input value (see
///     [`§ Limits of approximation`](Approx#limits-of-approximation)).
/// -   Conversions must be *value-preserving*, like [`From`]. For example,
///     `-1_i8` and `-1_i32` are conceptually the same value while `255_u8` is
///     conceptually a different value.
///
/// The rounding mode used is implementation-defined. Conversions provided by
/// this crate use the same behaviour as [`as` numeric casts]: float-to-int
/// conversions round towards zero while conversions to floating-point formats
/// produce the closest possible float (rounding ties to even).
/// Use [`ConvTo`] where specific rounding is required.
///
/// The sister-trait [`CastApprox`] supports "into" style usage.
///
/// This trait should not be implemented directly; instead implement [`ConvTo`]
/// using the [`Approx`] rounding mode.
///
/// [`as` numeric casts]: https://doc.rust-lang.org/reference/expressions/operator-expr.html#r-expr.as.numeric
pub trait ConvApprox<S>: Sized {
    /// Conversion error type
    ///
    /// This should be either [`Infallible`] or [`RangeError`].
    type Error: Into<RangeError> + core::error::Error;

    /// Try converting from `S` to `Self`, allowing approximation
    fn try_conv_approx(s: S) -> Result<Self, Self::Error>;

    /// Convert from `S` to `Self`, allowing approximation
    ///
    /// Use this method only when success is expected. On error, this method may
    /// panic or may exhibit [§ Fallback behaviour](crate#fallback-behaviour).
    #[inline]
    fn conv_approx(s: S) -> Self {
        Self::try_conv_approx(s).unwrap_or_else(|e| {
            panic!("ConvApprox::conv_approx(_) failed: {}", e);
        })
    }
}

impl<S, T: ConvTo<S, Approx>> ConvApprox<S> for T {
    type Error = T::Error;

    #[inline]
    fn try_conv_approx(s: S) -> Result<Self, Self::Error> {
        T::try_conv_to(Approx, s)
    }

    #[inline]
    fn conv_approx(s: S) -> Self {
        T::conv_to(Approx, s)
    }
}

/// Like [`Into`], but for [`ConvApprox`]
///
/// This trait supports [`Into`]- and [`TryInto`]-like conversions, but allowing
/// approximation:
/// -   Conversions may be *fallible*, like [`TryInto`].
/// -   Conversions may be *lossy*, provided that the result is close to the
///     input value (see
///     [`§ Limits of approximation`](Approx#limits-of-approximation)).
/// -   Conversions must be *value-preserving*, like [`Into`]. For example,
///     `-1_i8` and `-1_i32` are conceptually the same value while `255_u8` is
///     conceptually a different value.
///
/// The rounding mode used is implementation-defined. Conversions provided by
/// this crate use the same behaviour as [`as` numeric casts]: float-to-int
/// conversions round towards zero while conversions to floating-point formats
/// produce the closest possible float (rounding ties to even).
/// Use [`CastTo`] where specific rounding is required.
///
/// This trait is automatically implemented for every implementation of
/// [`ConvApprox`].
///
/// [`as` numeric casts]: https://doc.rust-lang.org/reference/expressions/operator-expr.html#r-expr.as.numeric
pub trait CastApprox<T> {
    /// Conversion error type
    ///
    /// This should be either [`Infallible`] or [`RangeError`].
    type Error: Into<RangeError> + core::error::Error;

    /// Try approximate conversion from `Self` to `T`
    fn try_cast_approx(self) -> Result<T, Self::Error>;

    /// Cast approximately from `Self` to `T`
    ///
    /// Use this method only when success is expected. On error, this method may
    /// panic or may exhibit [§ Fallback behaviour](crate#fallback-behaviour).
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
/// This trait supports [`From`]- and [`TryFrom`]-like conversions, but with a
/// specified rounding mode:
/// -   Conversions may be *fallible*, like [`TryFrom`].
/// -   Conversions may be *lossy*, according to the [`Rounding`] mode used.
/// -   Conversions must be *value-preserving*, like [`From`]. For example,
///     `-1_i8` and `-1_i32` are conceptually the same value while `255_u8` is
///     conceptually a different value.
///
/// The [`Rounding`] mode must be specified:
/// ```
/// # use easy_cast::{ConvTo, Exact, Nearest};
/// assert_eq!(i32::conv_to(Nearest, 7.6f32), 8);
/// assert_eq!(f32::conv_to(Exact, 20), 20.0);
/// ```
/// Usage with [`Exact`] and [`Approx`] is equivalent to usage of [`Conv`] and
/// [`ConvApprox`] respectively.
///
/// The sister-trait [`CastTo`] supports "into" style usage.
///
/// ## Implementing conversions
///
/// Implement conversions which cannot lose precision using [`ConvExact`] and
/// other conversions using this trait. Separate implementations may be provided
/// for each [`Rounding`] mode.
///
/// ### Example
///
/// ```
/// use easy_cast::{Approx, ConvTo, Error, Exact, RangeError};
///
/// struct MyFloat { /* details */ }
/// # impl MyFloat {
/// #   fn is_in_range_of<T>(&self) -> bool { todo!() }
/// #   fn is_integral(&self) -> bool { todo!() }
/// # }
///
/// impl ConvTo<MyFloat, Exact> for i32 {
///     type Error = Error;
///
///     fn try_conv_to(_: Exact, f: MyFloat) -> Result<Self, Self::Error> {
///         if f.is_in_range_of::<i32>() {
///             if f.is_integral() {
///                 Ok(todo!())
///             } else {
///                 Err(Error::Inexact)
///             }
///         } else {
///             Err(Error::Range)
///         }
///     }
///
///     // optionally also impl fn conv
/// }
///
/// impl ConvTo<MyFloat, Approx> for i32 {
///     type Error = RangeError;
///
///     fn try_conv_to(_: Approx, f: MyFloat) -> Result<Self, Self::Error> {
///         if f.is_in_range_of::<i32>() {
///             Ok(todo!())
///         } else {
///             Err(RangeError)
///         }
///     }
///
///     // optionally also impl fn conv
/// }
///
/// // optionally also implement ConvTo for other rounding modes
/// ```
pub trait ConvTo<S, R: Rounding>: Sized {
    /// Conversion error type
    ///
    /// This should be one of [`Infallible`], [`RangeError`] or [`Error`].
    type Error: Into<R::MaximumError> + core::error::Error;

    /// Try converting from `S` to `Self`, rounding according to `mode`
    fn try_conv_to(mode: R, s: S) -> Result<Self, Self::Error>;

    /// Convert from `S` to `Self`, rounding according to `mode`
    ///
    /// Use this method only when success is expected. On error, this method may
    /// panic or may exhibit [§ Fallback behaviour](crate#fallback-behaviour).
    ///
    /// # Implementing
    ///
    /// Implementing this method directly (with fallback behaviour) is optional.
    /// In debug builds, this method must panic on error.
    fn conv_to(mode: R, s: S) -> Self {
        Self::try_conv_to(mode, s).unwrap_or_else(|e| panic!("ConvTo::conv_to(_) failed: {e}"))
    }
}

/// Generic "into" conversion trait with specified rounding mode
///
/// This trait supports [`Into`]- and [`TryInto`]-like conversions, but with a
/// specified rounding mode:
/// -   Conversions may be *fallible*, like [`TryInto`].
/// -   Conversions may be *lossy*, according to the [`Rounding`] mode used.
/// -   Conversions must be *value-preserving*, like [`Into`]. For example,
///     `-1_i8` and `-1_i32` are conceptually the same value while `255_u8` is
///     conceptually a different value.
///
/// The [`Rounding`] mode must be specified:
/// ```
/// # use easy_cast::{CastTo, Floor, Nearest};
/// let x: i32 = 3.14192.cast_to(Floor);
/// assert_eq!(x, 3);
///
/// let y = (1i32 << 30) - 1;
/// let z: f32 = y.cast_to(Nearest);  // this example rounds up
/// assert_eq!(z as i32, 1i32 << 30);
/// ```
/// Usage with [`Exact`] and [`Approx`] is equivalent to usage of [`Cast`] and
/// [`CastApprox`] respectively.
///
/// This trait is automatically implemented for every implementation of [`ConvTo`].
pub trait CastTo<T, R: Rounding>: Sized {
    /// Conversion error type
    ///
    /// This should be one of [`Infallible`], [`RangeError`] or [`Error`].
    type Error: Into<R::MaximumError> + core::error::Error;

    /// Try converting from `Self` to `T`, rounding according to `mode`
    fn try_cast_to(self, mode: R) -> Result<T, Self::Error>;

    /// Convert from `Self` to `T`, rounding according to `mode`
    ///
    /// Use this method only when success is expected. On error, this method may
    /// panic or may exhibit [§ Fallback behaviour](crate#fallback-behaviour).
    fn cast_to(self, mode: R) -> T;
}

impl<R: Rounding, S, T: ConvTo<S, R>> CastTo<T, R> for S {
    type Error = T::Error;

    fn try_cast_to(self, mode: R) -> Result<T, Self::Error> {
        T::try_conv_to(mode, self)
    }

    fn cast_to(self, mode: R) -> T {
        T::conv_to(mode, self)
    }
}
