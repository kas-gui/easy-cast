// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License in the LICENSE-APACHE file or at:
//     https://www.apache.org/licenses/LICENSE-2.0

//! Rounding modes

use crate::{ConvExact, ConvTo, Error, RangeError};
use core::convert::Infallible;

/// Rounding mode
///
/// Implementations of this trait are (probably) unit structs, used to mark the
/// type of rounding used at the type level.
///
/// # Implied implementations
///
/// <code>impl&lt;S, T: [ConvExact]&lt;S&gt;&gt; [ConvTo]&lt;S, R&gt;</code> is
/// is implemented for each rounding mode `R` provided by this crate since a
/// more general impl over `R: Rounding` is not compatible with the wider trait
/// design under the limitations of Rust's current trait solver. Any rounding
/// mode added by a third-party crate should therefore provide a similar `impl`.
pub trait Rounding: Copy + Default {
    /// Maximum error type
    type MaximumError: From<Infallible> + Into<Error> + core::error::Error;
}

/// Exact conversion only
///
/// Successful conversions using this "rounding" mode must preserve the value
/// exactly.
///
/// Example: `2.0_f32` may convert to `2_i32`. `2.1_f32` is not convertible to
/// [`i32`].
///
/// Another example: [`u128::MAX`] (which is larger than [`f32::MAX`]) may not
/// be converted to [`f32`] with `Exact` rounding (with other modes it may
/// round to [`f32::INFINITY`]).
#[derive(Clone, Copy, Debug, Default)]
pub struct Exact;
impl Rounding for Exact {
    type MaximumError = Error;
}

/// Approximate conversion
///
/// This rounding mode allows an implementation-defined rounding mode.
/// The result must be close to the input value (see below).
///
/// Example: `2.1_f32` may convert to `2_i32` or to `3_i32` (either
/// implementation is valid so long as the behaviour is well-defined).
///
/// # Limits of approximation
///
/// (This section applies to all [`Rounding`] modes provided by `easy-cast`
/// except for [`Exact`].)
///
/// The output value of a successful conversion must be close to the input
/// value. More precisely, the distance between the input and output values
/// should be less than the distance between the two closest representable
/// values in the target type.
/// For example, `1.9_f32` may be approximated to `1_i32` or `2_i32` since
/// mathematically `1.9` lies between `1` and `2`. As another example,
/// `1_f64 + (f32::EPSILON as f64) / 2.0` may be approximated to
/// `1_f32` or `1_f32 + f32::EPSILON`.
///
/// Infinity "values" like [`f32::INFINITY`] are a bit special; essentially we
/// allow any input of the appropriate sign to approximate to "infinity" where
/// the input may not approximate to another value. For example, the above rules
/// may be used to calculate the maximum `u128` value which is allowed to
/// approximate to `f32::MAX` (`0xFFFFFF7F_FFFFFFFF_FFFFFFFF_FFFFFFFF`);
/// the value above this should thus approximate to `f32::INFINITY`.
#[derive(Clone, Copy, Debug, Default)]
pub struct Approx;
impl Rounding for Approx {
    type MaximumError = RangeError;
}

/// Truncation towards zero
///
/// Excess precision is truncated (rounds towards zero). This is the rounding
/// mode used by [`as` numeric casts] for floating-point to integer conversions.
///
/// Example: `2.9_f32` converts to `2_i32`, `-2.9_f32` converts to `-2_i32`.
///
/// The [`§ Limits of approximation`](Approx#limits-of-approximation) as
/// specified by [`Approx`] apply.
///
/// [`as` numeric casts]: https://doc.rust-lang.org/reference/expressions/operator-expr.html#r-expr.as.numeric
#[derive(Clone, Copy, Debug, Default)]
pub struct Trunc;
impl Rounding for Trunc {
    type MaximumError = RangeError;
}

/// Round to the nearest representable value
///
/// The precise behaviour of half-way cases is implementation-defined. Provided
/// implementations follow common practices: float-to-int conversions use the
/// `round()` inherent function which rounds away from zero while int-to-float
/// conversions follow the behaviour of [`as` numeric casts] which rounds ties
/// to even.
///
/// Example: `2.5_f32` converts to `3_i32`, `-2.5_f32` converts to `-3_i32`.
/// Another example: converting [`i32::MAX`] to [`f32`] rounds up to
/// 2<sup>31</sup>.
///
/// The [`§ Limits of approximation`](Approx#limits-of-approximation) as
/// specified by [`Approx`] apply.
///
/// [`as` numeric casts]: https://doc.rust-lang.org/reference/expressions/operator-expr.html#r-expr.as.numeric
#[cfg(any(feature = "std", feature = "libm"))]
#[derive(Clone, Copy, Debug, Default)]
pub struct Nearest;
#[cfg(any(feature = "std", feature = "libm"))]
impl Rounding for Nearest {
    type MaximumError = RangeError;
}

/// Round towards negative infinity (floor)
///
/// Returns the largest integer less than or equal to the input.
///
/// Example: `2.9_f32` converts to `2_i32`, `-2.1_f32` converts to `-3_i32`.
///
/// The [`§ Limits of approximation`](Approx#limits-of-approximation) as
/// specified by [`Approx`] apply.
#[cfg(any(feature = "std", feature = "libm"))]
#[derive(Clone, Copy, Debug, Default)]
pub struct Floor;
#[cfg(any(feature = "std", feature = "libm"))]
impl Rounding for Floor {
    type MaximumError = RangeError;
}

/// Round towards positive infinity (ceiling)
///
/// Returns the smallest integer greater than or equal to the input.
///
/// Example: `2.1_f32` converts to `3_i32`, `-2.9_f32` converts to `-2_i32`.
///
/// The [`§ Limits of approximation`](Approx#limits-of-approximation) as
/// specified by [`Approx`] apply.
#[cfg(any(feature = "std", feature = "libm"))]
#[derive(Clone, Copy, Debug, Default)]
pub struct Ceil;
#[cfg(any(feature = "std", feature = "libm"))]
impl Rounding for Ceil {
    type MaximumError = RangeError;
}

impl<S, T: ConvExact<S>> ConvTo<S, Exact> for T {
    type Error = T::Error;

    #[inline]
    fn try_conv_to(_: Exact, s: S) -> Result<Self, Self::Error> {
        T::try_conv_exact(s)
    }

    #[inline]
    fn conv_to(_: Exact, s: S) -> Self {
        T::conv_exact(s)
    }
}

impl<S, T: ConvExact<S>> ConvTo<S, Approx> for T {
    type Error = T::Error;

    #[inline]
    fn try_conv_to(_: Approx, s: S) -> Result<Self, Self::Error> {
        T::try_conv_exact(s)
    }

    #[inline]
    fn conv_to(_: Approx, s: S) -> Self {
        T::conv_exact(s)
    }
}

#[cfg(any(feature = "std", feature = "libm"))]
impl<S, T: ConvExact<S>> ConvTo<S, Trunc> for T {
    type Error = T::Error;

    #[inline]
    fn try_conv_to(_: Trunc, s: S) -> Result<Self, Self::Error> {
        T::try_conv_exact(s)
    }

    #[inline]
    fn conv_to(_: Trunc, s: S) -> Self {
        T::conv_exact(s)
    }
}

#[cfg(any(feature = "std", feature = "libm"))]
impl<S, T: ConvExact<S>> ConvTo<S, Nearest> for T {
    type Error = T::Error;

    #[inline]
    fn try_conv_to(_: Nearest, s: S) -> Result<Self, Self::Error> {
        T::try_conv_exact(s)
    }

    #[inline]
    fn conv_to(_: Nearest, s: S) -> Self {
        T::conv_exact(s)
    }
}

#[cfg(any(feature = "std", feature = "libm"))]
impl<S, T: ConvExact<S>> ConvTo<S, Floor> for T {
    type Error = T::Error;

    #[inline]
    fn try_conv_to(_: Floor, s: S) -> Result<Self, Self::Error> {
        T::try_conv_exact(s)
    }

    #[inline]
    fn conv_to(_: Floor, s: S) -> Self {
        T::conv_exact(s)
    }
}

#[cfg(any(feature = "std", feature = "libm"))]
impl<S, T: ConvExact<S>> ConvTo<S, Ceil> for T {
    type Error = T::Error;

    #[inline]
    fn try_conv_to(_: Ceil, s: S) -> Result<Self, Self::Error> {
        T::try_conv_exact(s)
    }

    #[inline]
    fn conv_to(_: Ceil, s: S) -> Self {
        T::conv_exact(s)
    }
}
