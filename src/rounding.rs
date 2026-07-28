// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License in the LICENSE-APACHE file or at:
//     https://www.apache.org/licenses/LICENSE-2.0

//! Rounding modes

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

/// Truncation towards zero
///
/// Excess precision is truncated (rounds towards zero). This is the rounding
/// mode used by [`as` numeric casts] for floating-point to integer conversions.
///
/// Example: `2.9_f32` converts to `2_i32`, `-2.9_f32` converts to `-2_i32`.
///
/// [`as` numeric casts]: https://doc.rust-lang.org/reference/expressions/operator-expr.html#r-expr.as.numeric
#[cfg(any(feature = "std", feature = "libm"))]
#[derive(Clone, Copy, Debug, Default)]
pub struct Trunc;
#[cfg(any(feature = "std", feature = "libm"))]
impl Rounding for Trunc {
    type MaximumError = RangeError;
}

/// Round to nearest integer
///
/// Half-way cases are rounded away from `0`.
///
/// Example: `2.5_f32` converts to `3_i32`, `-2.5_f32` converts to `-3_i32`.
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
#[cfg(any(feature = "std", feature = "libm"))]
#[derive(Clone, Copy, Debug, Default)]
pub struct Ceil;
#[cfg(any(feature = "std", feature = "libm"))]
impl Rounding for Ceil {
    type MaximumError = RangeError;
}
