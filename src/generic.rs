// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License in the LICENSE-APACHE file or at:
//     https://www.apache.org/licenses/LICENSE-2.0

//! Generic conversion support
//!
//! The [`Convert`] trait is generic over rounding modes. This is provided as a
//! tool to facilitate writing conversions; [other traits](crate::traits) may be
//! easier to use to convert values.

/// Rounding mode
pub trait Rounding: Copy + Default {}

/// Exact conversion only
///
/// Successful conversions using this "rounding" mode must preserve value
/// exactly.
///
/// Example: `2.0_f32` may convert to `2_i32`. `2.1_f32` is not convertible to
/// `i32`.
#[derive(Clone, Copy, Debug, Default)]
pub struct Exact;
impl Rounding for Exact {}

/// Generic conversion trait
///
/// This trait is an extension over [`From`] and [`TryFrom`] for numeric casts.
pub trait Convert<S, R: Rounding>: Sized {
    /// Conversion error type
    type Error: Into<crate::Error> + core::error::Error;

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
