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
        write!(
            f,
            "cast conversion: {}",
            match self {
                Error::Range => "source value not in target range",
                Error::Inexact => "loss of precision or range error",
            }
        )
    }
}

#[cfg(feature = "std")]
impl std::error::Error for Error {}

/// Like [`From`], but supporting potentially-fallible conversions
///
/// This trait is intended to replace *many* uses of the `as` keyword for
/// numeric conversions, though not all.
/// Conversions from floating-point types are excluded since it is very easy to
/// (accidentally) produce non-integer values; instead use [`ConvFloat`].
///
/// Two methods are provided:
///
/// -   [`Conv::conv`] is for "success expected" conversions. In debug builds
///     and when using the `always_assert` feature flag, inexact conversions
///     will panic. In other cases, conversions may produce incorrect values
///     (according to the behaviour of `as`). This is similar to the behviour of
///     Rust's overflow checks on integer arithmetic, and intended for usage
///     when the user is "reasonably sure" that conversion will succeed.
/// -   [`Conv::try_conv`] is for fallible conversions, and always produces an
///     error if the conversion would be inexact.
pub trait Conv<T>: Sized {
    /// Convert from `T` to `Self`
    fn conv(v: T) -> Self;

    /// Try converting from `T` to `Self`
    fn try_conv(v: T) -> Result<Self, Error>;
}

impl<T> Conv<T> for T {
    #[inline]
    fn conv(v: T) -> Self {
        v
    }
    #[inline]
    fn try_conv(v: T) -> Result<Self, Error> {
        Ok(v)
    }
}

macro_rules! impl_via_from {
    ($x:ty: $y:ty) => {
        impl Conv<$x> for $y {
            #[inline]
            fn conv(x: $x) -> $y {
                <$y>::from(x)
            }
            #[inline]
            fn try_conv(x: $x) -> Result<Self, Error> {
                Ok(<$y>::from(x))
            }
        }
    };
    ($x:ty: $y:ty, $($yy:ty),+) => {
        impl_via_from!($x: $y);
        impl_via_from!($x: $($yy),+);
    };
}

impl_via_from!(f32: f64);
impl_via_from!(i8: f32, f64, i16, i32, i64, i128);
impl_via_from!(i16: f32, f64, i32, i64, i128);
impl_via_from!(i32: f64, i64, i128);
impl_via_from!(i64: i128);
impl_via_from!(u8: f32, f64, i16, i32, i64, i128);
impl_via_from!(u8: u16, u32, u64, u128);
impl_via_from!(u16: f32, f64, i32, i64, i128, u32, u64, u128);
impl_via_from!(u32: f64, i64, i128, u64, u128);
impl_via_from!(u64: i128, u128);

macro_rules! impl_via_as_neg_check {
    ($x:ty: $y:ty) => {
        impl Conv<$x> for $y {
            #[inline]
            fn conv(x: $x) -> $y {
                #[cfg(any(debug_assertions, feature = "assert_int"))]
                assert!(x >= 0);
                x as $y
            }
            #[inline]
            fn try_conv(x: $x) -> Result<Self, Error> {
                if x >= 0 {
                    Ok(x as $y)
                } else {
                    Err(Error::Range)
                }
            }
        }
    };
    ($x:ty: $y:ty, $($yy:ty),+) => {
        impl_via_as_neg_check!($x: $y);
        impl_via_as_neg_check!($x: $($yy),+);
    };
}

impl_via_as_neg_check!(i8: u8, u16, u32, u64, u128);
impl_via_as_neg_check!(i16: u16, u32, u64, u128);
impl_via_as_neg_check!(i32: u32, u64, u128);
impl_via_as_neg_check!(i64: u64, u128);
impl_via_as_neg_check!(i128: u128);

// Assumption: $y::MAX is representable as $x
macro_rules! impl_via_as_max_check {
    ($x:ty: $y:tt) => {
        impl Conv<$x> for $y {
            #[inline]
            fn conv(x: $x) -> $y {
                #[cfg(any(debug_assertions, feature = "assert_int"))]
                assert!(x <= core::$y::MAX as $x);
                x as $y
            }
            #[inline]
            fn try_conv(x: $x) -> Result<Self, Error> {
                if x <= core::$y::MAX as $x {
                    Ok(x as $y)
                } else {
                    Err(Error::Range)
                }
            }
        }
    };
    ($x:ty: $y:tt, $($yy:tt),+) => {
        impl_via_as_max_check!($x: $y);
        impl_via_as_max_check!($x: $($yy),+);
    };
}

impl_via_as_max_check!(u8: i8);
impl_via_as_max_check!(u16: i8, i16, u8);
impl_via_as_max_check!(u32: i8, i16, i32, u8, u16);
impl_via_as_max_check!(u64: i8, i16, i32, i64, u8, u16, u32);
impl_via_as_max_check!(u128: i8, i16, i32, i64, i128);
impl_via_as_max_check!(u128: u8, u16, u32, u64);

// Assumption: $y::MAX and $y::MIN are representable as $x
macro_rules! impl_via_as_range_check {
    ($x:ty: $y:tt) => {
        impl Conv<$x> for $y {
            #[inline]
            fn conv(x: $x) -> $y {
                #[cfg(any(debug_assertions, feature = "assert_int"))]
                assert!(core::$y::MIN as $x <= x && x <= core::$y::MAX as $x);
                x as $y
            }
            #[inline]
            fn try_conv(x: $x) -> Result<Self, Error> {
                if core::$y::MIN as $x <= x && x <= core::$y::MAX as $x {
                    Ok(x as $y)
                } else {
                    Err(Error::Range)
                }
            }
        }
    };
    ($x:ty: $y:tt, $($yy:tt),+) => {
        impl_via_as_range_check!($x: $y);
        impl_via_as_range_check!($x: $($yy),+);
    };
}

impl_via_as_range_check!(i16: i8, u8);
impl_via_as_range_check!(i32: i8, i16, u8, u16);
impl_via_as_range_check!(i64: i8, i16, i32, u8, u16, u32);
impl_via_as_range_check!(i128: i8, i16, i32, i64, u8, u16, u32, u64);

macro_rules! impl_int_signed_dest {
    ($x:ty: $y:tt) => {
        impl Conv<$x> for $y {
            #[inline]
            fn conv(x: $x) -> $y {
                if size_of::<$x>() == size_of::<$y>() {
                    #[cfg(any(debug_assertions, feature = "assert_int"))]
                    assert!(x <= core::$y::MAX as $x);
                } else if size_of::<$x>() > size_of::<$y>() {
                    #[cfg(any(debug_assertions, feature = "assert_int"))]
                    assert!(core::$y::MIN as $x <= x && x <= core::$y::MAX as $x);
                }
                x as $y
            }
            #[inline]
            fn try_conv(x: $x) -> Result<Self, Error> {
                if size_of::<$x>() == size_of::<$y>() {
                    if x <= core::$y::MAX as $x {
                        return Ok(x as $y);
                    }
                } else if size_of::<$x>() > size_of::<$y>() {
                    if core::$y::MIN as $x <= x && x <= core::$y::MAX as $x {
                        return Ok(x as $y);
                    }
                } else {
                    return Ok(x as $y);
                }
                Err(Error::Range)
            }
        }
    };
    ($x:ty: $y:tt, $($yy:tt),+) => {
        impl_int_signed_dest!($x: $y);
        impl_int_signed_dest!($x: $($yy),+);
    };
}

impl_int_signed_dest!(i8: isize);
impl_int_signed_dest!(i16: isize);
impl_int_signed_dest!(i32: isize);
impl_int_signed_dest!(i64: isize);
impl_int_signed_dest!(i128: isize);
impl_int_signed_dest!(u8: isize);
impl_int_signed_dest!(u16: isize);
impl_int_signed_dest!(u32: isize);
impl_int_signed_dest!(u64: isize);
impl_int_signed_dest!(u128: isize);
impl_int_signed_dest!(isize: i8, i16, i32, i64, i128);
impl_int_signed_dest!(usize: i8, i16, i32, i64, i128, isize);

macro_rules! impl_int_signed_to_unsigned {
    ($x:ty: $y:tt) => {
        impl Conv<$x> for $y {
            #[inline]
            fn conv(x: $x) -> $y {
                if size_of::<$x>() > size_of::<$y>() {
                    #[cfg(any(debug_assertions, feature = "assert_int"))]
                    assert!(x >= 0 && x <= core::$y::MAX as $x);
                } else {
                    #[cfg(any(debug_assertions, feature = "assert_int"))]
                    assert!(x >= 0);
                }
                x as $y
            }
            #[inline]
            fn try_conv(x: $x) -> Result<Self, Error> {
                if size_of::<$x>() > size_of::<$y>() {
                    if x >= 0 && x <= core::$y::MAX as $x {
                        return Ok(x as $y);
                    }
                } else if x >= 0 {
                    return Ok(x as $y);
                }
                Err(Error::Range)
            }
        }
    };
    ($x:ty: $y:tt, $($yy:tt),+) => {
        impl_int_signed_to_unsigned!($x: $y);
        impl_int_signed_to_unsigned!($x: $($yy),+);
    };
}

impl_int_signed_to_unsigned!(i8: usize);
impl_int_signed_to_unsigned!(i16: usize);
impl_int_signed_to_unsigned!(i32: usize);
impl_int_signed_to_unsigned!(i64: usize);
impl_int_signed_to_unsigned!(i128: usize);
impl_int_signed_to_unsigned!(isize: u8, u16, u32, u64, u128, usize);

macro_rules! impl_int_unsigned_to_unsigned {
    ($x:ty: $y:tt) => {
        impl Conv<$x> for $y {
            #[inline]
            fn conv(x: $x) -> $y {
                if size_of::<$x>() > size_of::<$y>() {
                    #[cfg(any(debug_assertions, feature = "assert_int"))]
                    assert!(x <= core::$y::MAX as $x);
                }
                x as $y
            }
            #[inline]
            fn try_conv(x: $x) -> Result<Self, Error> {
                if size_of::<$x>() > size_of::<$y>() {
                    if x <= core::$y::MAX as $x {
                        return Ok(x as $y);
                    }
                } else {
                    return Ok(x as $y);
                }
                Err(Error::Range)
            }
        }
    };
    ($x:ty: $y:tt, $($yy:tt),+) => {
        impl_int_unsigned_to_unsigned!($x: $y);
        impl_int_unsigned_to_unsigned!($x: $($yy),+);
    };
}

impl_int_unsigned_to_unsigned!(u8: usize);
impl_int_unsigned_to_unsigned!(u16: usize);
impl_int_unsigned_to_unsigned!(u32: usize);
impl_int_unsigned_to_unsigned!(u64: usize);
impl_int_unsigned_to_unsigned!(u128: usize);
impl_int_unsigned_to_unsigned!(usize: u8, u16, u32, u64, u128);

macro_rules! impl_via_digits_check {
    ($x:ty: $y:tt) => {
        impl Conv<$x> for $y {
            #[inline]
            fn conv(x: $x) -> Self {
                if cfg!(any(debug_assertions, feature = "assert_digits")) {
                    Self::try_conv(x).expect("int-to-float conversion: inexact")
                } else {
                    x as $y
                }
            }
            #[inline]
            fn try_conv(x: $x) -> Result<Self, Error> {
                let src_ty_bits = (size_of::<$x>() * 8) as u32;
                let src_digits = src_ty_bits.saturating_sub(x.leading_zeros() + x.trailing_zeros());
                let dst_digits = core::$y::MANTISSA_DIGITS;
                if src_digits <= dst_digits {
                    Ok(x as $y)
                } else {
                    Err(Error::Inexact)
                }
            }
        }
    };
    ($x:ty: $y:tt, $($yy:tt),+) => {
        impl_via_digits_check!($x: $y);
        impl_via_digits_check!($x: $($yy),+);
    };
}

impl_via_digits_check!(i32: f32);
impl_via_digits_check!(u32: f32);
impl_via_digits_check!(i64: f32, f64);
impl_via_digits_check!(u64: f32, f64);
impl_via_digits_check!(i128: f32, f64);
impl_via_digits_check!(u128: f32, f64);
impl_via_digits_check!(isize: f32, f64);
impl_via_digits_check!(usize: f32, f64);

#[cfg(all(not(feature = "std"), feature = "libm"))]
trait FloatRound {
    fn round(self) -> Self;
    fn floor(self) -> Self;
    fn ceil(self) -> Self;
}
#[cfg(all(not(feature = "std"), feature = "libm"))]
impl FloatRound for f32 {
    fn round(self) -> Self {
        libm::roundf(self)
    }
    fn floor(self) -> Self {
        libm::floorf(self)
    }
    fn ceil(self) -> Self {
        libm::ceilf(self)
    }
}
#[cfg(all(not(feature = "std"), feature = "libm"))]
impl FloatRound for f64 {
    fn round(self) -> Self {
        libm::round(self)
    }
    fn floor(self) -> Self {
        libm::floor(self)
    }
    fn ceil(self) -> Self {
        libm::ceil(self)
    }
}

/// Nearest / floor / ceil conversions from floating point types
///
/// This trait is explicitly for conversions from floating-point values to
/// integers, supporting four rounding modes for fallible and for
/// "success expected" conversions.
///
/// Two sets of methods are provided:
///
/// -   `conv_*` methods are for "success expected" conversions. In debug builds
///     and when using the `always_assert` or the `assert_float` feature flag,
///     out-of-range conversions will panic. In other cases, conversions may
///     produce incorrect values (according to the behaviour of as, which is
///     saturating cast since Rust 1.45.0 and undefined for older compilers).
///     Non-finite source values (`inf` and `NaN`) are considered out-of-range.
/// -   `try_conv_*` methods are for fallible conversions and always produce an
///     error if the conversion would be out of range.
///
/// For `f64` to `f32` where loss-of-precision is allowable, it is probably
/// acceptable to use `as` (and if need be, check that the result is finite
/// with `x.is_finite()`). The reverse, `f32` to `f64`, is always exact.
#[cfg(any(feature = "std", feature = "libm"))]
#[cfg_attr(doc_cfg, doc(cfg(any(feature = "std", feature = "libm"))))]
pub trait ConvFloat<T>: Sized {
    /// Convert to integer with truncatation
    ///
    /// Rounds towards zero (same as `as`).
    fn conv_trunc(x: T) -> Self;
    /// Convert to the nearest integer
    ///
    /// Half-way cases are rounded away from `0`.
    fn conv_nearest(x: T) -> Self;
    /// Convert the floor to an integer
    ///
    /// Returns the largest integer less than or equal to `x`.
    fn conv_floor(x: T) -> Self;
    /// Convert the ceiling to an integer
    ///
    /// Returns the smallest integer greater than or equal to `x`.
    fn conv_ceil(x: T) -> Self;

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
}

#[cfg(any(feature = "std", feature = "libm"))]
#[cfg_attr(doc_cfg, doc(cfg(any(feature = "std", feature = "libm"))))]
macro_rules! impl_float {
    ($x:ty: $y:tt) => {
        impl ConvFloat<$x> for $y {
            #[inline]
            fn conv_trunc(x: $x) -> $y {
                if cfg!(any(debug_assertions, feature = "assert_float")) {
                    Self::try_conv_trunc(x).expect("float-to-int conversion: range error")
                } else {
                    x as $y
                }
            }
            #[inline]
            fn conv_nearest(x: $x) -> $y {
                if cfg!(any(debug_assertions, feature = "assert_float")) {
                    Self::try_conv_nearest(x).expect("float-to-int conversion: range error")
                } else {
                    x.round() as $y
                }
            }
            #[inline]
            fn conv_floor(x: $x) -> $y {
                if cfg!(any(debug_assertions, feature = "assert_float")) {
                    Self::try_conv_floor(x).expect("float-to-int conversion: range error")
                } else {
                    x.floor() as $y
                }
            }
            #[inline]
            fn conv_ceil(x: $x) -> $y {
                if cfg!(any(debug_assertions, feature = "assert_float")) {
                    Self::try_conv_ceil(x).expect("float-to-int conversion: range error")
                } else {
                    x.ceil() as $y
                }
            }

            #[inline]
            fn try_conv_trunc(x: $x) -> Result<Self, Error> {
                // Tested: these limits work for $x=f32 and all $y except u128
                const LBOUND: $x = core::$y::MIN as $x - 1.0;
                const UBOUND: $x = core::$y::MAX as $x + 1.0;
                if x > LBOUND && x < UBOUND {
                    Ok(x as $y)
                } else {
                    Err(Error::Range)
                }
            }
            #[inline]
            fn try_conv_nearest(x: $x) -> Result<Self, Error> {
                // Tested: these limits work for $x=f32 and all $y except u128
                const LBOUND: $x = core::$y::MIN as $x;
                const UBOUND: $x = core::$y::MAX as $x + 1.0;
                let x = x.round();
                if x >= LBOUND && x < UBOUND {
                    Ok(x as $y)
                } else {
                    Err(Error::Range)
                }
            }
            #[inline]
            fn try_conv_floor(x: $x) -> Result<Self, Error> {
                // Tested: these limits work for $x=f32 and all $y except u128
                const LBOUND: $x = core::$y::MIN as $x;
                const UBOUND: $x = core::$y::MAX as $x + 1.0;
                let x = x.floor();
                if x >= LBOUND && x < UBOUND {
                    Ok(x as $y)
                } else {
                    Err(Error::Range)
                }
            }
            #[inline]
            fn try_conv_ceil(x: $x) -> Result<Self, Error> {
                // Tested: these limits work for $x=f32 and all $y except u128
                const LBOUND: $x = core::$y::MIN as $x;
                const UBOUND: $x = core::$y::MAX as $x + 1.0;
                let x = x.ceil();
                if x >= LBOUND && x < UBOUND {
                    Ok(x as $y)
                } else {
                    Err(Error::Range)
                }
            }
        }
    };
    ($x:ty: $y:tt, $($yy:tt),+) => {
        impl_float!($x: $y);
        impl_float!($x: $($yy),+);
    };
}

// Assumption: usize < 128-bit
#[cfg(any(feature = "std", feature = "libm"))]
impl_float!(f32: i8, i16, i32, i64, i128, isize);
#[cfg(any(feature = "std", feature = "libm"))]
impl_float!(f32: u8, u16, u32, u64, usize);
#[cfg(any(feature = "std", feature = "libm"))]
impl_float!(f64: i8, i16, i32, i64, i128, isize);
#[cfg(any(feature = "std", feature = "libm"))]
impl_float!(f64: u8, u16, u32, u64, u128, usize);

#[cfg(any(feature = "std", feature = "libm"))]
impl ConvFloat<f32> for u128 {
    #[inline]
    fn conv_trunc(x: f32) -> u128 {
        if cfg!(any(debug_assertions, feature = "assert_float")) {
            Self::try_conv_trunc(x).expect("float-to-int conversion: range error")
        } else {
            x as u128
        }
    }
    #[inline]
    fn conv_nearest(x: f32) -> u128 {
        if cfg!(any(debug_assertions, feature = "assert_float")) {
            Self::try_conv_nearest(x).expect("float-to-int conversion: range error")
        } else {
            x.round() as u128
        }
    }
    #[inline]
    fn conv_floor(x: f32) -> u128 {
        ConvFloat::conv_trunc(x)
    }
    #[inline]
    fn conv_ceil(x: f32) -> u128 {
        if cfg!(any(debug_assertions, feature = "assert_float")) {
            Self::try_conv_ceil(x).expect("float-to-int conversion: range error")
        } else {
            x.ceil() as u128
        }
    }

    #[inline]
    fn try_conv_trunc(x: f32) -> Result<Self, Error> {
        // Note: f32::MAX < u128::MAX
        if x >= 0.0 && x.is_finite() {
            Ok(x as u128)
        } else {
            Err(Error::Range)
        }
    }
    #[inline]
    fn try_conv_nearest(x: f32) -> Result<Self, Error> {
        let x = x.round();
        if x >= 0.0 && x.is_finite() {
            Ok(x as u128)
        } else {
            Err(Error::Range)
        }
    }
    #[inline]
    fn try_conv_floor(x: f32) -> Result<Self, Error> {
        Self::try_conv_trunc(x)
    }
    #[inline]
    fn try_conv_ceil(x: f32) -> Result<Self, Error> {
        let x = x.ceil();
        if x >= 0.0 && x.is_finite() {
            Ok(x as u128)
        } else {
            Err(Error::Range)
        }
    }
}

/// Like [`Into`], but for [`Conv`]
///
/// Two methods are provided:
///
/// -   [`Cast::cast`] is for "success expected" conversions. In debug builds
///     and when using the `always_assert` feature flag, inexact conversions
///     will panic. In other cases, conversions may produce incorrect values
///     (according to the behaviour of `as`). This is similar to the behviour of
///     Rust's overflow checks on integer arithmetic, and intended for usage
///     when the user is "reasonably sure" that conversion will succeed.
/// -   [`Cast::try_cast`] is for fallible conversions, and always produces an
///     error if the conversion would be inexact.
pub trait Cast<T> {
    /// Cast from `Self` to `T`
    fn cast(self) -> T;

    /// Try converting from `Self` to `T`
    fn try_cast(self) -> Result<T, Error>;
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

/// Like [`Into`], but for [`ConvFloat`]
///
/// Two sets of methods are provided:
///
/// -   `cast_*` methods are for "success expected" conversions. In debug builds
///     and when using the `always_assert` or the `assert_float` feature flag,
///     out-of-range conversions will panic. In other cases, conversions may
///     produce incorrect values (according to the behaviour of as, which is
///     saturating cast since Rust 1.45.0 and undefined for older compilers).
///     Non-finite source values (`inf` and `NaN`) are considered out-of-range.
/// -   `try_cast_*` methods are for fallible conversions and always produce an
///     error if the conversion would be out of range.
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
