// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License in the LICENSE-APACHE file or at:
//     https://www.apache.org/licenses/LICENSE-2.0

//! Type conversion, success expected
//!
//! Use [`Conv`] and [`Cast`] when:
//!
//! -   [`From`] and [`Into`] are not enough
//! -   it is expected that the value can be represented exactly by the target type
//! -   you could use `as`, but want some assurance it's doing the right thing
//! -   you are converting numbers (future versions *might* consider supporting
//!     other conversions)
//!
//! Use [`ConvFloat`] and [`CastFloat`] when:
//!
//! -   You are converting from `f32` or `f64`
//! -   You specifically want the nearest or ceiling or floor, but don't need
//!     detailed control over rounding (e.g. round-to-even)
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

#![deny(missing_docs)]

use std::mem::size_of;

/// Like [`From`], but supporting potentially-fallible conversions
///
/// This trait is intended to replace *many* uses of the `as` keyword for
/// conversions, though not all.
/// Very roughly, it is `T::try_from(x).unwrap()`, restricted to numeric
/// conversions (or like [`From`] but with more assumptions).
///
/// -   Conversions should preserve values precisely
/// -   Conversions should succeed, but may fail (panic)
/// -   We assume that `isize` and `usize` are 32 or 64 bits
///
/// Fallible conversions are allowed. In Debug builds failure must always panic
/// but in Release builds this is not required (similar to overflow checks on
/// integer arithmetic).
///
/// Note that you *may not* want to use this where loss of precision is
/// acceptable, e.g. if an approximate conversion `x as f64` suffices.
///
/// [`From`]: std::convert::From
pub trait Conv<T> {
    /// Convert from `T` to `Self` (see trait doc)
    fn conv(v: T) -> Self;
}

impl<T> Conv<T> for T {
    fn conv(v: T) -> Self {
        v
    }
}

macro_rules! impl_via_from {
    ($x:ty: $y:ty) => {
        impl Conv<$x> for $y {
            #[inline]
            fn conv(x: $x) -> $y {
                <$y>::from(x)
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
                #[cfg(any(debug_assertions, feature = "assert_non_neg"))]
                assert!(x >= 0);
                x as $y
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
                #[cfg(any(debug_assertions, feature = "assert_range"))]
                assert!(x <= std::$y::MAX as $x);
                x as $y
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
                #[cfg(any(debug_assertions, feature = "assert_range"))]
                assert!(std::$y::MIN as $x <= x && x <= std::$y::MAX as $x);
                x as $y
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
                    #[cfg(any(debug_assertions, feature = "assert_range"))]
                    assert!(x <= std::$y::MAX as $x);
                } else if size_of::<$x>() > size_of::<$y>() {
                    #[cfg(any(debug_assertions, feature = "assert_range"))]
                    assert!(std::$y::MIN as $x <= x && x <= std::$y::MAX as $x);
                }
                x as $y
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
                #[cfg(any(debug_assertions, feature = "assert_non_neg"))]
                assert!(x >= 0);
                if size_of::<$x>() > size_of::<$y>() {
                    #[cfg(any(debug_assertions, feature = "assert_range"))]
                    assert!(x <= std::$y::MAX as $x);
                }
                x as $y
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
                    #[cfg(any(debug_assertions, feature = "assert_range"))]
                    assert!(x <= std::$y::MAX as $x);
                }
                x as $y
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

impl Conv<f64> for f32 {
    #[inline]
    fn conv(x: f64) -> f32 {
        let y = x as f32;
        #[cfg(any(debug_assertions, feature = "assert_float"))]
        assert_eq!(x, y as f64);
        y
    }
}

macro_rules! impl_via_digits_check {
    ($x:ty: $y:tt) => {
        impl Conv<$x> for $y {
            #[inline]
            fn conv(x: $x) -> $y {
                if cfg!(any(debug_assertions, feature = "assert_digits")) {
                    let src_ty_bits = u32::conv(size_of::<$x>() * 8);
                    let src_digits = src_ty_bits - (x.leading_zeros() + x.trailing_zeros());
                    let dst_digits = std::$y::MANTISSA_DIGITS;
                    assert!(src_digits <= dst_digits);
                }
                x as $y
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

/// Nearest / floor / ceil conversions from floating point types
///
/// This trait is explicitly for conversions from floating-point values to
/// integers.
///
/// If the source value is out-of-range or not-a-number then the conversion must
/// fail with a panic.
pub trait ConvFloat<T> {
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
}

macro_rules! impl_float {
    ($x:ty: $y:tt) => {
        impl ConvFloat<$x> for $y {
            #[inline]
            fn conv_nearest(x: $x) -> $y {
                let x = x.round();
                if cfg!(any(debug_assertions, feature = "assert_float")) {
                    // Tested: these limits work for $x=f32 and all $y except u128
                    const LBOUND: $x = std::$y::MIN as $x;
                    const UBOUND: $x = std::$y::MAX as $x + 1.0;
                    assert!(x >= LBOUND && x < UBOUND);
                }
                x as $y
            }
            #[inline]
            fn conv_floor(x: $x) -> $y {
                if cfg!(any(debug_assertions, feature = "assert_float")) {
                    const LBOUND: $x = std::$y::MIN as $x;
                    const UBOUND: $x = std::$y::MAX as $x + 1.0;
                    assert!(x >= LBOUND && x < UBOUND);
                }
                x as $y
            }
            #[inline]
            fn conv_ceil(x: $x) -> $y {
                let x = x.ceil();
                if cfg!(any(debug_assertions, feature = "assert_float")) {
                    const LBOUND: $x = std::$y::MIN as $x;
                    const UBOUND: $x = std::$y::MAX as $x + 1.0;
                    assert!(x >= LBOUND && x < UBOUND);
                }
                x as $y
            }
        }
    };
    ($x:ty: $y:tt, $($yy:tt),+) => {
        impl_float!($x: $y);
        impl_float!($x: $($yy),+);
    };
}

// Assumption: usize < 128-bit
impl_float!(f32: i8, i16, i32, i64, i128, isize);
impl_float!(f32: u8, u16, u32, u64, usize);
impl_float!(f64: i8, i16, i32, i64, i128, isize);
impl_float!(f64: u8, u16, u32, u64, u128, usize);

impl ConvFloat<f32> for u128 {
    #[inline]
    fn conv_nearest(x: f32) -> u128 {
        let x = x.round();
        // Note: f32::MAX < u128::MAX
        #[cfg(any(debug_assertions, feature = "assert_float"))]
        assert!(x >= 0.0 && x.is_finite());
        x as u128
    }
    #[inline]
    fn conv_floor(x: f32) -> u128 {
        #[cfg(any(debug_assertions, feature = "assert_float"))]
        assert!(x >= 0.0 && x.is_finite());
        x as u128
    }
    #[inline]
    fn conv_ceil(x: f32) -> u128 {
        let x = x.ceil();
        #[cfg(any(debug_assertions, feature = "assert_float"))]
        assert!(x >= 0.0 && x.is_finite());
        x as u128
    }
}

/// Like [`Into`], but for [`Conv`]
pub trait Cast<T> {
    /// Cast from `Self` to `T` (see trait doc)
    fn cast(self) -> T;
}

impl<S, T: Conv<S>> Cast<T> for S {
    fn cast(self) -> T {
        T::conv(self)
    }
}

/// Like [`Into`], but for [`ConvFloat`]
pub trait CastFloat<T> {
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
}

impl<S, T: ConvFloat<S>> CastFloat<T> for S {
    fn cast_nearest(self) -> T {
        T::conv_nearest(self)
    }
    fn cast_floor(self) -> T {
        T::conv_floor(self)
    }
    fn cast_ceil(self) -> T {
        T::conv_ceil(self)
    }
}
