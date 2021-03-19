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
//! debug builds. In release builds assertions are omitted, except where the
//! source type is floating-point. It is thus possible that incorrect values may
//! be produced.

use std::mem::size_of;

// Borrowed from static_assertions:
macro_rules! const_assert {
    ($x:expr $(,)?) => {
        #[allow(unknown_lints, eq_op)]
        const _: [(); 0 - !{
            const ASSERT: bool = $x;
            ASSERT
        } as usize] = [];
    };
}

const_assert!(size_of::<isize>() >= size_of::<i32>());
const_assert!(size_of::<isize>() <= size_of::<i64>());
const_assert!(size_of::<usize>() == size_of::<isize>());

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
impl_via_from!(i8: f32, f64, i16, i32, i64, i128, isize);
impl_via_from!(i16: f32, f64, i32, i64, i128, isize);
impl_via_from!(i32: f64, i64, i128);
impl_via_from!(i64: i128);
impl_via_from!(u8: f32, f64, i16, i32, i64, i128, isize);
impl_via_from!(u8: u16, u32, u64, u128, usize);
impl_via_from!(u16: f32, f64, i32, i64, i128, u32, u64, u128, usize);
impl_via_from!(u32: f64, i64, i128, u64, u128);
impl_via_from!(u64: i128, u128);

// These rely on the const assertions above
macro_rules! impl_via_as {
    ($x:ty: $y:ty) => {
        impl Conv<$x> for $y {
            #[inline]
            fn conv(x: $x) -> $y {
                x as $y
            }
        }
    };
    ($x:ty: $y:ty, $($yy:ty),+) => {
        impl_via_as!($x: $y);
        impl_via_as!($x: $($yy),+);
    };
}

impl_via_as!(i32: isize);
impl_via_as!(isize: i64, i128);
impl_via_as!(u16: isize);
impl_via_as!(u32: usize);
impl_via_as!(usize: i128, u64, u128);

macro_rules! impl_via_as_neg_check {
    ($x:ty: $y:ty) => {
        impl Conv<$x> for $y {
            #[inline]
            fn conv(x: $x) -> $y {
                debug_assert!(x >= 0);
                x as $y
            }
        }
    };
    ($x:ty: $y:ty, $($yy:ty),+) => {
        impl_via_as_neg_check!($x: $y);
        impl_via_as_neg_check!($x: $($yy),+);
    };
}

impl_via_as_neg_check!(i8: u8, u16, u32, u64, u128, usize);
impl_via_as_neg_check!(i16: u16, u32, u64, u128, usize);
impl_via_as_neg_check!(i32: u32, u64, u128, usize);
impl_via_as_neg_check!(i64: u64, u128);
impl_via_as_neg_check!(i128: u128);
impl_via_as_neg_check!(isize: u64, u128, usize);

// Assumption: $y::MAX is representable as $x
macro_rules! impl_via_as_max_check {
    ($x:ty: $y:ty) => {
        impl Conv<$x> for $y {
            #[inline]
            fn conv(x: $x) -> $y {
                debug_assert!(x <= <$y>::MAX as $x);
                x as $y
            }
        }
    };
    ($x:ty: $y:ty, $($yy:ty),+) => {
        impl_via_as_max_check!($x: $y);
        impl_via_as_max_check!($x: $($yy),+);
    };
}

impl_via_as_max_check!(u8: i8);
impl_via_as_max_check!(u16: i8, i16, u8);
impl_via_as_max_check!(u32: i8, i16, i32, u8, u16);
impl_via_as_max_check!(u64: i8, i16, i32, i64, isize, u8, u16, u32, usize);
impl_via_as_max_check!(u128: i8, i16, i32, i64, i128, isize);
impl_via_as_max_check!(u128: u8, u16, u32, u64, usize);
impl_via_as_max_check!(usize: i8, i16, i32, isize, u8, u16, u32);

// Assumption: $y::MAX and $y::MIN are representable as $x
macro_rules! impl_via_as_range_check {
    ($x:ty: $y:ty) => {
        impl Conv<$x> for $y {
            #[inline]
            fn conv(x: $x) -> $y {
                debug_assert!(<$y>::MIN as $x <= x && x <= <$y>::MAX as $x);
                x as $y
            }
        }
    };
    ($x:ty: $y:ty, $($yy:ty),+) => {
        impl_via_as_range_check!($x: $y);
        impl_via_as_range_check!($x: $($yy),+);
    };
}

impl_via_as_range_check!(i16: i8, u8);
impl_via_as_range_check!(i32: i8, i16, u8, u16);
impl_via_as_range_check!(i64: i8, i16, i32, isize, u8, u16, u32);
impl_via_as_range_check!(i128: i8, i16, i32, i64, isize, u8, u16, u32, u64, usize);
impl_via_as_range_check!(isize: i8, i16, i32, u8, u16);

macro_rules! impl_via_as_revert_check {
    ($x:ty: $y:ty) => {
        impl Conv<$x> for $y {
            #[inline]
            fn conv(x: $x) -> $y {
                let y = x as $y;
                debug_assert_eq!(x, y as $x);
                y
            }
        }
    };
}

impl_via_as_revert_check!(u32: isize);
impl_via_as_revert_check!(i64: usize);
impl_via_as_revert_check!(isize: u32);
impl_via_as_revert_check!(usize: i64);
impl_via_as_revert_check!(f64: f32);

macro_rules! impl_via_digits_check {
    ($x:ty: $y:ty) => {
        impl Conv<$x> for $y {
            #[inline]
            fn conv(x: $x) -> $y {
                let src_ty_bits = u32::conv(std::mem::size_of::<$x>() * 8);
                let src_digits = src_ty_bits - (x.leading_zeros() + x.trailing_zeros());
                let dst_digits = <$y>::MANTISSA_DIGITS;
                dbg!(src_ty_bits, src_digits, dst_digits);
                assert!(src_digits <= dst_digits);
                x as $y
            }
        }
    };
    ($x:ty: $y:ty, $($yy:ty),+) => {
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
    ($x:ty: $y:ty) => {
        impl ConvFloat<$x> for $y {
            #[inline]
            fn conv_nearest(x: $x) -> $y {
                let x = x.round();
                // Tested: these limits work for $x=f32 and all $y except u128
                const LBOUND: $x = <$y>::MIN as $x;
                const UBOUND: $x = <$y>::MAX as $x + 1.0;
                assert!(x >= LBOUND && x < UBOUND);
                x as $y
            }
            #[inline]
            fn conv_floor(x: $x) -> $y {
                const LBOUND: $x = <$y>::MIN as $x;
                const UBOUND: $x = <$y>::MAX as $x + 1.0;
                assert!(x >= LBOUND && x < UBOUND);
                x as $y
            }
            #[inline]
            fn conv_ceil(x: $x) -> $y {
                let x = x.ceil();
                const LBOUND: $x = <$y>::MIN as $x;
                const UBOUND: $x = <$y>::MAX as $x + 1.0;
                assert!(x >= LBOUND && x < UBOUND);
                x as $y
            }
        }
    };
    ($x:ty: $y:ty, $($yy:ty),+) => {
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
        assert!(x >= 0.0 && x.is_finite());
        x as u128
    }
    #[inline]
    fn conv_floor(x: f32) -> u128 {
        assert!(x >= 0.0 && x.is_finite());
        x as u128
    }
    #[inline]
    fn conv_ceil(x: f32) -> u128 {
        let x = x.ceil();
        assert!(x >= 0.0 && x.is_finite());
        x as u128
    }
}

/// Like [`Into`], but for [`Conv`]
pub trait Cast<T> {
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
