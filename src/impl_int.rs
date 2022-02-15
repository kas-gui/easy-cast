// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License in the LICENSE-APACHE file or at:
//     https://www.apache.org/licenses/LICENSE-2.0

//! Integer impls for Conv.
//!
//! See also `impl_basic` which inherits integer impls from From.

use super::*;
use core::mem::size_of;

macro_rules! impl_via_as_neg_check {
    ($x:ty: $y:ty) => {
        impl Conv<$x> for $y {
            #[inline]
            fn conv(x: $x) -> $y {
                #[cfg(any(debug_assertions, feature = "assert_int"))]
                assert!(
                    x >= 0,
                    "cast x: {} to {}: expected x >= 0, found x = {}",
                    stringify!($x), stringify!($y), x
                );
                x as $y
            }
            #[inline]
            fn try_conv(x: $x) -> Result<Self> {
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
                assert!(
                    x <= core::$y::MAX as $x,
                    "cast x: {} to {}: expected x <= {}, found x = {}",
                    stringify!($x), stringify!($y), core::$y::MAX, x
                );
                x as $y
            }
            #[inline]
            fn try_conv(x: $x) -> Result<Self> {
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
                assert!(
                    core::$y::MIN as $x <= x && x <= core::$y::MAX as $x,
                    "cast x: {} to {}: expected {} <= x <= {}, found x = {}",
                    stringify!($x), stringify!($y), core::$y::MIN, core::$y::MAX, x
                );
                x as $y
            }
            #[inline]
            fn try_conv(x: $x) -> Result<Self> {
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

macro_rules! impl_int_generic {
    ($x:tt: $y:tt) => {
        impl Conv<$x> for $y {
            #[allow(unused_comparisons)]
            #[inline]
            fn conv(x: $x) -> $y {
                let src_is_signed = core::$x::MIN != 0;
                let dst_is_signed = core::$y::MIN != 0;
                if size_of::<$x>() < size_of::<$y>() {
                    if !dst_is_signed {
                        #[cfg(any(debug_assertions, feature = "assert_int"))]
                        assert!(
                            x >= 0,
                            "cast x: {} to {}: expected x >= 0, found x = {}",
                            stringify!($x), stringify!($y), x
                        );
                    }
                } else if size_of::<$x>() == size_of::<$y>() {
                    if dst_is_signed {
                        #[cfg(any(debug_assertions, feature = "assert_int"))]
                        assert!(
                            x <= core::$y::MAX as $x,
                            "cast x: {} to {}: expected x <= {}, found x = {}",
                            stringify!($x), stringify!($y), core::$y::MAX, x
                        );
                    } else if src_is_signed {
                        #[cfg(any(debug_assertions, feature = "assert_int"))]
                        assert!(
                            x >= 0,
                            "cast x: {} to {}: expected x >= 0, found x = {}",
                            stringify!($x), stringify!($y), x
                        );
                    }
                } else {
                    // src size > dst size
                    if src_is_signed {
                        #[cfg(any(debug_assertions, feature = "assert_int"))]
                        assert!(
                            core::$y::MIN as $x <= x && x <= core::$y::MAX as $x,
                            "cast x: {} to {}: expected {} <= x <= {}, found x = {}",
                            stringify!($x), stringify!($y), core::$y::MIN, core::$y::MAX, x
                        );
                    } else {
                        #[cfg(any(debug_assertions, feature = "assert_int"))]
                        assert!(
                            x <= core::$y::MAX as $x,
                            "cast x: {} to {}: expected x <= {}, found x = {}",
                            stringify!($x), stringify!($y), core::$y::MAX, x
                        );
                    }
                }
                x as $y
            }
            #[allow(unused_comparisons)]
            #[inline]
            fn try_conv(x: $x) -> Result<Self> {
                let src_is_signed = core::$x::MIN != 0;
                let dst_is_signed = core::$y::MIN != 0;
                if size_of::<$x>() < size_of::<$y>() {
                    if dst_is_signed || x >= 0 {
                        return Ok(x as $y);
                    }
                } else if size_of::<$x>() == size_of::<$y>() {
                    if dst_is_signed {
                        if x <= core::$y::MAX as $x {
                            return Ok(x as $y);
                        }
                    } else if src_is_signed {
                        if x >= 0 {
                            return Ok(x as $y);
                        }
                    } else {
                        // types are identical (e.g. usize == u64)
                        return Ok(x as $y);
                    }
                } else {
                    // src size > dst size
                    if src_is_signed {
                        if core::$y::MIN as $x <= x && x <= core::$y::MAX as $x {
                            return Ok(x as $y);
                        }
                    } else {
                        if x <= core::$y::MAX as $x {
                            return Ok(x as $y);
                        }
                    }
                }
                Err(Error::Range)
            }
        }
    };
    ($x:tt: $y:tt, $($yy:tt),+) => {
        impl_int_generic!($x: $y);
        impl_int_generic!($x: $($yy),+);
    };
}

impl_int_generic!(i8: isize, usize);
impl_int_generic!(i16: isize, usize);
impl_int_generic!(i32: isize, usize);
impl_int_generic!(i64: isize, usize);
impl_int_generic!(i128: isize, usize);
impl_int_generic!(u8: isize, usize);
impl_int_generic!(u16: isize, usize);
impl_int_generic!(u32: isize, usize);
impl_int_generic!(u64: isize, usize);
impl_int_generic!(u128: isize, usize);
impl_int_generic!(isize: i8, i16, i32, i64, i128);
impl_int_generic!(usize: i8, i16, i32, i64, i128, isize);
impl_int_generic!(isize: u8, u16, u32, u64, u128, usize);
impl_int_generic!(usize: u8, u16, u32, u64, u128);

macro_rules! impl_via_digits_check {
    ($x:ty: $y:tt) => {
        impl Conv<$x> for $y {
            #[inline]
            fn conv(x: $x) -> Self {
                if cfg!(any(debug_assertions, feature = "assert_digits")) {
                    Self::try_conv(x).unwrap_or_else(|_| {
                        panic!(
                            "cast x: {} to {}: inexact for x = {}",
                            stringify!($x), stringify!($y), x
                        )
                    })
                } else {
                    x as $y
                }
            }
            #[inline]
            fn try_conv(x: $x) -> Result<Self> {
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

macro_rules! impl_via_digits_check_signed {
    ($x:ty: $y:tt) => {
        impl Conv<$x> for $y {
            #[inline]
            fn conv(x: $x) -> Self {
                if cfg!(any(debug_assertions, feature = "assert_digits")) {
                    Self::try_conv(x).unwrap_or_else(|_| {
                        panic!(
                            "cast x: {} to {}: inexact for x = {}",
                            stringify!($x), stringify!($y), x
                        )
                    })
                } else {
                    x as $y
                }
            }
            #[inline]
            fn try_conv(x: $x) -> Result<Self> {
                let src_ty_bits = (size_of::<$x>() * 8) as u32;
                let src_digits = x.checked_abs()
                    .map(|y| src_ty_bits.saturating_sub(y.leading_zeros() + y.trailing_zeros()))
                    .unwrap_or(1 /*MIN has one binary digit in float repr*/);
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
        impl_via_digits_check_signed!($x: $y);
        impl_via_digits_check_signed!($x: $($yy),+);
    };
}

impl_via_digits_check!(u32: f32);
impl_via_digits_check!(u64: f32, f64);
impl_via_digits_check!(u128: f32, f64);
impl_via_digits_check!(usize: f32, f64);

impl_via_digits_check_signed!(i32: f32);
impl_via_digits_check_signed!(i64: f32, f64);
impl_via_digits_check_signed!(i128: f32, f64);
impl_via_digits_check_signed!(isize: f32, f64);
