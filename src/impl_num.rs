// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License in the LICENSE-APACHE file or at:
//     https://www.apache.org/licenses/LICENSE-2.0

//! `core::num` impls for Conv.

use super::*;
use core::num::NonZero;

macro_rules! impl_via_trivial {
    ($x:ty) => {
        impl Conv<NonZero<$x>> for NonZero<$x> {
            #[inline]
            fn conv(x: NonZero<$x>) -> Self {
                x
            }
            #[inline]
            fn try_conv(x: NonZero<$x>) -> Result<Self> {
                Ok(x)
            }
        }
    };
    ($x:ty $(, $xx:tt)* $(,)?) => {
        impl_via_trivial!($x);
        impl_via_trivial!($($xx),*);
    };
}

#[rustfmt::skip]
impl_via_trivial!(
    u8, u16, u32, u64, u128, usize,
    i8, i16, i32, i64, i128, isize,
);

macro_rules! impl_nonzero {
    ($x:ty: $y:ty) => {
        impl Conv<NonZero<$x>> for NonZero<$y> {
            #[inline]
            fn try_conv(n: NonZero<$x>) -> Result<NonZero<$y>> {
                let m: $y = n.get().try_cast()?;
                Ok(if cfg!(any(debug_assertions, feature = "assert_nonzero")) {
                    NonZero::new(m).expect("should be non-zero")
                } else {
                    // SAFETY: since cast() does not change the numeric value, m cannot be zero
                    unsafe { NonZero::new_unchecked(m) }
                })
            }

            #[inline]
            fn conv(n: NonZero<$x>) -> NonZero<$y> {
                let m: $y = n.get().cast();
                if cfg!(any(debug_assertions, feature = "assert_nonzero")) {
                    NonZero::new(m).expect("should be non-zero")
                } else {
                    // SAFETY: since cast() does not change the numeric value, m cannot be zero
                    unsafe { NonZero::new_unchecked(m) }
                }
            }
        }
    };
    ($x:ty: $y:ty, $($yy:ty),+) => {
        impl_nonzero!($x: $y);
        impl_nonzero!($x: $($yy),+);
    };
}

// From impl_basic:
impl_nonzero!(i8: i16, i32, i64, i128);
impl_nonzero!(i16: i32, i64, i128);
impl_nonzero!(i32: i64, i128);
impl_nonzero!(i64: i128);
impl_nonzero!(u8: i16, i32, i64, i128);
impl_nonzero!(u8: u16, u32, u64, u128);
impl_nonzero!(u16: i32, i64, i128, u32, u64, u128);
impl_nonzero!(u32: i64, i128, u64, u128);
impl_nonzero!(u64: i128, u128);

// From impl_int:
impl_nonzero!(i8: u8, u16, u32, u64, u128);
impl_nonzero!(i16: u16, u32, u64, u128);
impl_nonzero!(i32: u32, u64, u128);
impl_nonzero!(i64: u64, u128);
impl_nonzero!(i128: u128);

impl_nonzero!(u8: i8);
impl_nonzero!(u16: i8, i16, u8);
impl_nonzero!(u32: i8, i16, i32, u8, u16);
impl_nonzero!(u64: i8, i16, i32, i64, u8, u16, u32);
impl_nonzero!(u128: i8, i16, i32, i64, i128);
impl_nonzero!(u128: u8, u16, u32, u64);

impl_nonzero!(i16: i8, u8);
impl_nonzero!(i32: i8, i16, u8, u16);
impl_nonzero!(i64: i8, i16, i32, u8, u16, u32);
impl_nonzero!(i128: i8, i16, i32, i64, u8, u16, u32, u64);

impl_nonzero!(i8: isize, usize);
impl_nonzero!(i16: isize, usize);
impl_nonzero!(i32: isize, usize);
impl_nonzero!(i64: isize, usize);
impl_nonzero!(i128: isize, usize);
impl_nonzero!(u8: isize, usize);
impl_nonzero!(u16: isize, usize);
impl_nonzero!(u32: isize, usize);
impl_nonzero!(u64: isize, usize);
impl_nonzero!(u128: isize, usize);
impl_nonzero!(isize: i8, i16, i32, i64, i128);
impl_nonzero!(usize: i8, i16, i32, i64, i128, isize);
impl_nonzero!(isize: u8, u16, u32, u64, u128, usize);
impl_nonzero!(usize: u8, u16, u32, u64, u128);
