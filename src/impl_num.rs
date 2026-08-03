// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License in the LICENSE-APACHE file or at:
//     https://www.apache.org/licenses/LICENSE-2.0

//! `core::num` impls.

use crate::{ConvExact, RangeError, impl_via_identity};
use core::num::NonZero;

macro_rules! impl_identity {
    ($($x:tt),*) => {
        $(
            impl_via_identity!(NonZero<$x>);
        )*
    };
}

impl_identity!(u8, u16, u32, u64, u128, usize);
impl_identity!(i8, i16, i32, i64, i128, isize);

macro_rules! impl_nonzero {
    ($x:ty : $y:ty) => {
        impl ConvExact<NonZero<$x>> for NonZero<$y> {
            type Error = RangeError;

            #[inline]
            fn try_conv_exact(n: NonZero<$x>) -> Result<NonZero<$y>, Self::Error> {
                let m: $y = <$y>::try_conv_exact(n.get())?;
                // An error here should be impossible, but handling one is basically free:
                NonZero::new(m).ok_or(RangeError)
            }

            // We do not implement conv since its main purpose is to allow
            // bypassing checks, but since this would allow wrapping-to-zero
            // we cannot omit all checks.
        }
    };
    ($x:ty : $y:ty, $($yy:ty),+) => {
        impl_nonzero!($x: $y);
        impl_nonzero!($x: $($yy),+);
    };
}

// From impl_basic:
// NOTE: these impls should be Infallible but this would require unsafe code
impl_nonzero!(i8: i16, i32, i64, i128, isize);
impl_nonzero!(i16: i32, i64, i128, isize);
impl_nonzero!(i32: i64, i128);
impl_nonzero!(i64: i128);
impl_nonzero!(u8: i16, i32, i64, i128, isize);
impl_nonzero!(u8: u16, u32, u64, u128, usize);
impl_nonzero!(u16: i32, i64, i128, u32, u64, u128, usize);
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

impl_nonzero!(i8: usize);
impl_nonzero!(i16: usize);
impl_nonzero!(i32: isize, usize);
impl_nonzero!(i64: isize, usize);
impl_nonzero!(i128: isize, usize);
impl_nonzero!(u16: isize);
impl_nonzero!(u32: isize, usize);
impl_nonzero!(u64: isize, usize);
impl_nonzero!(u128: isize, usize);
impl_nonzero!(isize: i8, i16, i32, i64, i128);
impl_nonzero!(usize: i8, i16, i32, i64, i128, isize);
impl_nonzero!(isize: u8, u16, u32, u64, u128, usize);
impl_nonzero!(usize: u8, u16, u32, u64, u128);
