// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License in the LICENSE-APACHE file or at:
//     https://www.apache.org/licenses/LICENSE-2.0

//! Floating-point impls

use crate::RangeError;
use crate::generic::{Approx, Convert, ConvertExact};
#[cfg(any(feature = "std", feature = "libm"))]
use crate::{ConvFloat, Error};

impl ConvertExact<f32> for f64 {
    type Error = RangeError;

    fn try_convert(x: f32) -> Result<Self, RangeError> {
        match x.is_nan() {
            false => Ok(x as f64),
            true => Err(RangeError),
        }
    }

    #[inline]
    fn convert(x: f32) -> f64 {
        fn trap_nan(x: f32) {
            if x.is_nan() {
                panic!("cast float-to-float: NaN")
            }
        }

        if cfg!(any(debug_assertions, feature = "assert_float")) {
            trap_nan(x)
        }

        x as f64
    }
}

#[allow(clippy::manual_range_contains)]
impl Convert<f64, Approx> for f32 {
    type Error = RangeError;

    fn try_convert(x: f64) -> Result<f32, Self::Error> {
        match x.is_nan() {
            false => Ok(x as f32),
            true => Err(RangeError),
        }
    }

    #[inline]
    fn convert(x: f64) -> f32 {
        fn trap_nan(x: f64) {
            if x.is_nan() {
                panic!("cast float-to-float: NaN")
            }
        }

        if cfg!(any(debug_assertions, feature = "assert_float")) {
            trap_nan(x)
        }

        x as f32
    }
}

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

#[cfg(any(feature = "std", feature = "libm"))]
macro_rules! impl_float {
    ($x:ty: $y:tt) => {
        impl ConvFloat<$x> for $y {
            #[inline]
            fn conv_trunc(x: $x) -> $y {
                if cfg!(any(debug_assertions, feature = "assert_float")) {
                    Self::try_conv_trunc(x).unwrap_or_else(|_| {
                        panic!(
                            "cast x: {} to {} (trunc): range error for x = {}",
                            stringify!($x), stringify!($y), x
                        )
                    })
                } else {
                    x as $y
                }
            }
            #[inline]
            fn conv_nearest(x: $x) -> $y {
                if cfg!(any(debug_assertions, feature = "assert_float")) {
                    Self::try_conv_nearest(x).unwrap_or_else(|_| {
                        panic!(
                            "cast x: {} to {} (nearest): range error for x = {}",
                            stringify!($x), stringify!($y), x
                        )
                    })
                } else {
                    x.round() as $y
                }
            }
            #[inline]
            fn conv_floor(x: $x) -> $y {
                if cfg!(any(debug_assertions, feature = "assert_float")) {
                    Self::try_conv_floor(x).unwrap_or_else(|_| {
                        panic!(
                            "cast x: {} to {} (floor): range error for x = {}",
                            stringify!($x), stringify!($y), x
                        )
                    })
                } else {
                    x.floor() as $y
                }
            }
            #[inline]
            fn conv_ceil(x: $x) -> $y {
                if cfg!(any(debug_assertions, feature = "assert_float")) {
                    Self::try_conv_ceil(x).unwrap_or_else(|_| {
                        panic!(
                            "cast x: {} to {} (ceil): range error for x = {}",
                            stringify!($x), stringify!($y), x
                        )
                    })
                } else {
                    x.ceil() as $y
                }
            }

            #[inline]
            fn try_conv_trunc(x: $x) -> Result<Self, RangeError> {
                // Tested: these limits work for $x=f32 and all $y except u128
                const LBOUND: $x = $y::MIN as $x - 1.0;
                const UBOUND: $x = $y::MAX as $x + 1.0;
                if x > LBOUND && x < UBOUND {
                    Ok(x as $y)
                } else {
                    Err(RangeError)
                }
            }
            #[inline]
            fn try_conv_nearest(x: $x) -> Result<Self, RangeError> {
                // Tested: these limits work for $x=f32 and all $y except u128
                const LBOUND: $x = $y::MIN as $x;
                const UBOUND: $x = $y::MAX as $x + 1.0;
                let x = x.round();
                if (LBOUND..UBOUND).contains(&x) {
                    Ok(x as $y)
                } else {
                    Err(RangeError)
                }
            }
            #[inline]
            fn try_conv_floor(x: $x) -> Result<Self, RangeError> {
                // Tested: these limits work for $x=f32 and all $y except u128
                const LBOUND: $x = $y::MIN as $x;
                const UBOUND: $x = $y::MAX as $x + 1.0;
                let x = x.floor();
                if (LBOUND..UBOUND).contains(&x) {
                    Ok(x as $y)
                } else {
                    Err(RangeError)
                }
            }
            #[inline]
            fn try_conv_ceil(x: $x) -> Result<Self, RangeError> {
                // Tested: these limits work for $x=f32 and all $y except u128
                const LBOUND: $x = $y::MIN as $x;
                const UBOUND: $x = $y::MAX as $x + 1.0;
                let x = x.ceil();
                if (LBOUND..UBOUND).contains(&x) {
                    Ok(x as $y)
                } else {
                    Err(RangeError)
                }
            }
        }

        impl Convert<$x, Approx> for $y {
            type Error = Error;

            #[inline]
            fn try_convert(x: $x) -> Result<Self, Self::Error> {
                ConvFloat::<$x>::try_conv_trunc(x).map_err(Into::into)
            }
            #[inline]
            fn convert(x: $x) -> Self {
                ConvFloat::<$x>::conv_trunc(x)
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
            Self::try_conv_trunc(x).unwrap_or_else(|_| {
                panic!(
                    "cast x: f32 to u128 (trunc/floor): range error for x = {}",
                    x
                )
            })
        } else {
            x as u128
        }
    }
    #[inline]
    fn conv_nearest(x: f32) -> u128 {
        if cfg!(any(debug_assertions, feature = "assert_float")) {
            Self::try_conv_nearest(x).unwrap_or_else(|_| {
                panic!("cast x: f32 to u128 (nearest): range error for x = {}", x)
            })
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
            Self::try_conv_ceil(x)
                .unwrap_or_else(|_| panic!("cast x: f32 to u128 (ceil): range error for x = {}", x))
        } else {
            x.ceil() as u128
        }
    }

    #[inline]
    fn try_conv_trunc(x: f32) -> Result<Self, RangeError> {
        // Note: f32::MAX < u128::MAX
        if x >= 0.0 && x.is_finite() {
            Ok(x as u128)
        } else {
            Err(RangeError)
        }
    }
    #[inline]
    fn try_conv_nearest(x: f32) -> Result<Self, RangeError> {
        let x = x.round();
        if x >= 0.0 && x.is_finite() {
            Ok(x as u128)
        } else {
            Err(RangeError)
        }
    }
    #[inline]
    fn try_conv_floor(x: f32) -> Result<Self, RangeError> {
        Self::try_conv_trunc(x)
    }
    #[inline]
    fn try_conv_ceil(x: f32) -> Result<Self, RangeError> {
        let x = x.ceil();
        if x >= 0.0 && x.is_finite() {
            Ok(x as u128)
        } else {
            Err(RangeError)
        }
    }
}

#[cfg(any(feature = "std", feature = "libm"))]
impl Convert<f32, Approx> for u128 {
    type Error = Error;

    #[inline]
    fn try_convert(x: f32) -> Result<Self, Self::Error> {
        ConvFloat::<f32>::try_conv_trunc(x).map_err(Into::into)
    }
    #[inline]
    fn convert(x: f32) -> Self {
        ConvFloat::<f32>::conv_trunc(x)
    }
}
