// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License in the LICENSE-APACHE file or at:
//     https://www.apache.org/licenses/LICENSE-2.0

//! Floating-point impls

use crate::{Approx, ConvExact, ConvTo, Error, Exact, RangeError, Trunc};
#[cfg(any(feature = "std", feature = "libm"))]
use crate::{Ceil, Floor, Nearest};

impl ConvExact<f32> for f64 {
    type Error = RangeError;

    fn try_conv_exact(x: f32) -> Result<Self, RangeError> {
        match x.is_nan() {
            false => Ok(x as f64),
            true => Err(RangeError),
        }
    }

    #[inline]
    fn conv_exact(x: f32) -> f64 {
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

impl ConvTo<f64, Approx> for f32 {
    type Error = RangeError;

    fn try_conv_to(_: Approx, x: f64) -> Result<f32, Self::Error> {
        match x.is_nan() {
            false => Ok(x as f32),
            true => Err(RangeError),
        }
    }

    #[inline]
    fn conv_to(_: Approx, x: f64) -> f32 {
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

impl ConvTo<f64, Exact> for f32 {
    type Error = Error;

    fn try_conv_to(_: Exact, x: f64) -> Result<f32, Self::Error> {
        match x.is_nan() {
            false => {
                let y = x as f32;
                if <f64 as ConvExact<f32>>::try_conv_exact(y) == Ok(x) {
                    Ok(y)
                } else {
                    Err(Error::Inexact)
                }
            }
            true => Err(Error::Range),
        }
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

macro_rules! impl_float {
    ($x:ty: $y:tt) => {
        impl ConvTo<$x, Trunc> for $y {
            type Error = RangeError;

            #[inline]
            fn try_conv_to(_: Trunc, x: $x) -> Result<Self, RangeError> {
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
            fn conv_to(_: Trunc, x: $x) -> Self {
                if cfg!(any(debug_assertions, feature = "assert_float")) {
                    <$y>::try_conv_to(Trunc, x).unwrap_or_else(|_| {
                        panic!(
                            "cast x: {} to {} (trunc): range error for x = {}",
                            stringify!($x), stringify!($y), x
                        )
                    })
                } else {
                    x as $y
                }
            }
        }

        #[cfg(any(feature = "std", feature = "libm"))]
        impl ConvTo<$x, Nearest> for $y {
            type Error = RangeError;

            #[inline]
            fn try_conv_to(_: Nearest, x: $x) -> Result<Self, RangeError> {
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
            fn conv_to(_: Nearest, x: $x) -> Self {
                if cfg!(any(debug_assertions, feature = "assert_float")) {
                    <$y>::try_conv_to(Nearest, x).unwrap_or_else(|_| {
                        panic!(
                            "cast x: {} to {} (nearest): range error for x = {}",
                            stringify!($x), stringify!($y), x
                        )
                    })
                } else {
                    x.round() as $y
                }
            }
        }

        #[cfg(any(feature = "std", feature = "libm"))]
        impl ConvTo<$x, Floor> for $y {
            type Error = RangeError;

            #[inline]
            fn try_conv_to(_: Floor, x: $x) -> Result<Self, RangeError> {
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
            fn conv_to(_: Floor, x: $x) -> Self {
                if cfg!(any(debug_assertions, feature = "assert_float")) {
                    <$y>::try_conv_to(Floor, x).unwrap_or_else(|_| {
                        panic!(
                            "cast x: {} to {} (floor): range error for x = {}",
                            stringify!($x), stringify!($y), x
                        )
                    })
                } else {
                    x.floor() as $y
                }
            }
        }

        #[cfg(any(feature = "std", feature = "libm"))]
        impl ConvTo<$x, Ceil> for $y {
            type Error = RangeError;

            #[inline]
            fn try_conv_to(_: Ceil, x: $x) -> Result<Self, RangeError> {
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

            #[inline]
            fn conv_to(_: Ceil, x: $x) -> Self {
                if cfg!(any(debug_assertions, feature = "assert_float")) {
                    <$y>::try_conv_to(Ceil, x).unwrap_or_else(|_| {
                        panic!(
                            "cast x: {} to {} (ceil): range error for x = {}",
                            stringify!($x), stringify!($y), x
                        )
                    })
                } else {
                    x.ceil() as $y
                }
            }
        }

        impl ConvTo<$x, Approx> for $y {
            type Error = RangeError;

            #[inline]
            fn try_conv_to(_: Approx, x: $x) -> Result<Self, Self::Error> {
                Self::try_conv_to(Trunc, x)
            }
            #[inline]
            fn conv_to(_: Approx, x: $x) -> Self {
                Self::conv_to(Trunc, x)
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

impl ConvTo<f32, Trunc> for u128 {
    type Error = RangeError;

    #[inline]
    fn try_conv_to(_: Trunc, x: f32) -> Result<Self, RangeError> {
        // Note: f32::MAX < u128::MAX
        if x >= 0.0 && x.is_finite() {
            Ok(x as u128)
        } else {
            Err(RangeError)
        }
    }

    #[inline]
    fn conv_to(_: Trunc, x: f32) -> u128 {
        if cfg!(any(debug_assertions, feature = "assert_float")) {
            <u128>::try_conv_to(Trunc, x).unwrap_or_else(|_| {
                panic!(
                    "cast x: f32 to u128 (trunc/floor): range error for x = {}",
                    x
                )
            })
        } else {
            x as u128
        }
    }
}

#[cfg(any(feature = "std", feature = "libm"))]
impl ConvTo<f32, Nearest> for u128 {
    type Error = RangeError;

    #[inline]
    fn try_conv_to(_: Nearest, x: f32) -> Result<Self, RangeError> {
        let x = x.round();
        if x >= 0.0 && x.is_finite() {
            Ok(x as u128)
        } else {
            Err(RangeError)
        }
    }

    #[inline]
    fn conv_to(_: Nearest, x: f32) -> u128 {
        if cfg!(any(debug_assertions, feature = "assert_float")) {
            <u128>::try_conv_to(Nearest, x).unwrap_or_else(|_| {
                panic!("cast x: f32 to u128 (nearest): range error for x = {}", x)
            })
        } else {
            x.round() as u128
        }
    }
}

#[cfg(any(feature = "std", feature = "libm"))]
impl ConvTo<f32, Floor> for u128 {
    type Error = RangeError;

    #[inline]
    fn try_conv_to(_: Floor, x: f32) -> Result<Self, RangeError> {
        Self::try_conv_to(Trunc, x)
    }

    #[inline]
    fn conv_to(_: Floor, x: f32) -> u128 {
        Self::conv_to(Trunc, x)
    }
}

#[cfg(any(feature = "std", feature = "libm"))]
impl ConvTo<f32, Ceil> for u128 {
    type Error = RangeError;

    #[inline]
    fn try_conv_to(_: Ceil, x: f32) -> Result<Self, RangeError> {
        let x = x.ceil();
        if x >= 0.0 && x.is_finite() {
            Ok(x as u128)
        } else {
            Err(RangeError)
        }
    }

    #[inline]
    fn conv_to(_: Ceil, x: f32) -> u128 {
        if cfg!(any(debug_assertions, feature = "assert_float")) {
            u128::try_conv_to(Ceil, x)
                .unwrap_or_else(|_| panic!("cast x: f32 to u128 (ceil): range error for x = {}", x))
        } else {
            x.ceil() as u128
        }
    }
}

impl ConvTo<f32, Approx> for u128 {
    type Error = RangeError;

    #[inline]
    fn try_conv_to(_: Approx, x: f32) -> Result<Self, Self::Error> {
        Self::try_conv_to(Trunc, x)
    }
    #[inline]
    fn conv_to(_: Approx, x: f32) -> Self {
        Self::conv_to(Trunc, x)
    }
}
