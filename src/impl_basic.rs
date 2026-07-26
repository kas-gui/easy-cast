// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License in the LICENSE-APACHE file or at:
//     https://www.apache.org/licenses/LICENSE-2.0

//! Basic impls

use crate::generic::{Convert, Rounding};
#[cfg(any(feature = "std", feature = "libm"))]
use crate::{ConvFloat, RangeError};
use core::convert::Infallible;

/// Implement [`ConvertExact`] infallibly over a [`From`] implementation
///
/// # Example
///
/// ```
/// struct MyInt(i32);
///
/// impl From<MyInt> for i32 {
///     fn from(x: MyInt) -> i32 {
///         x.0
///     }
/// }
///
/// impl From<MyInt> for i64 {
///     fn from(x: MyInt) -> i64 {
///         x.0.into()
///     }
/// }
///
/// easy_cast::impl_via_from!(MyInt: i32, i64);
/// ```
///
/// [`ConvertExact`]: crate::generic::ConvertExact
#[macro_export]
macro_rules! impl_via_from {
    ($x:ty: $y:ty) => {
        impl $crate::generic::ConvertExact<$x> for $y {
            type Error = ::core::convert::Infallible;

            #[inline]
            fn convert(x: $x) -> $y {
                <$y>::from(x)
            }
            #[inline]
            fn try_convert(x: $x) -> Result<Self, Self::Error> {
                Ok(<$y>::from(x))
            }
        }
    };
    ($x:ty: $y:ty, $($yy:ty),+) => {
        $crate::impl_via_from!($x: $y);
        $crate::impl_via_from!($x: $($yy),+);
    };
}

impl_via_from!(i8: f32, f64, i16, i32, i64, i128, isize);
impl_via_from!(i16: f32, f64, i32, i64, i128, isize);
impl_via_from!(i32: f64, i64, i128);
impl_via_from!(i64: i128);
impl_via_from!(u8: f32, f64, i16, i32, i64, i128, isize);
impl_via_from!(u8: u16, u32, u64, u128, usize);
impl_via_from!(u16: f32, f64, i32, i64, i128, u32, u64, u128, usize);
impl_via_from!(u32: f64, i64, i128, u64, u128);
impl_via_from!(u64: i128, u128);

// TODO(unsize): remove T: Copy + Default bound
// TODO(specialization): implement ConvApprox for arrays and tuples
impl<R: Rounding, S, T: Convert<S, R> + Copy + Default, const N: usize> Convert<[S; N], R>
    for [T; N]
{
    type Error = T::Error;

    #[inline]
    fn try_convert(ss: [S; N]) -> Result<Self, Self::Error> {
        let mut tt = [T::default(); N];
        for (s, t) in IntoIterator::into_iter(ss).zip(tt.iter_mut()) {
            *t = T::try_convert(s)?;
        }
        Ok(tt)
    }
    #[inline]
    fn convert(ss: [S; N]) -> Self {
        let mut tt = [T::default(); N];
        for (s, t) in IntoIterator::into_iter(ss).zip(tt.iter_mut()) {
            *t = T::convert(s);
        }
        tt
    }
}

#[cfg(any(feature = "std", feature = "libm"))]
impl<S, T: ConvFloat<S> + Copy + Default, const N: usize> ConvFloat<[S; N]> for [T; N] {
    #[inline]
    fn try_conv_trunc(ss: [S; N]) -> Result<Self, RangeError> {
        let mut tt = [T::default(); N];
        for (s, t) in IntoIterator::into_iter(ss).zip(tt.iter_mut()) {
            *t = T::try_conv_trunc(s)?;
        }
        Ok(tt)
    }
    #[inline]
    fn try_conv_nearest(ss: [S; N]) -> Result<Self, RangeError> {
        let mut tt = [T::default(); N];
        for (s, t) in IntoIterator::into_iter(ss).zip(tt.iter_mut()) {
            *t = T::try_conv_nearest(s)?;
        }
        Ok(tt)
    }
    #[inline]
    fn try_conv_floor(ss: [S; N]) -> Result<Self, RangeError> {
        let mut tt = [T::default(); N];
        for (s, t) in IntoIterator::into_iter(ss).zip(tt.iter_mut()) {
            *t = T::try_conv_floor(s)?;
        }
        Ok(tt)
    }
    #[inline]
    fn try_conv_ceil(ss: [S; N]) -> Result<Self, RangeError> {
        let mut tt = [T::default(); N];
        for (s, t) in IntoIterator::into_iter(ss).zip(tt.iter_mut()) {
            *t = T::try_conv_ceil(s)?;
        }
        Ok(tt)
    }

    #[inline]
    fn conv_trunc(ss: [S; N]) -> Self {
        let mut tt = [T::default(); N];
        for (s, t) in IntoIterator::into_iter(ss).zip(tt.iter_mut()) {
            *t = T::conv_trunc(s);
        }
        tt
    }
    #[inline]
    fn conv_nearest(ss: [S; N]) -> Self {
        let mut tt = [T::default(); N];
        for (s, t) in IntoIterator::into_iter(ss).zip(tt.iter_mut()) {
            *t = T::conv_nearest(s);
        }
        tt
    }
    #[inline]
    fn conv_floor(ss: [S; N]) -> Self {
        let mut tt = [T::default(); N];
        for (s, t) in IntoIterator::into_iter(ss).zip(tt.iter_mut()) {
            *t = T::conv_floor(s);
        }
        tt
    }
    #[inline]
    fn conv_ceil(ss: [S; N]) -> Self {
        let mut tt = [T::default(); N];
        for (s, t) in IntoIterator::into_iter(ss).zip(tt.iter_mut()) {
            *t = T::conv_ceil(s);
        }
        tt
    }
}

impl<R: Rounding> Convert<(), R> for () {
    type Error = Infallible;

    #[inline]
    fn try_convert(_: ()) -> Result<Self, Self::Error> {
        Ok(())
    }
    #[inline]
    fn convert(_: ()) -> Self {}
}
impl<R: Rounding, S0, T0: Convert<S0, R>> Convert<(S0,), R> for (T0,) {
    type Error = T0::Error;

    #[inline]
    fn try_convert(ss: (S0,)) -> Result<Self, Self::Error> {
        Ok((T0::try_convert(ss.0)?,))
    }
    #[inline]
    fn convert(ss: (S0,)) -> Self {
        (T0::convert(ss.0),)
    }
}
impl<R: Rounding, S0, S1, T0: Convert<S0, R>, T1: Convert<S1, R>> Convert<(S0, S1), R>
    for (T0, T1)
{
    type Error = R::MaximumError;

    #[inline]
    fn try_convert(ss: (S0, S1)) -> Result<Self, Self::Error> {
        Ok((
            T0::try_convert(ss.0).map_err(Into::into)?,
            T1::try_convert(ss.1).map_err(Into::into)?,
        ))
    }
    #[inline]
    fn convert(ss: (S0, S1)) -> Self {
        (T0::convert(ss.0), T1::convert(ss.1))
    }
}
impl<R: Rounding, S0, S1, S2, T0: Convert<S0, R>, T1: Convert<S1, R>, T2: Convert<S2, R>>
    Convert<(S0, S1, S2), R> for (T0, T1, T2)
{
    type Error = R::MaximumError;

    #[inline]
    fn try_convert(ss: (S0, S1, S2)) -> Result<Self, Self::Error> {
        Ok((
            T0::try_convert(ss.0).map_err(Into::into)?,
            T1::try_convert(ss.1).map_err(Into::into)?,
            T2::try_convert(ss.2).map_err(Into::into)?,
        ))
    }
    #[inline]
    fn convert(ss: (S0, S1, S2)) -> Self {
        (T0::convert(ss.0), T1::convert(ss.1), T2::convert(ss.2))
    }
}
impl<
    R: Rounding,
    S0,
    S1,
    S2,
    S3,
    T0: Convert<S0, R>,
    T1: Convert<S1, R>,
    T2: Convert<S2, R>,
    T3: Convert<S3, R>,
> Convert<(S0, S1, S2, S3), R> for (T0, T1, T2, T3)
{
    type Error = R::MaximumError;

    #[inline]
    fn try_convert(ss: (S0, S1, S2, S3)) -> Result<Self, Self::Error> {
        Ok((
            T0::try_convert(ss.0).map_err(Into::into)?,
            T1::try_convert(ss.1).map_err(Into::into)?,
            T2::try_convert(ss.2).map_err(Into::into)?,
            T3::try_convert(ss.3).map_err(Into::into)?,
        ))
    }
    #[inline]
    fn convert(ss: (S0, S1, S2, S3)) -> Self {
        (
            T0::convert(ss.0),
            T1::convert(ss.1),
            T2::convert(ss.2),
            T3::convert(ss.3),
        )
    }
}
impl<
    R: Rounding,
    S0,
    S1,
    S2,
    S3,
    S4,
    T0: Convert<S0, R>,
    T1: Convert<S1, R>,
    T2: Convert<S2, R>,
    T3: Convert<S3, R>,
    T4: Convert<S4, R>,
> Convert<(S0, S1, S2, S3, S4), R> for (T0, T1, T2, T3, T4)
{
    type Error = R::MaximumError;

    #[inline]
    fn try_convert(ss: (S0, S1, S2, S3, S4)) -> Result<Self, Self::Error> {
        Ok((
            T0::try_convert(ss.0).map_err(Into::into)?,
            T1::try_convert(ss.1).map_err(Into::into)?,
            T2::try_convert(ss.2).map_err(Into::into)?,
            T3::try_convert(ss.3).map_err(Into::into)?,
            T4::try_convert(ss.4).map_err(Into::into)?,
        ))
    }
    #[inline]
    fn convert(ss: (S0, S1, S2, S3, S4)) -> Self {
        (
            T0::convert(ss.0),
            T1::convert(ss.1),
            T2::convert(ss.2),
            T3::convert(ss.3),
            T4::convert(ss.4),
        )
    }
}
impl<R: Rounding, S0, S1, S2, S3, S4, S5, T0, T1, T2, T3, T4, T5>
    Convert<(S0, S1, S2, S3, S4, S5), R> for (T0, T1, T2, T3, T4, T5)
where
    T0: Convert<S0, R>,
    T1: Convert<S1, R>,
    T2: Convert<S2, R>,
    T3: Convert<S3, R>,
    T4: Convert<S4, R>,
    T5: Convert<S5, R>,
{
    type Error = R::MaximumError;

    #[inline]
    fn try_convert(ss: (S0, S1, S2, S3, S4, S5)) -> Result<Self, Self::Error> {
        Ok((
            T0::try_convert(ss.0).map_err(Into::into)?,
            T1::try_convert(ss.1).map_err(Into::into)?,
            T2::try_convert(ss.2).map_err(Into::into)?,
            T3::try_convert(ss.3).map_err(Into::into)?,
            T4::try_convert(ss.4).map_err(Into::into)?,
            T5::try_convert(ss.5).map_err(Into::into)?,
        ))
    }
    #[inline]
    fn convert(ss: (S0, S1, S2, S3, S4, S5)) -> Self {
        (
            T0::convert(ss.0),
            T1::convert(ss.1),
            T2::convert(ss.2),
            T3::convert(ss.3),
            T4::convert(ss.4),
            T5::convert(ss.5),
        )
    }
}

#[cfg(any(feature = "std", feature = "libm"))]
impl<S0, S1, T0: ConvFloat<S0>, T1: ConvFloat<S1>> ConvFloat<(S0, S1)> for (T0, T1) {
    #[inline]
    fn try_conv_trunc(ss: (S0, S1)) -> Result<Self, RangeError> {
        Ok((T0::try_conv_trunc(ss.0)?, T1::try_conv_trunc(ss.1)?))
    }
    #[inline]
    fn try_conv_nearest(ss: (S0, S1)) -> Result<Self, RangeError> {
        Ok((T0::try_conv_nearest(ss.0)?, T1::try_conv_nearest(ss.1)?))
    }
    #[inline]
    fn try_conv_floor(ss: (S0, S1)) -> Result<Self, RangeError> {
        Ok((T0::try_conv_floor(ss.0)?, T1::try_conv_floor(ss.1)?))
    }
    #[inline]
    fn try_conv_ceil(ss: (S0, S1)) -> Result<Self, RangeError> {
        Ok((T0::try_conv_ceil(ss.0)?, T1::try_conv_ceil(ss.1)?))
    }

    #[inline]
    fn conv_trunc(ss: (S0, S1)) -> Self {
        (T0::conv_trunc(ss.0), T1::conv_trunc(ss.1))
    }
    #[inline]
    fn conv_nearest(ss: (S0, S1)) -> Self {
        (T0::conv_nearest(ss.0), T1::conv_nearest(ss.1))
    }
    #[inline]
    fn conv_floor(ss: (S0, S1)) -> Self {
        (T0::conv_floor(ss.0), T1::conv_floor(ss.1))
    }
    #[inline]
    fn conv_ceil(ss: (S0, S1)) -> Self {
        (T0::conv_ceil(ss.0), T1::conv_ceil(ss.1))
    }
}

/// Implement a trivial [`ConvertExact`] infallibly
///
/// A trivial conversion is one which maps a type to itself.
///
/// # Example
///
/// ```
/// struct MyInt(i32);
///
/// easy_cast::impl_via_trivial!(MyInt);
/// ```
///
/// [`ConvertExact`]: crate::generic::ConvertExact
#[macro_export]
macro_rules! impl_via_trivial {
    ($x:ty) => {
        impl $crate::generic::ConvertExact<$x> for $x {
            type Error = ::core::convert::Infallible;

            #[inline]
            fn convert(x: $x) -> Self {
                x
            }
            #[inline]
            fn try_convert(x: $x) -> Result<Self, Self::Error> {
                Ok(x)
            }
        }
    };
    ($x:ty $(, $xx:tt)* $(,)?) => {
        $crate::impl_via_trivial!($x);
        $crate::impl_via_trivial!($($xx),*);
    };
}

#[rustfmt::skip]
impl_via_trivial!(
    u8, u16, u32, u64, u128, usize,
    i8, i16, i32, i64, i128, isize,
    f32, f64,
);
