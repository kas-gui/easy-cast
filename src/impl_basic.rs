// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License in the LICENSE-APACHE file or at:
//     https://www.apache.org/licenses/LICENSE-2.0

//! Basic impls for Conv

use super::*;

macro_rules! impl_via_from {
    ($x:ty: $y:ty) => {
        impl Conv<$x> for $y {
            #[inline]
            fn conv(x: $x) -> $y {
                <$y>::from(x)
            }
            #[inline]
            fn try_conv(x: $x) -> Result<Self> {
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

// TODO(unsize): remove T: Copy + Default bound
// TODO(specialization): implement ConvApprox for arrays and tuples
impl<S, T: Conv<S> + Copy + Default, const N: usize> Conv<[S; N]> for [T; N] {
    #[inline]
    fn try_conv(ss: [S; N]) -> Result<Self> {
        let mut tt = [T::default(); N];
        for (s, t) in IntoIterator::into_iter(ss).zip(tt.iter_mut()) {
            *t = T::try_conv(s)?;
        }
        Ok(tt)
    }
    #[inline]
    fn conv(ss: [S; N]) -> Self {
        let mut tt = [T::default(); N];
        for (s, t) in IntoIterator::into_iter(ss).zip(tt.iter_mut()) {
            *t = T::conv(s);
        }
        tt
    }
}

#[cfg(any(feature = "std", feature = "libm"))]
impl<S, T: ConvFloat<S> + Copy + Default, const N: usize> ConvFloat<[S; N]> for [T; N] {
    #[inline]
    fn try_conv_trunc(ss: [S; N]) -> Result<Self> {
        let mut tt = [T::default(); N];
        for (s, t) in IntoIterator::into_iter(ss).zip(tt.iter_mut()) {
            *t = T::try_conv_trunc(s)?;
        }
        Ok(tt)
    }
    #[inline]
    fn try_conv_nearest(ss: [S; N]) -> Result<Self> {
        let mut tt = [T::default(); N];
        for (s, t) in IntoIterator::into_iter(ss).zip(tt.iter_mut()) {
            *t = T::try_conv_nearest(s)?;
        }
        Ok(tt)
    }
    #[inline]
    fn try_conv_floor(ss: [S; N]) -> Result<Self> {
        let mut tt = [T::default(); N];
        for (s, t) in IntoIterator::into_iter(ss).zip(tt.iter_mut()) {
            *t = T::try_conv_floor(s)?;
        }
        Ok(tt)
    }
    #[inline]
    fn try_conv_ceil(ss: [S; N]) -> Result<Self> {
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

impl Conv<()> for () {
    #[inline]
    fn try_conv(_: ()) -> Result<Self> {
        Ok(())
    }
    #[inline]
    fn conv(_: ()) -> Self {
        ()
    }
}
impl<S0, T0: Conv<S0>> Conv<(S0,)> for (T0,) {
    #[inline]
    fn try_conv(ss: (S0,)) -> Result<Self> {
        Ok((ss.0.try_cast()?,))
    }
    #[inline]
    fn conv(ss: (S0,)) -> Self {
        (ss.0.cast(),)
    }
}
impl<S0, S1, T0: Conv<S0>, T1: Conv<S1>> Conv<(S0, S1)> for (T0, T1) {
    #[inline]
    fn try_conv(ss: (S0, S1)) -> Result<Self> {
        Ok((ss.0.try_cast()?, ss.1.try_cast()?))
    }
    #[inline]
    fn conv(ss: (S0, S1)) -> Self {
        (ss.0.cast(), ss.1.cast())
    }
}
impl<S0, S1, S2, T0: Conv<S0>, T1: Conv<S1>, T2: Conv<S2>> Conv<(S0, S1, S2)> for (T0, T1, T2) {
    #[inline]
    fn try_conv(ss: (S0, S1, S2)) -> Result<Self> {
        Ok((ss.0.try_cast()?, ss.1.try_cast()?, ss.2.try_cast()?))
    }
    #[inline]
    fn conv(ss: (S0, S1, S2)) -> Self {
        (ss.0.cast(), ss.1.cast(), ss.2.cast())
    }
}
impl<S0, S1, S2, S3, T0: Conv<S0>, T1: Conv<S1>, T2: Conv<S2>, T3: Conv<S3>> Conv<(S0, S1, S2, S3)>
    for (T0, T1, T2, T3)
{
    #[inline]
    fn try_conv(ss: (S0, S1, S2, S3)) -> Result<Self> {
        Ok((
            ss.0.try_cast()?,
            ss.1.try_cast()?,
            ss.2.try_cast()?,
            ss.3.try_cast()?,
        ))
    }
    #[inline]
    fn conv(ss: (S0, S1, S2, S3)) -> Self {
        (ss.0.cast(), ss.1.cast(), ss.2.cast(), ss.3.cast())
    }
}
impl<S0, S1, S2, S3, S4, T0: Conv<S0>, T1: Conv<S1>, T2: Conv<S2>, T3: Conv<S3>, T4: Conv<S4>>
    Conv<(S0, S1, S2, S3, S4)> for (T0, T1, T2, T3, T4)
{
    #[inline]
    fn try_conv(ss: (S0, S1, S2, S3, S4)) -> Result<Self> {
        Ok((
            ss.0.try_cast()?,
            ss.1.try_cast()?,
            ss.2.try_cast()?,
            ss.3.try_cast()?,
            ss.4.try_cast()?,
        ))
    }
    #[inline]
    fn conv(ss: (S0, S1, S2, S3, S4)) -> Self {
        (
            ss.0.cast(),
            ss.1.cast(),
            ss.2.cast(),
            ss.3.cast(),
            ss.4.cast(),
        )
    }
}
impl<S0, S1, S2, S3, S4, S5, T0, T1, T2, T3, T4, T5> Conv<(S0, S1, S2, S3, S4, S5)>
    for (T0, T1, T2, T3, T4, T5)
where
    T0: Conv<S0>,
    T1: Conv<S1>,
    T2: Conv<S2>,
    T3: Conv<S3>,
    T4: Conv<S4>,
    T5: Conv<S5>,
{
    #[inline]
    fn try_conv(ss: (S0, S1, S2, S3, S4, S5)) -> Result<Self> {
        Ok((
            ss.0.try_cast()?,
            ss.1.try_cast()?,
            ss.2.try_cast()?,
            ss.3.try_cast()?,
            ss.4.try_cast()?,
            ss.5.try_cast()?,
        ))
    }
    #[inline]
    fn conv(ss: (S0, S1, S2, S3, S4, S5)) -> Self {
        (
            ss.0.cast(),
            ss.1.cast(),
            ss.2.cast(),
            ss.3.cast(),
            ss.4.cast(),
            ss.5.cast(),
        )
    }
}

#[cfg(any(feature = "std", feature = "libm"))]
impl<S0, S1, T0: ConvFloat<S0>, T1: ConvFloat<S1>> ConvFloat<(S0, S1)> for (T0, T1) {
    #[inline]
    fn try_conv_trunc(ss: (S0, S1)) -> Result<Self> {
        Ok((T0::try_conv_trunc(ss.0)?, T1::try_conv_trunc(ss.1)?))
    }
    #[inline]
    fn try_conv_nearest(ss: (S0, S1)) -> Result<Self> {
        Ok((T0::try_conv_nearest(ss.0)?, T1::try_conv_nearest(ss.1)?))
    }
    #[inline]
    fn try_conv_floor(ss: (S0, S1)) -> Result<Self> {
        Ok((T0::try_conv_floor(ss.0)?, T1::try_conv_floor(ss.1)?))
    }
    #[inline]
    fn try_conv_ceil(ss: (S0, S1)) -> Result<Self> {
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

macro_rules! impl_via_trivial {
    ($x:ty) => {
        impl Conv<$x> for $x {
            #[inline]
            fn conv(x: $x) -> Self {
                x
            }
            #[inline]
            fn try_conv(x: $x) -> Result<Self> {
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
    f32, f64,
);
