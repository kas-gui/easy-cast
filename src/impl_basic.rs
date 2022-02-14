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

// TODO: remove T: Copy + Default bound
impl<S, T: Conv<S> + Copy + Default, const N: usize> Conv<[S; N]> for [T; N] {
    #[inline]
    fn try_conv(ss: [S; N]) -> Result<Self, Error> {
        let mut tt = [T::default(); N];
        for (s, t) in IntoIterator::into_iter(ss).zip(tt.iter_mut()) {
            *t = T::try_conv(s)?;
        }
        Ok(tt)
    }
}

impl Conv<()> for () {
    #[inline]
    fn try_conv(_: ()) -> Result<Self, Error> {
        Ok(())
    }
}
impl<S0, T0: Conv<S0>> Conv<(S0,)> for (T0,) {
    #[inline]
    fn try_conv(ss: (S0,)) -> Result<Self, Error> {
        Ok((ss.0.try_cast()?,))
    }
}
impl<S0, S1, T0: Conv<S0>, T1: Conv<S1>> Conv<(S0, S1)> for (T0, T1) {
    #[inline]
    fn try_conv(ss: (S0, S1)) -> Result<Self, Error> {
        Ok((ss.0.try_cast()?, ss.1.try_cast()?))
    }
}
impl<S0, S1, S2, T0: Conv<S0>, T1: Conv<S1>, T2: Conv<S2>> Conv<(S0, S1, S2)> for (T0, T1, T2) {
    #[inline]
    fn try_conv(ss: (S0, S1, S2)) -> Result<Self, Error> {
        Ok((ss.0.try_cast()?, ss.1.try_cast()?, ss.2.try_cast()?))
    }
}
impl<S0, S1, S2, S3, T0: Conv<S0>, T1: Conv<S1>, T2: Conv<S2>, T3: Conv<S3>> Conv<(S0, S1, S2, S3)>
    for (T0, T1, T2, T3)
{
    #[inline]
    fn try_conv(ss: (S0, S1, S2, S3)) -> Result<Self, Error> {
        Ok((
            ss.0.try_cast()?,
            ss.1.try_cast()?,
            ss.2.try_cast()?,
            ss.3.try_cast()?,
        ))
    }
}
impl<S0, S1, S2, S3, S4, T0: Conv<S0>, T1: Conv<S1>, T2: Conv<S2>, T3: Conv<S3>, T4: Conv<S4>>
    Conv<(S0, S1, S2, S3, S4)> for (T0, T1, T2, T3, T4)
{
    #[inline]
    fn try_conv(ss: (S0, S1, S2, S3, S4)) -> Result<Self, Error> {
        Ok((
            ss.0.try_cast()?,
            ss.1.try_cast()?,
            ss.2.try_cast()?,
            ss.3.try_cast()?,
            ss.4.try_cast()?,
        ))
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
    fn try_conv(ss: (S0, S1, S2, S3, S4, S5)) -> Result<Self, Error> {
        Ok((
            ss.0.try_cast()?,
            ss.1.try_cast()?,
            ss.2.try_cast()?,
            ss.3.try_cast()?,
            ss.4.try_cast()?,
            ss.5.try_cast()?,
        ))
    }
}
