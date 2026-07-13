#![cfg(any(feature = "std", feature = "libm"))]

use easy_cast::{Error, traits::*};

#[test]
fn tuple_conversions_cover_arities_one_through_six() {
    assert_eq!(<(u8,)>::try_conv((7u16,)), Ok((7u8,)));
    assert_eq!(<(u8, i8)>::try_conv((7u16, -7i16)), Ok((7u8, -7i8)));
    assert_eq!(
        <(u8, i8, u16)>::try_conv((7u16, -7i16, 9u32)),
        Ok((7u8, -7i8, 9u16)),
    );
    assert_eq!(
        <(u8, i8, u16, i16)>::try_conv((7u16, -7i16, 9u32, -9i32)),
        Ok((7u8, -7i8, 9u16, -9i16)),
    );
    assert_eq!(
        <(u8, i8, u16, i16, u32)>::try_conv((7u16, -7i16, 9u32, -9i32, 11u64)),
        Ok((7u8, -7i8, 9u16, -9i16, 11u32)),
    );
    assert_eq!(
        <(u8, i8, u16, i16, u32, i32)>::try_conv((7u16, -7i16, 9u32, -9i32, 11u64, -11i64)),
        Ok((7u8, -7i8, 9u16, -9i16, 11u32, -11i32)),
    );
}

#[test]
fn tuple_conversions_cover_mixed_types_and_errors() {
    assert_eq!(
        <(u8, i16, f64)>::try_conv((42u32, -12i64, 1.25f32)),
        Ok((42u8, -12i16, 1.25f64)),
    );

    assert_eq!(<(u8,)>::try_conv((256u16,)), Err(Error::Range));
    assert_eq!(<(u8, i8)>::try_conv((1u16, 128i16)), Err(Error::Range));
    assert_eq!(
        <(u8, i8, u16)>::try_conv((1u16, -1i16, 70_000u32)),
        Err(Error::Range)
    );
    assert_eq!(
        <(u8, i8, u16, i16)>::try_conv((1u16, -1i16, 2u32, 40_000i32,)),
        Err(Error::Range)
    );
    assert_eq!(
        <(u8, i8, u16, i16, u32)>::try_conv((1u16, -1i16, 2u32, -2i32, u64::MAX,)),
        Err(Error::Range)
    );
    assert_eq!(
        <(u8, i8, u16, i16, u32, i32)>::try_conv((1u16, -1i16, 2u32, -2i32, 3u64, i64::MAX,)),
        Err(Error::Range)
    );
}

#[test]
fn tuple_float_conversions_cover_all_rounding_modes() {
    assert_eq!(<(i32, u8)>::try_conv_trunc((1.9f32, 2.9f32)), Ok((1, 2)));
    assert_eq!(<(i32, u8)>::try_conv_nearest((1.5f32, 2.5f32)), Ok((2, 3)));
    assert_eq!(<(i32, u8)>::try_conv_floor((1.9f32, 2.9f32)), Ok((1, 2)));
    assert_eq!(<(i32, u8)>::try_conv_ceil((1.1f32, 2.1f32)), Ok((2, 3)));
}
