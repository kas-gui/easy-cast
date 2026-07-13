#![cfg(any(feature = "std", feature = "libm"))]

mod common;

use common::{assert_ok_eq, assert_range};
use easy_cast::traits::*;

#[test]
fn tuple_conversions_cover_arities_one_through_six() {
    assert_ok_eq(<(u8,)>::try_conv((7u16,)), (7u8,));
    assert_ok_eq(<(u8, i8)>::try_conv((7u16, -7i16)), (7u8, -7i8));
    assert_ok_eq(
        <(u8, i8, u16)>::try_conv((7u16, -7i16, 9u32)),
        (7u8, -7i8, 9u16),
    );
    assert_ok_eq(
        <(u8, i8, u16, i16)>::try_conv((7u16, -7i16, 9u32, -9i32)),
        (7u8, -7i8, 9u16, -9i16),
    );
    assert_ok_eq(
        <(u8, i8, u16, i16, u32)>::try_conv((7u16, -7i16, 9u32, -9i32, 11u64)),
        (7u8, -7i8, 9u16, -9i16, 11u32),
    );
    assert_ok_eq(
        <(u8, i8, u16, i16, u32, i32)>::try_conv((7u16, -7i16, 9u32, -9i32, 11u64, -11i64)),
        (7u8, -7i8, 9u16, -9i16, 11u32, -11i32),
    );
}

#[test]
fn tuple_conversions_cover_mixed_types_and_errors() {
    assert_ok_eq(
        <(u8, i16, f64)>::try_conv((42u32, -12i64, 1.25f32)),
        (42u8, -12i16, 1.25f64),
    );

    assert_range(<(u8,)>::try_conv((256u16,)));
    assert_range(<(u8, i8)>::try_conv((1u16, 128i16)));
    assert_range(<(u8, i8, u16)>::try_conv((1u16, -1i16, 70_000u32)));
    assert_range(<(u8, i8, u16, i16)>::try_conv((
        1u16, -1i16, 2u32, 40_000i32,
    )));
    assert_range(<(u8, i8, u16, i16, u32)>::try_conv((
        1u16,
        -1i16,
        2u32,
        -2i32,
        u64::MAX,
    )));
    assert_range(<(u8, i8, u16, i16, u32, i32)>::try_conv((
        1u16,
        -1i16,
        2u32,
        -2i32,
        3u64,
        i64::MAX,
    )));
}

#[test]
fn tuple_float_conversions_cover_all_rounding_modes() {
    assert_ok_eq(<(i32, u8)>::try_conv_trunc((1.9f32, 2.9f32)), (1, 2));
    assert_ok_eq(<(i32, u8)>::try_conv_nearest((1.5f32, 2.5f32)), (2, 3));
    assert_ok_eq(<(i32, u8)>::try_conv_floor((1.9f32, 2.9f32)), (1, 2));
    assert_ok_eq(<(i32, u8)>::try_conv_ceil((1.1f32, 2.1f32)), (2, 3));
}
