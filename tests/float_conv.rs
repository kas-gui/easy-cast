#![cfg(any(feature = "std", feature = "libm"))]

mod common;

use common::{assert_ok_eq, assert_range};
use easy_cast::{Error, traits::*};

macro_rules! assert_all_modes {
    ($value:expr, $dst:ty, trunc = $trunc:expr, nearest = $nearest:expr, floor = $floor:expr, ceil = $ceil:expr) => {
        assert_ok_eq(<$dst>::try_conv_trunc($value), $trunc as $dst);
        assert_ok_eq(<$dst>::try_conv_nearest($value), $nearest as $dst);
        assert_ok_eq(<$dst>::try_conv_floor($value), $floor as $dst);
        assert_ok_eq(<$dst>::try_conv_ceil($value), $ceil as $dst);
    };
}

#[test]
fn trunc_nearest_floor_and_ceil_on_representative_values() {
    assert_all_modes!(1.9f32, i32, trunc = 1, nearest = 2, floor = 1, ceil = 2);
    assert_all_modes!(
        -1.9f32,
        i32,
        trunc = -1,
        nearest = -2,
        floor = -2,
        ceil = -1
    );
    assert_all_modes!(0.5f64, i8, trunc = 0, nearest = 1, floor = 0, ceil = 1);
    assert_all_modes!(-0.5f64, i8, trunc = 0, nearest = -1, floor = -1, ceil = 0);
    assert_all_modes!(2.5f64, u8, trunc = 2, nearest = 3, floor = 2, ceil = 3);
}

#[test]
fn float_boundaries_for_small_integer_types() {
    assert_ok_eq(i8::try_conv_trunc(f32::from(i8::MIN)), i8::MIN);
    assert_ok_eq(i8::try_conv_trunc(f32::from(i8::MAX)), i8::MAX);
    assert_range(i8::try_conv_trunc(f32::from(i8::MIN) - 1.0));
    assert_range(i8::try_conv_trunc(f32::from(i8::MAX) + 1.0));

    assert_ok_eq(u8::try_conv_nearest(255.0f32), u8::MAX);
    assert_range(u8::try_conv_nearest(256.0f32));

    assert_ok_eq(i16::try_conv_floor(f64::from(i16::MIN)), i16::MIN);
    assert_ok_eq(i16::try_conv_ceil(f64::from(i16::MAX)), i16::MAX);
    assert_range(i16::try_conv_floor(f64::from(i16::MIN) - 1.0));
    assert_range(i16::try_conv_ceil(f64::from(i16::MAX) + 1.0));

    assert_ok_eq(u32::try_conv_trunc(f64::from(u32::MAX)), u32::MAX);
    assert_range(u32::try_conv_trunc(f64::from(u32::MAX) + 1.0));
}

#[test]
fn nan_and_infinity_are_range_errors_for_all_modes() {
    for value in [f32::NAN, f32::INFINITY, f32::NEG_INFINITY] {
        assert_eq!(i8::try_conv_trunc(value), Err(Error::Range));
        assert_eq!(i8::try_conv_nearest(value), Err(Error::Range));
        assert_eq!(i8::try_conv_floor(value), Err(Error::Range));
        assert_eq!(i8::try_conv_ceil(value), Err(Error::Range));

        assert_eq!(u128::try_conv_trunc(value), Err(Error::Range));
        assert_eq!(u128::try_conv_nearest(value), Err(Error::Range));
        assert_eq!(u128::try_conv_floor(value), Err(Error::Range));
        assert_eq!(u128::try_conv_ceil(value), Err(Error::Range));
    }

    for value in [f64::NAN, f64::INFINITY, f64::NEG_INFINITY] {
        assert_eq!(i16::try_conv_trunc(value), Err(Error::Range));
        assert_eq!(i16::try_conv_nearest(value), Err(Error::Range));
        assert_eq!(i16::try_conv_floor(value), Err(Error::Range));
        assert_eq!(i16::try_conv_ceil(value), Err(Error::Range));
    }
}

#[test]
fn f32_to_u128_special_case() {
    let max = 0xFFFFFF00_00000000_00000000_00000000u128;
    assert_ok_eq(u128::try_conv_trunc(f32::MAX), max);
    assert_ok_eq(u128::try_conv_nearest(f32::MAX), max);
    assert_ok_eq(u128::try_conv_floor(f32::MAX), max);
    assert_ok_eq(u128::try_conv_ceil(f32::MAX), max);
    assert_ok_eq(u128::try_conv_trunc(0.0f32), 0u128);
    assert_range(u128::try_conv_trunc(-1.0f32));
    assert_range(u128::try_conv_trunc(f32::INFINITY));
}

#[test]
#[should_panic(expected = "cast x: f32 to i16 (trunc): range error for x = 32768")]
fn float_conv_trunc_panics_with_expected_message() {
    i16::conv_trunc(32768.0f32);
}

#[test]
#[should_panic(expected = "cast x: f64 to u8 (ceil): range error for x = -1")]
fn float_conv_ceil_panics_with_expected_message() {
    u8::conv_ceil(-1.1f64);
}
