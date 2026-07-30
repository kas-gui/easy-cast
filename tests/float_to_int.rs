#![cfg(any(feature = "std", feature = "libm"))]

use easy_cast::generic::{Ceil, Floor, Nearest, Trunc};
use easy_cast::{ConvTo, RangeError};

#[test]
fn float_boundaries_for_small_integer_types() {
    assert_eq!(i8::try_conv_to(Trunc, f32::from(i8::MIN)), Ok(i8::MIN));
    assert_eq!(i8::try_conv_to(Trunc, f32::from(i8::MAX)), Ok(i8::MAX));
    assert_eq!(
        i8::try_conv_to(Trunc, f32::from(i8::MIN) - 1.0),
        Err(RangeError)
    );
    assert_eq!(
        i8::try_conv_to(Trunc, f32::from(i8::MAX) + 1.0),
        Err(RangeError)
    );

    assert_eq!(u8::try_conv_to(Nearest, 255.0f32), Ok(u8::MAX));
    assert_eq!(u8::try_conv_to(Nearest, 256.0f32), Err(RangeError));

    assert_eq!(i16::try_conv_to(Floor, f64::from(i16::MIN)), Ok(i16::MIN));
    assert_eq!(i16::try_conv_to(Ceil, f64::from(i16::MAX)), Ok(i16::MAX));
    assert_eq!(
        i16::try_conv_to(Floor, f64::from(i16::MIN) - 1.0),
        Err(RangeError)
    );
    assert_eq!(
        i16::try_conv_to(Ceil, f64::from(i16::MAX) + 1.0),
        Err(RangeError)
    );

    assert_eq!(u32::try_conv_to(Trunc, f64::from(u32::MAX)), Ok(u32::MAX));
    assert_eq!(
        u32::try_conv_to(Trunc, f64::from(u32::MAX) + 1.0),
        Err(RangeError)
    );
}

#[test]
fn nan_and_infinity_are_range_errors_for_all_modes() {
    for value in [f32::NAN, f32::INFINITY, f32::NEG_INFINITY] {
        assert_eq!(i8::try_conv_to(Trunc, value), Err(RangeError));
        assert_eq!(i8::try_conv_to(Nearest, value), Err(RangeError));
        assert_eq!(i8::try_conv_to(Floor, value), Err(RangeError));
        assert_eq!(i8::try_conv_to(Ceil, value), Err(RangeError));

        assert_eq!(u128::try_conv_to(Trunc, value), Err(RangeError));
        assert_eq!(u128::try_conv_to(Nearest, value), Err(RangeError));
        assert_eq!(u128::try_conv_to(Floor, value), Err(RangeError));
        assert_eq!(u128::try_conv_to(Ceil, value), Err(RangeError));
    }

    for value in [f64::NAN, f64::INFINITY, f64::NEG_INFINITY] {
        assert_eq!(i16::try_conv_to(Trunc, value), Err(RangeError));
        assert_eq!(i16::try_conv_to(Nearest, value), Err(RangeError));
        assert_eq!(i16::try_conv_to(Floor, value), Err(RangeError));
        assert_eq!(i16::try_conv_to(Ceil, value), Err(RangeError));
    }
}

#[test]
fn f32_to_u128_special_case() {
    let max = 0xFFFFFF00_00000000_00000000_00000000u128;
    assert_eq!(u128::try_conv_to(Trunc, f32::MAX), Ok(max));
    assert_eq!(u128::try_conv_to(Nearest, f32::MAX), Ok(max));
    assert_eq!(u128::try_conv_to(Floor, f32::MAX), Ok(max));
    assert_eq!(u128::try_conv_to(Ceil, f32::MAX), Ok(max));
    assert_eq!(u128::try_conv_to(Trunc, 0.0f32), Ok(0u128));
    assert_eq!(u128::try_conv_to(Trunc, -1.0f32), Err(RangeError));
    assert_eq!(u128::try_conv_to(Trunc, f32::INFINITY), Err(RangeError));
}

#[test]
#[should_panic(expected = "cast x: f32 to i16 (trunc): range error for x = 32768")]
fn float_round_trunc_panics_with_expected_message() {
    i16::conv_to(Trunc, 32768.0f32);
}

#[test]
#[should_panic(expected = "cast x: f64 to u8 (ceil): range error for x = -1.1")]
fn float_round_ceil_panics_with_expected_message() {
    u8::conv_to(Ceil, -1.1f64);
}
