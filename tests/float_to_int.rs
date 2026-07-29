#![cfg(any(feature = "std", feature = "libm"))]

use easy_cast::generic::{Ceil, Floor, Nearest, Trunc};
use easy_cast::{ConvTo, RangeError};

#[test]
fn float_boundaries_for_small_integer_types() {
    assert_eq!(i8::try_conv_to(f32::from(i8::MIN), Trunc), Ok(i8::MIN));
    assert_eq!(i8::try_conv_to(f32::from(i8::MAX), Trunc), Ok(i8::MAX));
    assert_eq!(
        i8::try_conv_to(f32::from(i8::MIN) - 1.0, Trunc),
        Err(RangeError)
    );
    assert_eq!(
        i8::try_conv_to(f32::from(i8::MAX) + 1.0, Trunc),
        Err(RangeError)
    );

    assert_eq!(u8::try_conv_to(255.0f32, Nearest), Ok(u8::MAX));
    assert_eq!(u8::try_conv_to(256.0f32, Nearest), Err(RangeError));

    assert_eq!(i16::try_conv_to(f64::from(i16::MIN), Floor), Ok(i16::MIN));
    assert_eq!(i16::try_conv_to(f64::from(i16::MAX), Ceil), Ok(i16::MAX));
    assert_eq!(
        i16::try_conv_to(f64::from(i16::MIN) - 1.0, Floor),
        Err(RangeError)
    );
    assert_eq!(
        i16::try_conv_to(f64::from(i16::MAX) + 1.0, Ceil),
        Err(RangeError)
    );

    assert_eq!(u32::try_conv_to(f64::from(u32::MAX), Trunc), Ok(u32::MAX));
    assert_eq!(
        u32::try_conv_to(f64::from(u32::MAX) + 1.0, Trunc),
        Err(RangeError)
    );
}

#[test]
fn nan_and_infinity_are_range_errors_for_all_modes() {
    for value in [f32::NAN, f32::INFINITY, f32::NEG_INFINITY] {
        assert_eq!(i8::try_conv_to(value, Trunc), Err(RangeError));
        assert_eq!(i8::try_conv_to(value, Nearest), Err(RangeError));
        assert_eq!(i8::try_conv_to(value, Floor), Err(RangeError));
        assert_eq!(i8::try_conv_to(value, Ceil), Err(RangeError));

        assert_eq!(u128::try_conv_to(value, Trunc), Err(RangeError));
        assert_eq!(u128::try_conv_to(value, Nearest), Err(RangeError));
        assert_eq!(u128::try_conv_to(value, Floor), Err(RangeError));
        assert_eq!(u128::try_conv_to(value, Ceil), Err(RangeError));
    }

    for value in [f64::NAN, f64::INFINITY, f64::NEG_INFINITY] {
        assert_eq!(i16::try_conv_to(value, Trunc), Err(RangeError));
        assert_eq!(i16::try_conv_to(value, Nearest), Err(RangeError));
        assert_eq!(i16::try_conv_to(value, Floor), Err(RangeError));
        assert_eq!(i16::try_conv_to(value, Ceil), Err(RangeError));
    }
}

#[test]
fn f32_to_u128_special_case() {
    let max = 0xFFFFFF00_00000000_00000000_00000000u128;
    assert_eq!(u128::try_conv_to(f32::MAX, Trunc), Ok(max));
    assert_eq!(u128::try_conv_to(f32::MAX, Nearest), Ok(max));
    assert_eq!(u128::try_conv_to(f32::MAX, Floor), Ok(max));
    assert_eq!(u128::try_conv_to(f32::MAX, Ceil), Ok(max));
    assert_eq!(u128::try_conv_to(0.0f32, Trunc), Ok(0u128));
    assert_eq!(u128::try_conv_to(-1.0f32, Trunc), Err(RangeError));
    assert_eq!(u128::try_conv_to(f32::INFINITY, Trunc), Err(RangeError));
}

#[test]
#[should_panic(expected = "cast x: f32 to i16 (trunc): range error for x = 32768")]
fn float_round_trunc_panics_with_expected_message() {
    i16::conv_to(32768.0f32, Trunc);
}

#[test]
#[should_panic(expected = "cast x: f64 to u8 (ceil): range error for x = -1.1")]
fn float_round_ceil_panics_with_expected_message() {
    u8::conv_to(-1.1f64, Ceil);
}
