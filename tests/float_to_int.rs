#![cfg(any(feature = "std", feature = "libm"))]

use easy_cast::{RangeError, RoundFrom};
use easy_cast::generic::{Ceil, Floor, Nearest, Trunc};

/// Convenience wrapper: convert from float S to integer T with rounding mode R,
/// via `RoundFrom`. This avoids the E0034 ambiguity that occurs when calling
/// `T::try_round(s, mode)` because both `RoundFrom` and `RoundInto` define
/// `try_round` and Rust cannot always resolve which one is meant.
fn try_rf<T, S, R>(s: S, mode: R) -> Result<T, <T as RoundFrom<S, R>>::Error>
where
    T: RoundFrom<S, R>,
    R: easy_cast::generic::Rounding,
{
    <T as RoundFrom<S, R>>::try_round(s, mode)
}

fn rf<T, S, R>(s: S, mode: R) -> T
where
    T: RoundFrom<S, R>,
    R: easy_cast::generic::Rounding,
{
    <T as RoundFrom<S, R>>::round(s, mode)
}

#[test]
fn float_boundaries_for_small_integer_types() {
    assert_eq!(try_rf(f32::from(i8::MIN), Trunc), Ok(i8::MIN));
    assert_eq!(try_rf(f32::from(i8::MAX), Trunc), Ok(i8::MAX));
    assert_eq!(try_rf::<i8, f32, Trunc>(f32::from(i8::MIN) - 1.0, Trunc), Err(RangeError));
    assert_eq!(try_rf::<i8, f32, Trunc>(f32::from(i8::MAX) + 1.0, Trunc), Err(RangeError));

    assert_eq!(try_rf(255.0f32, Nearest), Ok(u8::MAX));
    assert_eq!(try_rf(256.0f32, Nearest), Err::<u8, _>(RangeError));

    assert_eq!(try_rf(f64::from(i16::MIN), Floor), Ok(i16::MIN));
    assert_eq!(try_rf(f64::from(i16::MAX), Ceil), Ok(i16::MAX));
    assert_eq!(try_rf::<i16, f64, Floor>(f64::from(i16::MIN) - 1.0, Floor), Err(RangeError));
    assert_eq!(try_rf::<i16, f64, Ceil>(f64::from(i16::MAX) + 1.0, Ceil), Err(RangeError));

    assert_eq!(try_rf(f64::from(u32::MAX), Trunc), Ok(u32::MAX));
    assert_eq!(try_rf::<u32, f64, Trunc>(f64::from(u32::MAX) + 1.0, Trunc), Err(RangeError));
}

#[test]
fn nan_and_infinity_are_range_errors_for_all_modes() {
    for value in [f32::NAN, f32::INFINITY, f32::NEG_INFINITY] {
        assert_eq!(try_rf(value, Trunc), Err::<i8, _>(RangeError));
        assert_eq!(try_rf(value, Nearest), Err::<i8, _>(RangeError));
        assert_eq!(try_rf(value, Floor), Err::<i8, _>(RangeError));
        assert_eq!(try_rf(value, Ceil), Err::<i8, _>(RangeError));

        assert_eq!(try_rf(value, Trunc), Err::<u128, _>(RangeError));
        assert_eq!(try_rf(value, Nearest), Err::<u128, _>(RangeError));
        assert_eq!(try_rf(value, Floor), Err::<u128, _>(RangeError));
        assert_eq!(try_rf(value, Ceil), Err::<u128, _>(RangeError));
    }

    for value in [f64::NAN, f64::INFINITY, f64::NEG_INFINITY] {
        assert_eq!(try_rf(value, Trunc), Err::<i16, _>(RangeError));
        assert_eq!(try_rf(value, Nearest), Err::<i16, _>(RangeError));
        assert_eq!(try_rf(value, Floor), Err::<i16, _>(RangeError));
        assert_eq!(try_rf(value, Ceil), Err::<i16, _>(RangeError));
    }
}

#[test]
fn f32_to_u128_special_case() {
    let max = 0xFFFFFF00_00000000_00000000_00000000u128;
    assert_eq!(try_rf(f32::MAX, Trunc), Ok(max));
    assert_eq!(try_rf(f32::MAX, Nearest), Ok(max));
    assert_eq!(try_rf(f32::MAX, Floor), Ok(max));
    assert_eq!(try_rf(f32::MAX, Ceil), Ok(max));
    assert_eq!(try_rf(0.0f32, Trunc), Ok(0u128));
    assert_eq!(try_rf(-1.0f32, Trunc), Err::<u128, _>(RangeError));
    assert_eq!(try_rf(f32::INFINITY, Trunc), Err::<u128, _>(RangeError));
}

#[test]
#[should_panic(expected = "cast x: f32 to i16 (trunc): range error for x = 32768")]
fn float_round_trunc_panics_with_expected_message() {
    rf::<i16, f32, Trunc>(32768.0f32, Trunc);
}

#[test]
#[should_panic(expected = "cast x: f64 to u8 (ceil): range error for x = -1.1")]
fn float_round_ceil_panics_with_expected_message() {
    rf::<u8, f64, Ceil>(-1.1f64, Ceil);
}
