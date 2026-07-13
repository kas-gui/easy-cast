#![cfg(any(feature = "std", feature = "libm"))]

use easy_cast::traits::*;

#[test]
#[cfg(any(debug_assertions, feature = "always_assert", feature = "assert_int"))]
#[should_panic(expected = "cast x: i32 to u32: expected x >= 0, found x = -1")]
fn integer_conv_panics_when_assertions_are_enabled() {
    u32::conv(-1i32);
}

#[test]
#[cfg(all(
    not(debug_assertions),
    not(feature = "always_assert"),
    not(feature = "assert_int")
))]
fn integer_conv_matches_as_without_assertions() {
    assert_eq!(u32::conv(-1i32), (-1i32) as u32);
}

#[test]
#[cfg(any(debug_assertions, feature = "always_assert", feature = "assert_digits"))]
#[should_panic(expected = "cast x: u32 to f32: inexact for x = 4294967295")]
fn digits_check_panics_when_assertions_are_enabled() {
    f32::conv(u32::MAX);
}

#[test]
#[cfg(all(
    not(debug_assertions),
    not(feature = "always_assert"),
    not(feature = "assert_digits")
))]
fn digits_check_matches_as_without_assertions() {
    assert_eq!(f32::conv(u32::MAX), u32::MAX as f32);
}

#[test]
#[cfg(any(debug_assertions, feature = "always_assert", feature = "assert_float"))]
#[should_panic(expected = "cast x: f32 to i16 (trunc): range error for x = 32768")]
fn float_conv_panics_when_assertions_are_enabled() {
    i16::conv_trunc(32768.0f32);
}

#[test]
#[cfg(all(
    not(debug_assertions),
    not(feature = "always_assert"),
    not(feature = "assert_float")
))]
fn float_conv_matches_as_without_assertions() {
    assert_eq!(i16::conv_trunc(32768.0f32), 32768.0f32 as i16);
}

#[cfg(feature = "assert_nonzero")]
#[test]
fn nonzero_conversions_still_preserve_nonzero_values() {
    use core::num::NonZeroU8;

    let value = NonZeroU8::new(5).unwrap();
    assert_eq!(NonZeroU8::conv(value).get(), 5);
}
