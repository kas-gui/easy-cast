#![cfg(any(feature = "std", feature = "libm"))]

use easy_cast::generic::{Ceil, Floor, Nearest, Trunc};
use easy_cast::traits::*;
use easy_cast::{RangeError, RoundFrom};

#[test]
fn integer_array_conversions_cover_success_and_failure() {
    assert_eq!(<[u8; 4]>::try_conv([0u32, 1, 255, 42]), Ok([0, 1, 255, 42]));
    assert_eq!(<[u8; 4]>::try_conv([0u32, 1, 256, 42]), Err(RangeError));
}

#[test]
fn zero_length_array_conversions_work() {
    assert_eq!(<[u8; 0]>::try_conv([0u32; 0]), Ok([]));
    assert_eq!(<[i32; 0]>::conv([0i32; 0]), []);
}

#[test]
fn float_array_conversions_cover_all_rounding_modes() {
    assert_eq!(
        <[i32; 3]>::try_round_from([1.9f32, -1.9, 2.0], Trunc),
        Ok([1i32, -1, 2])
    );
    assert_eq!(
        <[i32; 3]>::try_round_from([1.5f32, -1.5, 2.4], Nearest),
        Ok([2i32, -2, 2]),
    );
    assert_eq!(
        <[i32; 3]>::try_round_from([1.9f32, -1.1, 2.0], Floor),
        Ok([1i32, -2, 2])
    );
    assert_eq!(
        <[i32; 3]>::try_round_from([1.1f32, -1.9, 2.0], Ceil),
        Ok([2i32, -1, 2])
    );
    assert_eq!(
        <[u8; 3]>::try_round_from([1.0f32, 256.0, 3.0], Trunc),
        Err(RangeError)
    );
}

#[test]
#[should_panic(expected = "cast x: u32 to u8: expected x <= 255, found x = 256")]
fn integer_array_conv_panics_on_out_of_range_element() {
    let _ = <[u8; 4]>::conv([0u32, 1, 256, 42]);
}
