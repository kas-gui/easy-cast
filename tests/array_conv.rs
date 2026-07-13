#![cfg(any(feature = "std", feature = "libm"))]

mod common;

use common::{assert_ok_eq, assert_range};
use easy_cast::traits::*;

#[test]
fn integer_array_conversions_cover_success_and_failure() {
    assert_ok_eq(<[u8; 4]>::try_conv([0u32, 1, 255, 42]), [0, 1, 255, 42]);
    assert_range(<[u8; 4]>::try_conv([0u32, 1, 256, 42]));
}

#[test]
fn zero_length_array_conversions_work() {
    assert_ok_eq(<[u8; 0]>::try_conv([0u32; 0]), []);
    assert_eq!(<[i32; 0]>::conv([0i32; 0]), []);
}

#[test]
fn float_array_conversions_cover_all_rounding_modes() {
    assert_ok_eq(<[i32; 3]>::try_conv_trunc([1.9f32, -1.9, 2.0]), [1, -1, 2]);
    assert_ok_eq(
        <[i32; 3]>::try_conv_nearest([1.5f32, -1.5, 2.4]),
        [2, -2, 2],
    );
    assert_ok_eq(<[i32; 3]>::try_conv_floor([1.9f32, -1.1, 2.0]), [1, -2, 2]);
    assert_ok_eq(<[i32; 3]>::try_conv_ceil([1.1f32, -1.9, 2.0]), [2, -1, 2]);
    assert_range(<[u8; 3]>::try_conv_trunc([1.0f32, 256.0, 3.0]));
}

#[test]
#[should_panic(expected = "cast x: u32 to u8: expected x <= 255, found x = 256")]
fn integer_array_conv_panics_on_out_of_range_element() {
    let _ = <[u8; 4]>::conv([0u32, 1, 256, 42]);
}
