mod common;

use common::{assert_inexact, assert_ok_eq};
use easy_cast::traits::*;

#[test]
fn u32_to_f32_exact_and_inexact() {
    assert_ok_eq(f32::try_conv(0u32), 0.0);
    assert_ok_eq(f32::try_conv(1u32), 1.0);
    assert_ok_eq(f32::try_conv(0x00FF_FFFFu32), 16_777_215.0);
    assert_ok_eq(f32::try_conv(1u32 << 23), 8_388_608.0);
    assert_inexact(f32::try_conv(0x01FF_FFFFu32));
}

#[test]
fn signed_integer_to_float_boundaries() {
    assert_ok_eq(f32::try_conv(i32::MIN), i32::MIN as f32);
    assert_inexact(f32::try_conv(i32::MIN + 1));
    assert_ok_eq(f64::try_conv(i64::MIN), i64::MIN as f64);
    assert_inexact(f64::try_conv(i64::MIN + 1));
}

#[test]
fn wide_integer_to_float_boundaries() {
    const F32_EXACT: u64 = 0x00FF_FFFF;
    const F32_INEXACT: u64 = 0x01FF_FFFF;
    const F64_EXACT: u64 = (1u64 << 53) - 1;
    const F64_INEXACT: u64 = (1u64 << 54) - 1;

    assert_ok_eq(f32::try_conv(F32_EXACT), F32_EXACT as f32);
    assert_inexact(f32::try_conv(F32_INEXACT));
    assert_ok_eq(f64::try_conv(F64_EXACT), F64_EXACT as f64);
    assert_inexact(f64::try_conv(F64_INEXACT));

    assert_ok_eq(f32::try_conv(F32_EXACT as i64), F32_EXACT as f32);
    assert_inexact(f32::try_conv(F32_INEXACT as i64));
    assert_ok_eq(f64::try_conv(F64_EXACT as i128), F64_EXACT as f64);
    assert_inexact(f64::try_conv(F64_INEXACT as i128));

    assert_ok_eq(f32::try_conv(F32_EXACT as u128), F32_EXACT as f32);
    assert_inexact(f32::try_conv(F32_INEXACT as u128));
    assert_ok_eq(f64::try_conv(F64_EXACT as u128), F64_EXACT as f64);
    assert_inexact(f64::try_conv(F64_INEXACT as u128));
}

#[test]
fn usize_and_isize_to_float() {
    assert_ok_eq(f32::try_conv(0usize), 0.0);
    assert_ok_eq(f64::try_conv(1usize), 1.0);
    assert_ok_eq(f32::try_conv(0isize), 0.0);
    assert_ok_eq(f64::try_conv(-1isize), -1.0);

    if usize::BITS > f32::MANTISSA_DIGITS + 1 {
        let inexact = (1usize << ((f32::MANTISSA_DIGITS + 1) as usize)) - 1;
        assert_inexact(f32::try_conv(inexact));
    }

    if isize::BITS > f64::MANTISSA_DIGITS + 1 {
        let inexact = (1isize << ((f64::MANTISSA_DIGITS + 1) as usize)) - 1;
        assert_inexact(f64::try_conv(inexact));
        assert_inexact(f64::try_conv(-inexact));
    }
}

#[test]
#[should_panic(expected = "cast x: u64 to f32: inexact for x = 33554431")]
fn integer_to_float_conv_panics_on_inexact_conversion() {
    f32::conv(0x01FF_FFFFu64);
}
