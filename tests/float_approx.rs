#![cfg(any(feature = "std", feature = "libm"))]

mod common;

use common::{assert_ok_eq, assert_range};
use easy_cast::traits::*;

#[test]
fn subnormal_and_small_normal_f64_values_map_to_zero() {
    let positive_subnormal = f64::from_bits(1);
    let negative_subnormal = f64::from_bits((1u64 << 63) | 1);
    let positive_small_normal = f64::from_bits((896u64) << 52);
    let negative_small_normal = f64::from_bits((1u64 << 63) | ((896u64) << 52));

    let positive_zero = f32::conv_approx(positive_subnormal);
    let negative_zero = f32::conv_approx(negative_subnormal);
    let positive_small = f32::conv_approx(positive_small_normal);
    let negative_small = f32::conv_approx(negative_small_normal);

    assert_eq!(positive_zero.to_bits(), 0.0f32.to_bits());
    assert_eq!(negative_zero.to_bits(), (-0.0f32).to_bits());
    assert_eq!(positive_small.to_bits(), 0.0f32.to_bits());
    assert_eq!(negative_small.to_bits(), (-0.0f32).to_bits());
}

#[test]
fn float_approx_preserves_sign_for_zero_and_infinity() {
    assert_eq!(f32::conv_approx(0.0f64).to_bits(), 0.0f32.to_bits());
    assert_eq!(f32::conv_approx(-0.0f64).to_bits(), (-0.0f32).to_bits());
    assert_eq!(f32::conv_approx(f64::INFINITY).to_bits(), f32::INFINITY.to_bits());
    assert_eq!(
        f32::conv_approx(f64::NEG_INFINITY).to_bits(),
        f32::NEG_INFINITY.to_bits()
    );
}

#[test]
fn float_approx_rejects_values_above_f32_range() {
    assert_range(f32::try_conv_approx(f64::from_bits((1151u64) << 52)));
    assert_range(f32::try_conv_approx(f64::MAX));
}

#[test]
fn float_approx_truncates_low_order_mantissa_bits() {
    let base = 1.0f64;
    let delta = f64::from_bits(base.to_bits() + 1) - base;
    assert_ok_eq(f32::try_conv_approx(base + delta), 1.0f32);
    assert_ok_eq(
        f32::try_conv_approx(1.0f64 + f32::EPSILON as f64),
        1.0f32 + f32::EPSILON
    );
}
