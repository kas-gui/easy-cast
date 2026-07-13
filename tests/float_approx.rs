#![cfg(any(feature = "std", feature = "libm"))]

use easy_cast::{Error, traits::*};

#[test]
fn subnormal_and_small_normal_f64_values_map_to_zero() {
    let positive_subnormal = f64::MIN_POSITIVE / 2.0;
    let negative_subnormal = -positive_subnormal;
    let positive_small_normal = (f32::MIN_POSITIVE as f64) / 2.0;
    let negative_small_normal = -positive_small_normal;

    assert_eq!(f32::conv_approx(positive_subnormal).to_bits(), 0.0f32.to_bits());
    assert_eq!(f32::conv_approx(negative_subnormal).to_bits(), (-0.0f32).to_bits());
    assert_eq!(f32::conv_approx(positive_small_normal).to_bits(), 0.0f32.to_bits());
    assert_eq!(f32::conv_approx(negative_small_normal).to_bits(), (-0.0f32).to_bits());
}

#[test]
fn float_approx_preserves_sign_for_zero_and_infinity() {
    assert_eq!(f32::conv_approx(0.0f64).to_bits(), 0.0f32.to_bits());
    assert_eq!(f32::conv_approx(-0.0f64).to_bits(), (-0.0f32).to_bits());
    assert_eq!(
        f32::conv_approx(f64::INFINITY).to_bits(),
        f32::INFINITY.to_bits()
    );
    assert_eq!(
        f32::conv_approx(f64::NEG_INFINITY).to_bits(),
        f32::NEG_INFINITY.to_bits()
    );
}

#[test]
fn float_approx_rejects_values_above_f32_range() {
    assert_eq!(f32::try_conv_approx(f64::from_bits(1151u64 << 52)), Err(Error::Range));
    assert_eq!(f32::try_conv_approx(f64::MAX), Err(Error::Range));
}

#[test]
fn float_approx_truncates_low_order_mantissa_bits() {
    let base = 1.0f64;
    let delta = f64::from_bits(base.to_bits() + 1) - base;
    assert_eq!(f32::try_conv_approx(base + delta), Ok(1.0f32));
    assert_eq!(
        f32::try_conv_approx(1.0f64 + f32::EPSILON as f64),
        Ok(1.0f32 + f32::EPSILON),
    );
}
