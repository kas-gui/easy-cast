#![cfg(any(feature = "std", feature = "libm"))]

use easy_cast::{Error, traits::*};

#[test]
fn f64_to_f32_zero() {
    assert_eq!(f32::conv_approx(0f64), 0f32);
    assert_eq!(f32::conv_approx(0f64).is_sign_positive(), true);
    assert_eq!(f32::conv_approx(-0f64).is_sign_negative(), true);
}

#[test]
fn f64_to_f32_subnormal() {
    assert_eq!(
        f32::conv_approx((f32::MIN_POSITIVE as f64) / 2.0).to_bits(),
        1 << 22
    );
    assert_eq!(
        f32::conv_approx((f32::from_bits(1) as f64) / 2.0).to_bits(),
        0.0f32.to_bits()
    );
}

#[test]
fn f64_to_f32_normal() {
    const E32: f64 = f32::EPSILON as f64;
    assert_eq!(f32::conv_approx(1f64), 1f32);
    assert_eq!(f32::conv_approx(1f64 + E32), 1f32 + f32::EPSILON);
    assert_eq!(f32::conv_approx(1f64 + E32 / 2.0), 1f32);
    assert_eq!(
        f32::conv_approx((1f64 + E32 / 2.0).next_up()),
        1f32.next_up()
    );

    assert_eq!(f32::conv_approx(-10f64), -10f32);
    assert!((f32::conv_approx(1f64 / 3.0) - 1f32 / 3.0).abs() <= f32::EPSILON);
}

#[test]
fn f64_to_f32_overflow() {
    const MAX: f64 = f32::MAX as f64;
    assert_eq!(f32::conv_approx(MAX), f32::MAX);
    // last non-zero binary digits of mantissa are 1101, which rounds down:
    assert_eq!(f32::conv_approx(MAX + 2f64.powi(102)), f32::MAX);
    // last non-zero binary digits of mantissa are 1110, which rounds up:
    assert_eq!(f32::conv_approx(MAX + 2f64.powi(103)), f32::INFINITY);

    assert_eq!(
        f32::conv_approx(f64::INFINITY).to_bits(),
        f32::INFINITY.to_bits()
    );
    assert_eq!(f32::try_conv_approx(f64::MAX), Ok(f32::INFINITY));
}

#[test]
fn float_nan() {
    assert_eq!(f64::try_conv(f32::NAN), Err(Error::Range));
    assert_eq!(f64::try_conv_approx(f32::NAN), Err(Error::Range));
    assert_eq!(f32::try_conv_approx(f64::NAN), Err(Error::Range));
}
