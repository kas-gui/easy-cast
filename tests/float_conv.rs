#![cfg(any(feature = "std", feature = "libm"))]

use easy_cast::{Error, traits::*};

#[test]
#[should_panic(expected = "cast float-to-float: NaN")]
fn f32_nan_to_f64() {
    f64::conv(f32::NAN);
}

#[test]
#[should_panic(expected = "cast float-to-float: NaN")]
fn f64_nan_to_f32() {
    f32::conv_approx(f64::NAN);
}

#[test]
fn approx_f64_to_f32() {
    assert_eq!(f32::conv_approx(0f64), 0f32);
    assert_eq!(f32::conv_approx(0f64).is_sign_positive(), true);
    assert_eq!(f32::conv_approx(-0f64).is_sign_negative(), true);

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
    assert_eq!(f32::try_conv_approx(f64::NAN), Err(Error::Range));
}
