use easy_cast::{Error, traits::*};

#[test]
fn conv_approx_for_integer_sources_forwards_to_conv() {
    assert_eq!(i32::conv_approx(1i32), 1);
    assert_eq!(u8::try_conv_approx(255u16), Ok(255u8));
    assert_eq!(u8::try_conv_approx(256u16), Err(Error::Range));
}

#[test]
#[cfg(any(feature = "std", feature = "libm"))]
fn conv_approx_for_float_to_int_uses_truncation() {
    assert_eq!(i32::try_conv_approx(1.99f32), Ok(1));
    assert_eq!(i32::try_conv_approx(-1.99f32), Ok(-1));
    assert_eq!(u8::try_conv_approx(9.9f64), Ok(9));
    assert_eq!(u8::try_conv_approx(-0.1f64), Ok(0));
    assert_eq!(u8::try_conv_approx(-1.1f64), Err(Error::Range));
}

#[test]
#[cfg(any(feature = "std", feature = "libm"))]
fn conv_approx_for_f64_to_f32_uses_truncation() {
    const E32: f64 = f32::EPSILON as f64;

    assert_eq!(f32::conv_approx(0.0f64).to_bits(), 0.0f32.to_bits());
    assert_eq!(f32::conv_approx(-0.0f64).to_bits(), (-0.0f32).to_bits());
    assert_eq!(f32::conv_approx(1.0f64 + E32 / 2.0), 1.0f32);
    assert_eq!(f32::conv_approx(1.0f64 + E32), 1.0f32 + f32::EPSILON);
    assert_eq!(
        f32::conv_approx((f32::MIN_POSITIVE as f64) / 2.0).to_bits(),
        f32::from_bits(1 << 22).to_bits()
    );
    assert_eq!(
        f32::conv_approx((f32::from_bits(1) as f64) / 2.0).to_bits(),
        0.0f32.to_bits()
    );
    assert_eq!(
        f32::conv_approx(f64::INFINITY).to_bits(),
        f32::INFINITY.to_bits()
    );
    assert_eq!(f32::try_conv_approx(f64::MAX), Err(Error::Range));
    assert_eq!(f32::try_conv_approx(f64::NAN), Err(Error::Range));
}
