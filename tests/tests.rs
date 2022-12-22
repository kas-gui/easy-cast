use easy_cast::*;

#[test]
fn int_casts() {
    let a: i32 = 213;
    let b: u128 = a.cast();
    let c = u8::conv(b);
    let d = c.cast();
    assert_eq!(a, d);
}

#[test]
fn signed_to_unsigned() {
    u32::conv(0i32);
    u32::conv(1i32);
    u32::conv(core::i32::MAX);
}

#[test]
#[should_panic(expected = "cast x: i32 to u32: expected x >= 0, found x = -1")]
fn signed_to_unsigned_n1() {
    u32::conv(-1i32);
}

#[test]
fn unsigned_to_signed() {
    i32::conv(0u32);
    i32::conv(1u32);
    i16::conv(1usize);
}

#[test]
#[should_panic(expected = "cast x: u32 to i32: expected x <= 2147483647, found x = 2147483648")]
fn unsigned_to_signed_large() {
    i32::conv(0x8000_0000u32);
}

#[test]
fn int_to_float() {
    f32::conv(0);
    f32::conv(0x00FF_FFFF);
    f32::conv(-64i32);
}

#[test]
#[should_panic(expected = "cast x: i32 to f32: inexact for x = 33554431")]
fn int_to_float_inexact() {
    f32::conv(0x01FF_FFFF);
}

#[cfg(any(feature = "std", feature = "libm"))]
#[test]
fn f32_max_to_u128() {
    let v = 0xFFFFFF00_00000000_00000000_00000000u128;
    assert_eq!(u128::conv_trunc(f32::MAX), v);
    assert_eq!(u128::conv_nearest(f32::MAX), v);
    assert_eq!(u128::conv_floor(f32::MAX), v);
    assert_eq!(u128::conv_ceil(f32::MAX), v);
    assert_eq!(u128::conv_approx(f32::MAX), v);
}

#[test]
#[should_panic(
    expected = "cast x: u128 to f32: inexact for x = 340282346638528859811704183484516925441"
)]
fn u128_large_to_f32() {
    let v = 0xFFFFFF00_00000000_00000000_00000000u128 + 1;
    f32::conv(v);
}

#[test]
#[cfg(any(feature = "std", feature = "libm"))]
fn approx_float_to_int() {
    assert_eq!(i32::conv_approx(1.99f32), 1);
    assert_eq!(i32::conv_approx(-1.99f32), -1);
    assert_eq!(i32::conv_approx(9.1f64), 9);

    const MAX: f64 = i32::MAX as f64;
    assert_eq!(i32::conv_approx(MAX), i32::MAX);
    assert_eq!(i32::conv_approx(MAX + 0.9), i32::MAX);
    assert_eq!(i32::try_conv_approx(MAX + 1.0), Err(Error::Range));
}

#[test]
fn approx_f64_f32() {
    assert_eq!(f32::conv_approx(0f64), 0f32);
    assert_eq!(f32::conv_approx(0f64).is_sign_positive(), true);
    assert_eq!(f32::conv_approx(-0f64).is_sign_negative(), true);

    const E32: f64 = f32::EPSILON as f64;
    assert_eq!(f32::conv_approx(1f64), 1f32);
    assert_eq!(f32::conv_approx(1f64 + E32), 1f32 + f32::EPSILON);
    assert_eq!(f32::conv_approx(1f64 + E32 / 2.0), 1f32);
    assert_eq!(f32::conv_approx(1f64 + E32 - f64::EPSILON), 1f32);

    assert_eq!(f32::conv_approx(-10f64), -10f32);
    assert!((f32::conv_approx(1f64 / 3.0) - 1f32 / 3.0).abs() <= f32::EPSILON);

    const MAX: f64 = f32::MAX as f64;
    assert_eq!(f32::conv_approx(MAX), f32::MAX);
    assert!(MAX + 2f64.powi(103) != MAX);
    assert_eq!(f32::conv_approx(MAX + 2f64.powi(103)), f32::MAX);
    assert_eq!(f32::try_conv_approx(MAX * 2.0), Err(Error::Range));

    assert_eq!(
        f32::conv_approx(f64::INFINITY).to_bits(),
        f32::INFINITY.to_bits()
    );
    assert_eq!(f32::try_conv_approx(f64::NAN), Err(Error::Range));
}

#[test]
#[should_panic(expected = "cast x: f64 to f32 (approx): range error for x = NaN")]
fn approx_nan() {
    f32::conv_approx(f64::NAN);
}

#[test]
#[cfg(any(feature = "std", feature = "libm"))]
fn float_casts() {
    assert_eq!(u64::conv_nearest(13.2f32), 13);
    let x: i128 = 13.5f32.cast_nearest();
    assert_eq!(x, 14);
    assert_eq!(u8::conv_floor(13.8f64), 13);
    assert_eq!(u32::conv_ceil(13.1f32), 14);
    assert_eq!(i64::conv_floor(-3168565.13), -3168566);
}

#[test]
#[cfg(any(feature = "std", feature = "libm"))]
fn float_trunc() {
    let xx = [-32768.0f32, -32768.99, -0.99, 0.99, 32767.99];
    let yy = [-32768i16, -32768, 0, 0, 32767];
    for (x, y) in xx[..].iter().zip(yy[..].iter()) {
        assert_eq!(i16::conv_trunc(*x), *y);
    }
}

#[test]
#[should_panic(expected = "cast x: f32 to i16 (trunc): range error for x = 32768")]
#[cfg(any(feature = "std", feature = "libm"))]
fn float_trunc_fail1() {
    i16::conv_trunc(32768.0f32);
}

#[test]
#[should_panic(expected = "cast x: u32 to f32: inexact for x = 4294967295")]
fn u32_max_f32() {
    f32::conv(core::u32::MAX);
}

#[test]
fn self_cast() {
    fn generic<T, U: Conv<T>>(x: T) -> U {
        x.cast()
    }

    let y: u8 = generic(0u8);
    assert_eq!(0, y);

    let y: f32 = generic(0.0f32);
    assert_eq!(0.0, y);
}
