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
#[should_panic]
#[cfg(any(feature = "std", feature = "libm"))]
fn float_trunc_fail1() {
    i16::conv_trunc(32768.0f32);
}

#[test]
#[should_panic]
fn u32_max_f32() {
    f32::conv(core::u32::MAX);
}
