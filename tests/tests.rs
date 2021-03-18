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
fn float_casts() {
    assert_eq!(u64::conv_nearest(13.2f32), 13);
    let x: i128 = 13.5f32.cast_nearest();
    assert_eq!(x, 14);
    assert_eq!(u8::conv_floor(13.8f64), 13);
    assert_eq!(u32::conv_ceil(13.1f32), 14);
}
