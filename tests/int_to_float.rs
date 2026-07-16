use easy_cast::{Error, traits::*};

#[test]
fn int_to_float_exact_and_inexact() {
    assert_eq!(f32::try_conv(0u32), Ok(0.0));
    assert_eq!(f32::try_conv(1u32), Ok(1.0));
    assert_eq!(f32::try_conv(-0x00FF_FFFFi32), Ok(-16_777_215.0));
    assert_eq!(f32::try_conv(-0x01FF_FFFFi32), Err(Error::Inexact));
    assert_eq!(f32::try_conv(0xFFFF_FF00u32), Ok(4_294_967_000.0));
    assert_eq!(f32::try_conv(0xFFFF_FF80u32), Err(Error::Inexact));

    assert_eq!(f64::try_conv(-0x0000_000F_FFFF_FFFFi64), Ok(-68719476735.0));
    assert_eq!(
        f64::try_conv(-0x001F_FFFF_FFFF_FFFFi64),
        Ok(-9007199254740991.0)
    );
    assert_eq!(
        f64::try_conv(-0x003F_FFFF_FFFF_FFFFi64),
        Err(Error::Inexact)
    );
    assert_eq!(
        f64::try_conv(0xFFFF_FFFF_FFFF_F800u64),
        Ok(18446744073709549568.0)
    );
    assert_eq!(f64::try_conv(0xFFFF_FFFF_FFFF_FC00u64), Err(Error::Inexact));
}

#[test]
fn signed_integer_to_float_boundaries() {
    assert_eq!(f32::try_conv(i32::MIN), Ok(i32::MIN as f32));
    assert_eq!(f32::try_conv(i32::MIN + 1), Err(Error::Inexact));
    assert_eq!(f64::try_conv(i64::MIN), Ok(i64::MIN as f64));
    assert_eq!(f64::try_conv(i64::MIN + 1), Err(Error::Inexact));
}

#[test]
fn wide_integer_to_float_boundaries() {
    const F32_EXACT: u64 = 0x00FF_FFFF;
    const F32_INEXACT: u64 = 0x01FF_FFFF;
    const F64_EXACT: u64 = (1u64 << 53) - 1;
    const F64_INEXACT: u64 = (1u64 << 54) - 1;

    assert_eq!(f32::try_conv(F32_EXACT), Ok(F32_EXACT as f32));
    assert_eq!(f32::try_conv(F32_INEXACT), Err(Error::Inexact));
    assert_eq!(f64::try_conv(F64_EXACT), Ok(F64_EXACT as f64));
    assert_eq!(f64::try_conv(F64_INEXACT), Err(Error::Inexact));

    assert_eq!(f32::try_conv(F32_EXACT as i64), Ok(F32_EXACT as f32));
    assert_eq!(f32::try_conv(F32_INEXACT as i64), Err(Error::Inexact));
    assert_eq!(f64::try_conv(F64_EXACT as i128), Ok(F64_EXACT as f64));
    assert_eq!(f64::try_conv(F64_INEXACT as i128), Err(Error::Inexact));

    assert_eq!(f32::try_conv(F32_EXACT as u128), Ok(F32_EXACT as f32));
    assert_eq!(f32::try_conv(F32_INEXACT as u128), Err(Error::Inexact));
    assert_eq!(f64::try_conv(F64_EXACT as u128), Ok(F64_EXACT as f64));
    assert_eq!(f64::try_conv(F64_INEXACT as u128), Err(Error::Inexact));
}

#[test]
fn usize_and_isize_to_float() {
    assert_eq!(f32::try_conv(0usize), Ok(0.0));
    assert_eq!(f64::try_conv(1usize), Ok(1.0));
    assert_eq!(f32::try_conv(0isize), Ok(0.0));
    assert_eq!(f64::try_conv(-1isize), Ok(-1.0));

    if usize::BITS > f32::MANTISSA_DIGITS + 1 {
        let inexact = (1usize << ((f32::MANTISSA_DIGITS + 1) as usize)) - 1;
        assert_eq!(f32::try_conv(inexact), Err(Error::Inexact));
    }

    if isize::BITS > f64::MANTISSA_DIGITS + 1 {
        let inexact = (1isize << ((f64::MANTISSA_DIGITS + 1) as usize)) - 1;
        assert_eq!(f64::try_conv(inexact), Err(Error::Inexact));
        assert_eq!(f64::try_conv(-inexact), Err(Error::Inexact));
    }
}

#[test]
#[should_panic(expected = "cast x: u64 to f32: inexact for x = 33554431")]
fn integer_to_float_conv_panics_on_inexact_conversion() {
    f32::conv(0x01FF_FFFFu64);
}
