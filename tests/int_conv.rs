use easy_cast::{Error, traits::*};

macro_rules! assert_signed_to_unsigned {
    ($src:ty => $dst:ty) => {
        assert_eq!(<$dst>::try_conv(0 as $src), Ok(0 as $dst));
        assert_eq!(<$dst>::try_conv(1 as $src), Ok(1 as $dst));
        assert_eq!(<$dst>::try_conv(<$src>::MAX), Ok(<$src>::MAX as $dst));
        assert_eq!(<$dst>::try_conv(-1 as $src), Err(Error::Range));
    };
    ($src:ty => $($dst:ty),+ $(,)?) => {
        $(assert_signed_to_unsigned!($src => $dst);)+
    };
}

macro_rules! assert_unsigned_to_signed {
    ($src:ty => $dst:ty) => {
        assert_eq!(<$dst>::try_conv(0 as $src), Ok(0 as $dst));
        assert_eq!(<$dst>::try_conv(1 as $src), Ok(1 as $dst));
        assert_eq!(<$dst>::try_conv(<$dst>::MAX as $src), Ok(<$dst>::MAX));
        assert_eq!(
            <$dst>::try_conv((<$dst>::MAX as $src) + 1),
            Err(Error::Range)
        );
    };
    ($src:ty => $($dst:ty),+ $(,)?) => {
        $(assert_unsigned_to_signed!($src => $dst);)+
    };
}

#[test]
fn widening_integer_smoke_tests() {
    assert_eq!(i16::try_conv(i8::MIN), Ok(i16::from(i8::MIN)));
    assert_eq!(i32::try_conv(i16::MIN), Ok(i32::from(i16::MIN)));
    assert_eq!(i64::try_conv(i32::MAX), Ok(i64::from(i32::MAX)));
    assert_eq!(i128::try_conv(i64::MIN), Ok(i128::from(i64::MIN)));

    assert_eq!(u16::try_conv(u8::MAX), Ok(u16::from(u8::MAX)));
    assert_eq!(u32::try_conv(u16::MAX), Ok(u32::from(u16::MAX)));
    assert_eq!(u64::try_conv(u32::MAX), Ok(u64::from(u32::MAX)));
    assert_eq!(u128::try_conv(u64::MAX), Ok(u128::from(u64::MAX)));
}

#[test]
fn signed_to_unsigned_boundaries() {
    assert_signed_to_unsigned!(i8 => u8, u16, u32, u64, u128);
    assert_signed_to_unsigned!(i16 => u16, u32, u64, u128);
    assert_signed_to_unsigned!(i32 => u32, u64, u128);
    assert_signed_to_unsigned!(i64 => u64, u128);
    assert_signed_to_unsigned!(i128 => u128);
}

#[test]
fn unsigned_to_signed_boundaries() {
    assert_unsigned_to_signed!(u8 => i8);
    assert_unsigned_to_signed!(u16 => i8, i16);
    assert_unsigned_to_signed!(u32 => i8, i16, i32);
    assert_unsigned_to_signed!(u64 => i8, i16, i32, i64);
    assert_unsigned_to_signed!(u128 => i8, i16, i32, i64, i128);
}

#[test]
fn narrowing_signed_to_signed_boundaries() {
    assert_eq!(i8::try_conv(i32::from(i8::MIN)), Ok(i8::MIN));
    assert_eq!(i8::try_conv(i32::from(i8::MAX)), Ok(i8::MAX));
    assert_eq!(i8::try_conv(i32::from(i8::MIN) - 1), Err(Error::Range));
    assert_eq!(i8::try_conv(i32::from(i8::MAX) + 1), Err(Error::Range));
}

#[test]
fn isize_usize_boundaries() {
    assert_eq!(isize::try_conv(isize::MAX), Ok(isize::MAX));
    assert_eq!(usize::try_conv(0isize), Ok(0usize));
    assert_eq!(usize::try_conv(1isize), Ok(1usize));
    assert_eq!(usize::try_conv(-1isize), Err(Error::Range));
    assert_eq!(isize::try_conv(usize::MAX), Err(Error::Range));
}

#[test]
fn primitive_self_cast_identity() {
    assert_eq!(u8::try_conv(7u8), Ok(7u8));
    assert_eq!(u16::try_conv(7u16), Ok(7u16));
    assert_eq!(u32::try_conv(7u32), Ok(7u32));
    assert_eq!(u64::try_conv(7u64), Ok(7u64));
    assert_eq!(u128::try_conv(7u128), Ok(7u128));
    assert_eq!(usize::try_conv(7usize), Ok(7usize));
    assert_eq!(i8::try_conv(-7i8), Ok(-7i8));
    assert_eq!(i16::try_conv(-7i16), Ok(-7i16));
    assert_eq!(i32::try_conv(-7i32), Ok(-7i32));
    assert_eq!(i64::try_conv(-7i64), Ok(-7i64));
    assert_eq!(i128::try_conv(-7i128), Ok(-7i128));
    assert_eq!(isize::try_conv(-7isize), Ok(-7isize));
    assert_eq!(f32::try_conv(1.25f32), Ok(1.25f32));
    assert_eq!(f64::try_conv(-1.25f64), Ok(-1.25f64));
}

#[test]
#[should_panic(expected = "cast x: i32 to u32: expected x >= 0, found x = -1")]
fn signed_to_unsigned_conv_panics_on_negative() {
    u32::conv(-1i32);
}

#[test]
#[should_panic(expected = "cast x: u32 to i16: expected x <= 32767, found x = 32768")]
fn unsigned_to_signed_conv_panics_out_of_range() {
    i16::conv(32768u32);
}

#[test]
#[should_panic(expected = "cast x: i32 to i8: expected -128 <= x <= 127, found x = 128")]
fn narrowing_signed_to_signed_panics_out_of_range() {
    i8::conv(128i32);
}
