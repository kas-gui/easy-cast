mod common;

use common::{assert_ok_eq, assert_range};
use easy_cast::traits::*;

macro_rules! assert_signed_to_unsigned {
    ($src:ty => $($dst:ty),+ $(,)?) => {
        $(
            assert_ok_eq(<$dst>::try_conv(0 as $src), 0 as $dst);
            assert_ok_eq(<$dst>::try_conv(1 as $src), 1 as $dst);
            assert_ok_eq(<$dst>::try_conv(<$src>::MAX), <$src>::MAX as $dst);
            assert_range(<$dst>::try_conv(-1 as $src));
        )+
    };
}

macro_rules! assert_unsigned_to_signed {
    ($src:ty => $dst:ty) => {
        assert_ok_eq(<$dst>::try_conv(0 as $src), 0 as $dst);
        assert_ok_eq(<$dst>::try_conv(1 as $src), 1 as $dst);
        assert_ok_eq(<$dst>::try_conv(<$dst>::MAX as $src), <$dst>::MAX);
        assert_range(<$dst>::try_conv((<$dst>::MAX as $src) + 1));
    };
}

#[test]
fn widening_integer_smoke_tests() {
    assert_ok_eq(i16::try_conv(i8::MIN), i16::from(i8::MIN));
    assert_ok_eq(i32::try_conv(i16::MIN), i32::from(i16::MIN));
    assert_ok_eq(i64::try_conv(i32::MAX), i64::from(i32::MAX));
    assert_ok_eq(i128::try_conv(i64::MIN), i128::from(i64::MIN));

    assert_ok_eq(u16::try_conv(u8::MAX), u16::from(u8::MAX));
    assert_ok_eq(u32::try_conv(u16::MAX), u32::from(u16::MAX));
    assert_ok_eq(u64::try_conv(u32::MAX), u64::from(u32::MAX));
    assert_ok_eq(u128::try_conv(u64::MAX), u128::from(u64::MAX));
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
    assert_unsigned_to_signed!(u16 => i8);
    assert_unsigned_to_signed!(u16 => i16);
    assert_unsigned_to_signed!(u32 => i8);
    assert_unsigned_to_signed!(u32 => i16);
    assert_unsigned_to_signed!(u32 => i32);
    assert_unsigned_to_signed!(u64 => i8);
    assert_unsigned_to_signed!(u64 => i16);
    assert_unsigned_to_signed!(u64 => i32);
    assert_unsigned_to_signed!(u64 => i64);
    assert_unsigned_to_signed!(u128 => i8);
    assert_unsigned_to_signed!(u128 => i16);
    assert_unsigned_to_signed!(u128 => i32);
    assert_unsigned_to_signed!(u128 => i64);
    assert_unsigned_to_signed!(u128 => i128);
}

#[test]
fn narrowing_signed_to_signed_boundaries() {
    assert_ok_eq(i8::try_conv(i32::from(i8::MIN)), i8::MIN);
    assert_ok_eq(i8::try_conv(i32::from(i8::MAX)), i8::MAX);
    assert_range(i8::try_conv(i32::from(i8::MIN) - 1));
    assert_range(i8::try_conv(i32::from(i8::MAX) + 1));
}

#[test]
fn isize_usize_boundaries() {
    assert_ok_eq(isize::try_conv(isize::MAX), isize::MAX);
    assert_ok_eq(usize::try_conv(0isize), 0usize);
    assert_ok_eq(usize::try_conv(1isize), 1usize);
    assert_range(usize::try_conv(-1isize));
    assert_range(isize::try_conv(usize::MAX));
}

#[test]
fn primitive_self_cast_identity() {
    assert_ok_eq(u8::try_conv(7u8), 7u8);
    assert_ok_eq(u16::try_conv(7u16), 7u16);
    assert_ok_eq(u32::try_conv(7u32), 7u32);
    assert_ok_eq(u64::try_conv(7u64), 7u64);
    assert_ok_eq(u128::try_conv(7u128), 7u128);
    assert_ok_eq(usize::try_conv(7usize), 7usize);
    assert_ok_eq(i8::try_conv(-7i8), -7i8);
    assert_ok_eq(i16::try_conv(-7i16), -7i16);
    assert_ok_eq(i32::try_conv(-7i32), -7i32);
    assert_ok_eq(i64::try_conv(-7i64), -7i64);
    assert_ok_eq(i128::try_conv(-7i128), -7i128);
    assert_ok_eq(isize::try_conv(-7isize), -7isize);
    assert_ok_eq(f32::try_conv(1.25f32), 1.25f32);
    assert_ok_eq(f64::try_conv(-1.25f64), -1.25f64);
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
