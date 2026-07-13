mod common;

use common::{assert_ok_eq, assert_range};
use core::num::*;
use core::ops::{Range, RangeFrom, RangeInclusive, RangeTo, RangeToInclusive};
use easy_cast::traits::*;

#[test]
fn nonzero_casts() {
    let a = NonZeroI32::new(213).unwrap();
    let b: NonZero<u128> = a.cast();
    let c = NonZeroU8::conv(b);
    let d = c.cast();
    assert_eq!(a, d);
}

#[test]
fn saturating_casts() {
    let a: Saturating<i32> = Saturating(213);
    let b: Saturating<u128> = a.cast();
    let c = Saturating::<u8>::conv(b);
    let d = c.cast();
    assert_eq!(a, d);
}

#[test]
fn wrapping_casts() {
    let a: Wrapping<i32> = Wrapping(213);
    let b: Wrapping<u128> = a.cast();
    let c = Wrapping::<u8>::conv(b);
    let d = c.cast();
    assert_eq!(a, d);
}

#[test]
fn range_cast() {
    let a: Range<usize> = 10..20;
    let b: Range<u8> = a.cast();
    assert_eq!(b, 10..20);
}

#[test]
fn range_inclusive_cast() {
    let a: RangeInclusive<usize> = 0..=255;
    let b: RangeInclusive<u8> = a.cast();
    assert_eq!(b, 0..=255);

    let c: RangeInclusive<usize> = 0..=256;
    assert!(RangeInclusive::<u8>::try_conv(c).is_err());
}

#[test]
fn range_from_cast() {
    let a: RangeFrom<i32> = -12..;
    let b: RangeFrom<i8> = a.cast();
    assert_eq!(b, -12..);
}

#[test]
fn range_to_cast() {
    let a: RangeTo<i32> = ..-12;
    let b: RangeTo<i8> = a.cast();
    assert_eq!(b, ..-12);
}

#[test]
fn range_to_inclusive_cast() {
    let a: RangeToInclusive<i8> = ..=127;
    let b: RangeToInclusive<i16> = a.cast();
    assert_eq!(b, ..=127);
}

#[test]
fn nonzero_try_conv_range_errors() {
    assert_range(NonZeroU8::try_conv(NonZeroI16::new(-1).unwrap()));
    assert_range(NonZeroI8::try_conv(NonZeroU16::new(128).unwrap()));
}

#[test]
fn wrapper_try_conv_range_errors() {
    assert_range(Saturating::<u8>::try_conv(Saturating(256u16)));
    assert_range(Wrapping::<i8>::try_conv(Wrapping(128u16)));
}

#[test]
fn range_try_conv_boundary_checks() {
    assert_ok_eq(Range::<u8>::try_conv(0u32..255u32), 0u8..255u8);
    assert_range(Range::<u8>::try_conv(0u32..256u32));

    assert_ok_eq(RangeInclusive::<u8>::try_conv(0u32..=255u32), 0u8..=255u8);
    assert_range(RangeInclusive::<u8>::try_conv(0u32..=256u32));

    assert_ok_eq(RangeFrom::<u8>::try_conv(10u32..), 10u8..);
    assert_range(RangeFrom::<u8>::try_conv(256u32..));

    assert_ok_eq(RangeTo::<u8>::try_conv(..255u32), ..255u8);
    assert_range(RangeTo::<u8>::try_conv(..256u32));

    assert_ok_eq(RangeToInclusive::<u8>::try_conv(..=255u32), ..=255u8);
    assert_range(RangeToInclusive::<u8>::try_conv(..=256u32));
}
