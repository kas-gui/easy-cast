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
