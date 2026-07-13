mod common;

use common::{assert_ok_eq, assert_range};
use core::num::*;
use core::range::{Range, RangeFrom, RangeInclusive, RangeToInclusive};
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
    let a: Range<usize> = (10..20).into();
    let b: Range<u8> = a.cast();
    assert_eq!(b, (10..20).into());
}

#[test]
fn range_inclusive_cast() {
    let a: RangeInclusive<usize> = (0..=255).into();
    let b: RangeInclusive<u8> = a.cast();
    assert_eq!(b, (0..=255).into());

    let c: RangeInclusive<usize> = (0..=256).into();
    assert!(RangeInclusive::<u8>::try_conv(c).is_err());
}

#[test]
fn range_from_cast() {
    let a: RangeFrom<i32> = (-12..).into();
    let b: RangeFrom<i8> = a.cast();
    assert_eq!(b, (-12..).into());
}

#[test]
fn range_to_inclusive_cast() {
    let a: RangeToInclusive<i8> = (..=127).into();
    let b: RangeToInclusive<i16> = a.cast();
    assert_eq!(b, (..=127).into());
}

#[test]
fn range_try_conv_boundary_checks() {
    assert_ok_eq(
        Range::<u8>::try_conv((0u32..255u32).into()),
        (0u8..255u8).into(),
    );
    assert_range(Range::<u8>::try_conv((0u32..256u32).into()));

    assert_ok_eq(
        RangeInclusive::<u8>::try_conv((0u32..=255u32).into()),
        (0u8..=255u8).into(),
    );
    assert_range(RangeInclusive::<u8>::try_conv((0u32..=256u32).into()));

    assert_ok_eq(RangeFrom::<u8>::try_conv((10u32..).into()), (10u8..).into());
    assert_range(RangeFrom::<u8>::try_conv((256u32..).into()));

    assert_ok_eq(
        RangeToInclusive::<u8>::try_conv((..=255u32).into()),
        (..=255u8).into(),
    );
    assert_range(RangeToInclusive::<u8>::try_conv((..=256u32).into()));
}
