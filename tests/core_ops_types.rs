use core::num::*;
use core::ops::{Range, RangeFrom, RangeInclusive, RangeTo, RangeToInclusive};
use easy_cast::{Error, traits::*};

#[test]
fn nonzero_casts() {
    let a = NonZeroI32::new(213).unwrap();
    let b: NonZero<u128> = a.cast();
    let c = NonZeroU8::conv(b);
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
    assert_eq!(
        NonZeroU8::try_conv(NonZeroI16::new(-1).unwrap()),
        Err(Error::Range)
    );
    assert_eq!(
        NonZeroI8::try_conv(NonZeroU16::new(128).unwrap()),
        Err(Error::Range)
    );
}

#[test]
fn range_try_conv_boundary_checks() {
    assert_eq!(Range::<u8>::try_conv(0u32..255u32), Ok(0u8..255u8));
    assert_eq!(Range::<u8>::try_conv(0u32..256u32), Err(Error::Range));

    assert_eq!(
        RangeInclusive::<u8>::try_conv(0u32..=255u32),
        Ok(0u8..=255u8)
    );
    assert_eq!(
        RangeInclusive::<u8>::try_conv(0u32..=256u32),
        Err(Error::Range)
    );

    assert_eq!(RangeFrom::<u8>::try_conv(10u32..), Ok(10u8..));
    assert_eq!(RangeFrom::<u8>::try_conv(256u32..), Err(Error::Range));

    assert_eq!(RangeTo::<u8>::try_conv(..255u32), Ok(..255u8));
    assert_eq!(RangeTo::<u8>::try_conv(..256u32), Err(Error::Range));

    assert_eq!(RangeToInclusive::<u8>::try_conv(..=255u32), Ok(..=255u8));
    assert_eq!(
        RangeToInclusive::<u8>::try_conv(..=256u32),
        Err(Error::Range)
    );
}
