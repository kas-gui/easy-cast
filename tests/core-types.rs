use core::num::{Saturating, Wrapping};
use core::ops::Range;
use easy_cast::traits::*;

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
