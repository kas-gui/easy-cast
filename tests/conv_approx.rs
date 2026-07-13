mod common;

use common::{assert_ok_eq, assert_range};
use easy_cast::traits::*;

#[test]
fn conv_approx_for_integer_sources_forwards_to_conv() {
    assert_eq!(i32::conv_approx(1i32), 1);
    assert_ok_eq(u8::try_conv_approx(255u16), 255u8);
    assert_range(u8::try_conv_approx(256u16));
}

#[test]
fn cast_approx_mirrors_conv_approx() {
    let ok: u8 = 42u16.cast_approx();
    assert_eq!(ok, 42);
    assert_range(256u16.try_cast_approx::<u8>());
}
