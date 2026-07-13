use easy_cast::{Error, traits::*};

#[test]
fn conv_approx_for_integer_sources_forwards_to_conv() {
    assert_eq!(i32::conv_approx(1i32), 1);
    assert_eq!(u8::try_conv_approx(255u16), Ok(255u8));
    assert_eq!(u8::try_conv_approx(256u16), Err(Error::Range));
}
