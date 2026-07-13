use easy_cast::Error;

#[test]
fn error_traits_and_display_messages() {
    let range = Error::Range;
    let inexact = Error::Inexact;

    assert_eq!(range.clone(), Error::Range);
    assert_eq!(inexact.clone(), Error::Inexact);
    assert_eq!(format!("{range:?}"), "Range");
    assert_eq!(format!("{inexact:?}"), "Inexact");
    assert_eq!(range.to_string(), "source value not in target range");
    assert_eq!(inexact.to_string(), "loss of precision or range error");
}

#[cfg(feature = "std")]
#[test]
fn error_implements_std_error() {
    fn assert_std_error(err: &dyn std::error::Error) -> String {
        err.to_string()
    }

    assert_eq!(
        assert_std_error(&Error::Range),
        "source value not in target range"
    );
}
