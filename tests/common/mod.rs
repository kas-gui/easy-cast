use easy_cast::{Error, Result};

#[allow(dead_code)]
pub fn assert_ok_eq<T: core::fmt::Debug + PartialEq>(result: Result<T>, expected: T) {
    assert_eq!(result, Ok(expected));
}

#[allow(dead_code)]
pub fn assert_range<T: core::fmt::Debug + PartialEq>(result: Result<T>) {
    assert_eq!(result, Err(Error::Range));
}

#[allow(dead_code)]
pub fn assert_inexact<T: core::fmt::Debug + PartialEq>(result: Result<T>) {
    assert_eq!(result, Err(Error::Inexact));
}
