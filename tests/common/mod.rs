#![allow(dead_code)]

use easy_cast::{Error, Result};

pub fn assert_ok_eq<T: core::fmt::Debug + PartialEq>(result: Result<T>, expected: T) {
    assert_eq!(result, Ok(expected));
}

pub fn assert_range<T: core::fmt::Debug + PartialEq>(result: Result<T>) {
    assert_eq!(result, Err(Error::Range));
}

pub fn assert_inexact<T: core::fmt::Debug + PartialEq>(result: Result<T>) {
    assert_eq!(result, Err(Error::Inexact));
}
