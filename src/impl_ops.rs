// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License in the LICENSE-APACHE file or at:
//     https://www.apache.org/licenses/LICENSE-2.0

//! `core::ops` impls for Conv.

use super::*;
use core::ops::Range;

impl<F, T: Conv<F>> Conv<Range<F>> for Range<T> {
    #[inline]
    fn try_conv(n: Range<F>) -> Result<Range<T>> {
        Ok(Range {
            start: n.start.try_cast()?,
            end: n.end.try_cast()?,
        })
    }

    #[inline]
    fn conv(n: Range<F>) -> Range<T> {
        Range {
            start: n.start.cast(),
            end: n.end.cast(),
        }
    }
}
