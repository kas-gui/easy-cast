// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License in the LICENSE-APACHE file or at:
//     https://www.apache.org/licenses/LICENSE-2.0

//! `core::range` impls.

use crate::{Rounding, generic::Convert};
use core::range::{Range, RangeFrom, RangeInclusive, RangeToInclusive};

impl<R: Rounding, F, T: Convert<F, R>> Convert<Range<F>, R> for Range<T> {
    type Error = T::Error;

    #[inline]
    fn try_convert(mode: R, n: Range<F>) -> Result<Range<T>, Self::Error> {
        Ok(Range {
            start: T::try_convert(mode, n.start)?,
            end: T::try_convert(mode, n.end)?,
        })
    }

    #[inline]
    fn convert(mode: R, n: Range<F>) -> Range<T> {
        Range {
            start: T::convert(mode, n.start),
            end: T::convert(mode, n.end),
        }
    }
}

impl<R: Rounding, F: Clone, T: Convert<F, R>> Convert<RangeInclusive<F>, R> for RangeInclusive<T> {
    type Error = T::Error;

    #[inline]
    fn try_convert(mode: R, n: RangeInclusive<F>) -> Result<RangeInclusive<T>, Self::Error> {
        let start = T::try_convert(mode, n.start.clone())?;
        let last = T::try_convert(mode, n.last.clone())?;
        Ok(RangeInclusive { start, last })
    }

    #[inline]
    fn convert(mode: R, n: RangeInclusive<F>) -> RangeInclusive<T> {
        let start = T::convert(mode, n.start.clone());
        let last = T::convert(mode, n.last.clone());
        RangeInclusive { start, last }
    }
}

impl<R: Rounding, F, T: Convert<F, R>> Convert<RangeFrom<F>, R> for RangeFrom<T> {
    type Error = T::Error;

    #[inline]
    fn try_convert(mode: R, n: RangeFrom<F>) -> Result<RangeFrom<T>, Self::Error> {
        Ok(RangeFrom {
            start: T::try_convert(mode, n.start)?,
        })
    }

    #[inline]
    fn convert(mode: R, n: RangeFrom<F>) -> RangeFrom<T> {
        RangeFrom {
            start: T::convert(mode, n.start),
        }
    }
}

impl<R: Rounding, F, T: Convert<F, R>> Convert<RangeToInclusive<F>, R> for RangeToInclusive<T> {
    type Error = T::Error;

    #[inline]
    fn try_convert(mode: R, n: RangeToInclusive<F>) -> Result<RangeToInclusive<T>, Self::Error> {
        Ok(RangeToInclusive {
            last: T::try_convert(mode, n.last)?,
        })
    }

    #[inline]
    fn convert(mode: R, n: RangeToInclusive<F>) -> RangeToInclusive<T> {
        RangeToInclusive {
            last: T::convert(mode, n.last),
        }
    }
}
