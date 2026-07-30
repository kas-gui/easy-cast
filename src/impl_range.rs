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
    fn try_convert(n: Range<F>) -> Result<Range<T>, Self::Error> {
        Ok(Range {
            start: T::try_convert(n.start)?,
            end: T::try_convert(n.end)?,
        })
    }

    #[inline]
    fn convert(n: Range<F>) -> Range<T> {
        Range {
            start: T::convert(n.start),
            end: T::convert(n.end),
        }
    }
}

impl<R: Rounding, F: Clone, T: Convert<F, R>> Convert<RangeInclusive<F>, R> for RangeInclusive<T> {
    type Error = T::Error;

    #[inline]
    fn try_convert(n: RangeInclusive<F>) -> Result<RangeInclusive<T>, Self::Error> {
        let start = T::try_convert(n.start.clone())?;
        let last = T::try_convert(n.last.clone())?;
        Ok(RangeInclusive { start, last })
    }

    #[inline]
    fn convert(n: RangeInclusive<F>) -> RangeInclusive<T> {
        let start = T::convert(n.start.clone());
        let last = T::convert(n.last.clone());
        RangeInclusive { start, last }
    }
}

impl<R: Rounding, F, T: Convert<F, R>> Convert<RangeFrom<F>, R> for RangeFrom<T> {
    type Error = T::Error;

    #[inline]
    fn try_convert(n: RangeFrom<F>) -> Result<RangeFrom<T>, Self::Error> {
        Ok(RangeFrom {
            start: T::try_convert(n.start)?,
        })
    }

    #[inline]
    fn convert(n: RangeFrom<F>) -> RangeFrom<T> {
        RangeFrom {
            start: T::convert(n.start),
        }
    }
}

impl<R: Rounding, F, T: Convert<F, R>> Convert<RangeToInclusive<F>, R> for RangeToInclusive<T> {
    type Error = T::Error;

    #[inline]
    fn try_convert(n: RangeToInclusive<F>) -> Result<RangeToInclusive<T>, Self::Error> {
        Ok(RangeToInclusive {
            last: T::try_convert(n.last)?,
        })
    }

    #[inline]
    fn convert(n: RangeToInclusive<F>) -> RangeToInclusive<T> {
        RangeToInclusive {
            last: T::convert(n.last),
        }
    }
}
