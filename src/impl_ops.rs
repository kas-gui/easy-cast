// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License in the LICENSE-APACHE file or at:
//     https://www.apache.org/licenses/LICENSE-2.0

//! `core::ops` impls.

use crate::generic::{Convert, Rounding};
use core::ops::{Range, RangeFrom, RangeInclusive, RangeTo, RangeToInclusive};

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
        let start = T::try_convert(n.start().clone())?;
        let end = T::try_convert(n.end().clone())?;
        Ok(RangeInclusive::new(start, end))
    }

    #[inline]
    fn convert(n: RangeInclusive<F>) -> RangeInclusive<T> {
        let start = T::convert(n.start().clone());
        let end = T::convert(n.end().clone());
        RangeInclusive::new(start, end)
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

impl<R: Rounding, F, T: Convert<F, R>> Convert<RangeTo<F>, R> for RangeTo<T> {
    type Error = T::Error;

    #[inline]
    fn try_convert(n: RangeTo<F>) -> Result<RangeTo<T>, Self::Error> {
        Ok(RangeTo {
            end: T::try_convert(n.end)?,
        })
    }

    #[inline]
    fn convert(n: RangeTo<F>) -> RangeTo<T> {
        RangeTo {
            end: T::convert(n.end),
        }
    }
}

impl<R: Rounding, F, T: Convert<F, R>> Convert<RangeToInclusive<F>, R> for RangeToInclusive<T> {
    type Error = T::Error;

    #[inline]
    fn try_convert(n: RangeToInclusive<F>) -> Result<RangeToInclusive<T>, Self::Error> {
        Ok(RangeToInclusive {
            end: T::try_convert(n.end)?,
        })
    }

    #[inline]
    fn convert(n: RangeToInclusive<F>) -> RangeToInclusive<T> {
        RangeToInclusive {
            end: T::convert(n.end),
        }
    }
}
