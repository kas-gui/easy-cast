// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License in the LICENSE-APACHE file or at:
//     https://www.apache.org/licenses/LICENSE-2.0

//! `core::ops` impls.

use crate::{ConvTo, Rounding};
use core::ops::{Range, RangeFrom, RangeInclusive, RangeTo, RangeToInclusive};

impl<R: Rounding, F, T: ConvTo<F, R>> ConvTo<Range<F>, R> for Range<T> {
    type Error = T::Error;

    #[inline]
    fn try_conv_to(mode: R, n: Range<F>) -> Result<Range<T>, Self::Error> {
        Ok(Range {
            start: T::try_conv_to(mode, n.start)?,
            end: T::try_conv_to(mode, n.end)?,
        })
    }

    #[inline]
    fn conv_to(mode: R, n: Range<F>) -> Range<T> {
        Range {
            start: T::conv_to(mode, n.start),
            end: T::conv_to(mode, n.end),
        }
    }
}

impl<R: Rounding, F: Clone, T: ConvTo<F, R>> ConvTo<RangeInclusive<F>, R> for RangeInclusive<T> {
    type Error = T::Error;

    #[inline]
    fn try_conv_to(mode: R, n: RangeInclusive<F>) -> Result<RangeInclusive<T>, Self::Error> {
        let start = T::try_conv_to(mode, n.start().clone())?;
        let end = T::try_conv_to(mode, n.end().clone())?;
        Ok(RangeInclusive::new(start, end))
    }

    #[inline]
    fn conv_to(mode: R, n: RangeInclusive<F>) -> RangeInclusive<T> {
        let start = T::conv_to(mode, n.start().clone());
        let end = T::conv_to(mode, n.end().clone());
        RangeInclusive::new(start, end)
    }
}

impl<R: Rounding, F, T: ConvTo<F, R>> ConvTo<RangeFrom<F>, R> for RangeFrom<T> {
    type Error = T::Error;

    #[inline]
    fn try_conv_to(mode: R, n: RangeFrom<F>) -> Result<RangeFrom<T>, Self::Error> {
        Ok(RangeFrom {
            start: T::try_conv_to(mode, n.start)?,
        })
    }

    #[inline]
    fn conv_to(mode: R, n: RangeFrom<F>) -> RangeFrom<T> {
        RangeFrom {
            start: T::conv_to(mode, n.start),
        }
    }
}

impl<R: Rounding, F, T: ConvTo<F, R>> ConvTo<RangeTo<F>, R> for RangeTo<T> {
    type Error = T::Error;

    #[inline]
    fn try_conv_to(mode: R, n: RangeTo<F>) -> Result<RangeTo<T>, Self::Error> {
        Ok(RangeTo {
            end: T::try_conv_to(mode, n.end)?,
        })
    }

    #[inline]
    fn conv_to(mode: R, n: RangeTo<F>) -> RangeTo<T> {
        RangeTo {
            end: T::conv_to(mode, n.end),
        }
    }
}

impl<R: Rounding, F, T: ConvTo<F, R>> ConvTo<RangeToInclusive<F>, R> for RangeToInclusive<T> {
    type Error = T::Error;

    #[inline]
    fn try_conv_to(mode: R, n: RangeToInclusive<F>) -> Result<RangeToInclusive<T>, Self::Error> {
        Ok(RangeToInclusive {
            end: T::try_conv_to(mode, n.end)?,
        })
    }

    #[inline]
    fn conv_to(mode: R, n: RangeToInclusive<F>) -> RangeToInclusive<T> {
        RangeToInclusive {
            end: T::conv_to(mode, n.end),
        }
    }
}
