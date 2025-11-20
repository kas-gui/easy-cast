// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License in the LICENSE-APACHE file or at:
//     https://www.apache.org/licenses/LICENSE-2.0

//! `core::ops` impls for Conv.

use super::*;
use core::ops::{Range, RangeFrom, RangeInclusive, RangeTo, RangeToInclusive};

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

impl<F: Clone, T: Conv<F>> Conv<RangeInclusive<F>> for RangeInclusive<T> {
    #[inline]
    fn try_conv(n: RangeInclusive<F>) -> Result<RangeInclusive<T>> {
        let start = n.start().clone().try_cast()?;
        let end = n.end().clone().try_cast()?;
        Ok(RangeInclusive::new(start, end))
    }

    #[inline]
    fn conv(n: RangeInclusive<F>) -> RangeInclusive<T> {
        let start = n.start().clone().cast();
        let end = n.end().clone().cast();
        RangeInclusive::new(start, end)
    }
}

impl<F, T: Conv<F>> Conv<RangeFrom<F>> for RangeFrom<T> {
    #[inline]
    fn try_conv(n: RangeFrom<F>) -> Result<RangeFrom<T>> {
        Ok(RangeFrom {
            start: n.start.try_cast()?,
        })
    }

    #[inline]
    fn conv(n: RangeFrom<F>) -> RangeFrom<T> {
        RangeFrom {
            start: n.start.cast(),
        }
    }
}

impl<F, T: Conv<F>> Conv<RangeTo<F>> for RangeTo<T> {
    #[inline]
    fn try_conv(n: RangeTo<F>) -> Result<RangeTo<T>> {
        Ok(RangeTo {
            end: n.end.try_cast()?,
        })
    }

    #[inline]
    fn conv(n: RangeTo<F>) -> RangeTo<T> {
        RangeTo { end: n.end.cast() }
    }
}

impl<F, T: Conv<F>> Conv<RangeToInclusive<F>> for RangeToInclusive<T> {
    #[inline]
    fn try_conv(n: RangeToInclusive<F>) -> Result<RangeToInclusive<T>> {
        Ok(RangeToInclusive {
            end: n.end.try_cast()?,
        })
    }

    #[inline]
    fn conv(n: RangeToInclusive<F>) -> RangeToInclusive<T> {
        RangeToInclusive { end: n.end.cast() }
    }
}
