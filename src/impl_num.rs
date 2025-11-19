// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License in the LICENSE-APACHE file or at:
//     https://www.apache.org/licenses/LICENSE-2.0

//! `core::num` impls for Conv.

use super::*;
use core::num::{Saturating, Wrapping};

impl<F, T: Conv<F>> Conv<Saturating<F>> for Saturating<T> {
    #[inline]
    fn try_conv(n: Saturating<F>) -> Result<Saturating<T>> {
        n.0.try_cast().map(Saturating)
    }

    #[inline]
    fn conv(n: Saturating<F>) -> Saturating<T> {
        Saturating(n.0.cast())
    }
}

impl<F, T: Conv<F>> Conv<Wrapping<F>> for Wrapping<T> {
    #[inline]
    fn try_conv(n: Wrapping<F>) -> Result<Wrapping<T>> {
        n.0.try_cast().map(Wrapping)
    }

    #[inline]
    fn conv(n: Wrapping<F>) -> Wrapping<T> {
        Wrapping(n.0.cast())
    }
}
