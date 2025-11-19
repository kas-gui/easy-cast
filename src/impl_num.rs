// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License in the LICENSE-APACHE file or at:
//     https://www.apache.org/licenses/LICENSE-2.0

//! `core::num` impls for Conv.

use super::*;
use core::num::{NonZero, Saturating, Wrapping, ZeroablePrimitive};

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

impl<F: ZeroablePrimitive, T: Conv<F> + ZeroablePrimitive> Conv<NonZero<F>> for NonZero<T> {
    #[inline]
    fn try_conv(n: NonZero<F>) -> Result<NonZero<T>> {
        let m: T = n.get().try_cast()?;
        Ok(if cfg!(debug_assertions) {
            NonZero::new(m).expect("should be non-zero")
        } else {
            // SAFETY: since cast() does not change the numeric value, m cannot be zero
            unsafe { NonZero::new_unchecked(m) }
        })
    }

    #[inline]
    fn conv(n: NonZero<F>) -> NonZero<T> {
        let m: T = n.get().cast();
        if cfg!(debug_assertions) {
            NonZero::new(m).expect("should be non-zero")
        } else {
            // SAFETY: since cast() does not change the numeric value, m cannot be zero
            unsafe { NonZero::new_unchecked(m) }
        }
    }
}
