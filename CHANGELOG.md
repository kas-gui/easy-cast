Changelog
=========

## [0.7.0] — 2026-08-05

This version is a substantial revision of `easy-cast`, introducing generics over rounding modes via the new `Rounding` trait.

Simple usage via the `Conv`, `Cast`, `ConvApprox` and `CastApprox` traits is largely unchanged. Usage with other rounding modes should be moved to the new `ConvTo` and `CastTo` traits (e.g. `i32::conv_to(Nearest, 5.3)`, `x.cast_to(Floor)`).

External implementations of conversions should be moved to the `ConvExact` and `ConvTo` traits.

Added:

-   `Rounding` trait with `Exact`, `Approx` rounding modes (#58)
-   `Trunc`, `Nearest`, `Floor`, `Ceil` rounding modes (#61)
-   `ConvExact` trait as an implementation helper for conversions which are never inexact (#58, #65)
-   `ConvTo` trait for implementation and usage of conversions with a specific rounding mode (#58, #60, #63, #65)
-   `CastTo` trait for casting with a specific rounding mode (#58, #60, #63)
-   `RangeError` as a new error type (#56)

Changed:

-   Added an associated `Error` type to the `Conv` and `Cast` traits (#62)
-   Rename `impl_via_trivial!` to `impl_via_identity!` (#68)
-   Implement `Exact` `f64 → f32` conversion (#59)
-   Implement `Approx` and `Nearest` int-to-float conversions (#59, #63)
-   `u128::MAX` and other too-large values no longer coerce to `f32::INFINITY` under `Exact` rounding, as used by `Conv` and `Cast` (#67)
-   Truncating-conversions (`Trunc`) no longer require the `std` or `libm` feature (#66)
-   Implement `core::error::Error` on no-std (#57)
-   Enabled the `doc_cfg` feature (#66)

Removed:

-   `Result` type-def (#56)
-   `ConvFloat`, `CastFloat` traits; this functionality remains available through the new rounding modes (#61)

## [0.6.1] — 2026-07-24

Added:

-   Add pub macros `impl_via_from!`, `impl_via_trivial!` (#54)

## [0.6.0] — 2026-07-21

Fixed:

-   Fix `unsafe` code in `NonZero` conversion on input values which wrap to zero (#52)
-   Fix: allow overflow of large `u128` values to `f32::INFINITY` (#51)

Changed:

-   Adjust `ConvApprox<f64> for f32` to behave more like `*_f64 as f32`:
    too-large values round to infinity (instead of a range error) and rounding
    uses `roundTiesToEven`. Unlike `as f32`, NAN still yields
    `Err(Error::Range)`. (#47)
-   Change `Conv<f32> for f64` to trap NAN (#48)

Removed:

-   Remove support for `Saturating`, `Wrapping` (#49)
-   Remove `assert_nonzero` feature flag (#52)

## [0.5.5] — 2026-07-08

-   Bump MSRV to 1.96.0 and use Edition 2024 (#44)
-   Support `std::range` types (#44)

## [0.5.4] — 2025-11-20

-   Bump MSRV to 1.79.0
-   Support `Conv`, `Cast` for `core::ops::Range` and other range types (#38)
-   Support `Conv`, `Cast` for `core::num::{Saturating, Wrapping}` (#38)
-   Support `Conv`, `Cast` for `core::num::NonZero` (#39)

## [0.5.3] — 2024-12-12

-   Bump MSRV to 1.60.0 and use Edition 2021 (#30)

## [0.5.2] — 2022-12-22

-   Support cast to self, useful in generics (#28)

## [0.5.1] — 2022-10-14

-   Document feature assert_digits and imply by always_assert (#26)

## [0.5.0] — 2022-08-19

-   Reorganise code (#20)
-   Bump MSRV to 1.53.0 (#21)
-   Add default implementations of `conv` methods over equivalent `try_conv`
    variant to facilitate custom implementations (#21)
-   Add `ConvApprox` and `CastApprox`, supporting approximate conversions
    with unspecified rounding, implemented for `f64 → f32` and all type
    conversions supported by `Conv` (#21)
-   Support `Conv` and `ConvFloat` for arrays and tuples (#21)
-   Remove `impl<T> Conv<T> for T` (#21)
-   Add `easy_cast::Result` type alias (#22)
-   Move traits into new `easy_cast::traits` public module (#23)

## [0.4.4] — 2021-04-12

-   Fix negative int to float digits check (#18)

## [0.4.3] — 2021-04-12

-   Unify some macros via `impl_int_generic` (#16)
-   Improve error messages in asserts (#17)

## [0.4.2] — 2021-04-03

-   Fix `i16::conv(1usize)` (#15)
-   Update README (#15)

## [0.4.1] — 2021-04-01

-   Fix `conv(0)` from int to float (#14)

## [0.4.0] — 2021-04-01

-   Add `try_conv` and `try_cast` methods (#12)
-   Add `try_conv_nearest` etc. (#12)
-   Removed `Conv<f64> for f32` (#12)
-   Replaced `assert_range` and `assert_non_neg` with `assert_int` (#12)
-   MSRV is 1.32.0 (#12)

## [0.3.0] — 2021-03-29

-   Add `conv_trunc` / `cast_trunc` (#11)
-   Explicitly support Rust 1.36.0 (and potentially older; #10)
-   Support `no_std` (#10)
-   Fix rounding for `floor` on negative values (#10)

## [0.2.0] — 2021-03-20

-   Add feature flags controlling assert behaviour
-   Remove restrictions on isize/usize (#6)
-   Fix bad revert checks (#6)
