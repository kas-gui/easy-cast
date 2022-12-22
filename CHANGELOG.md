Changelog
=========

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
