Changelog
=========

## [0.4.1] — 2021-04-01

-   Fix `conv(0)` from int to float

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
