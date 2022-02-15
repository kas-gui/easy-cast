Easy-cast
=========

[![Test Status](https://github.com/kas-gui/easy-cast/workflows/Tests/badge.svg?event=push)](https://github.com/kas-gui/easy-cast/actions)
[![Docs](https://docs.rs/easy-cast/badge.svg)](https://docs.rs/easy-cast)

Type conversion, success expected

This library exists to make fallible numeric type conversions easy, without
resorting to the `as` keyword.

-   [`Conv`] is like [`From`], but supports fallible conversions
-   [`Cast`] is to [`Conv`] what [`Into`] is to [`From`]
-   [`ConvApprox`] and [`CastApprox`] support fallible, approximate conversion
-   [`ConvFloat`] and [`CastFloat`] are similar, providing precise control over rounding

If you are wondering "why not just use `as`", there are a few reasons:

-   integer conversions may silently truncate or sign-extend which does not
    preserve value
-   prior to Rust 1.45.0 float-to-int conversions were not fully defined;
    since this version they use saturating conversion (NaN converts to 0)
-   you want some assurance (at least in debug builds) that the conversion
    will preserve values correctly

Why might you *not* want to use this library?

-   You want saturating / truncating / other non-value-preserving conversion
-   You want to convert non-numeric types ([`From`] supports a lot more
    conversions than [`Conv`] does)!
-   You want a thoroughly tested library (we're not quite there yet)

### Error handling

All traits support two methods:

-   `try_*` methods return a `Result` and always fail if the correct
    conversion is not possible
-   other methods may panic or return incorrect results

In debug builds, methods not returning `Result` must panic on failure. As
with the overflow checks on Rust's standard integer arithmetic, this is
considered a tool for finding logic errors. In release builds, these methods
are permitted to return defined but incorrect results similar to the `as`
keyword.

If the `always_assert` feature flag is set, assertions will be turned on in
all builds. Some additional feature flags are available for finer-grained
control (see `Cargo.toml`).

### Performance

Performance is "good enough that it hasn't been a concern".

In debug builds and when `always_assert` is enabled, the priority is testing
but overhead should be small.

In release builds without `always_assert`, `conv*` methods should reduce to
`x as T` (with necessary additions for rounding).

### no_std support

When the crate's default features are disabled (and `std` is not enabled)
then the library supports `no_std`. In this case, [`ConvFloat`] and
[`CastFloat`] are only available if the `libm` optional dependency is
enabled.

[`From`]: https://doc.rust-lang.org/stable/std/convert/trait.From.html
[`Into`]: https://doc.rust-lang.org/stable/std/convert/trait.Into.html
[`TryFrom`]: https://doc.rust-lang.org/stable/std/convert/trait.TryFrom.html
[`TryInto`]: https://doc.rust-lang.org/stable/std/convert/trait.TryInto.html
[`Conv`]: https://docs.rs/easy-cast/latest/easy_cast/trait.Conv.html
[`Cast`]: https://docs.rs/easy-cast/latest/easy_cast/trait.Cast.html
[`Conv::try_conv`]: https://docs.rs/easy-cast/latest/easy_cast/trait.Conv.html#tymethod.try_conv
[`Conv::try_cast`]: https://docs.rs/easy-cast/latest/easy_cast/trait.Conv.html#tymethod.try_cast
[`ConvFloat`]: https://docs.rs/easy-cast/latest/easy_cast/trait.ConvFloat.html
[`CastFloat`]: https://docs.rs/easy-cast/latest/easy_cast/trait.CastFloat.html

## MSRV and no_std

The Minumum Supported Rust Version is 1.53.0 (`IntoIterator for [T; N]`).

By default, `std` support is required. With default features disabled `no_std`
is supported, but the `ConvFloat` and `CastFloat` traits are unavailable.
Enabling the `libm` feature will re-enable these traits.


Copyright and Licence
-------

The [COPYRIGHT](COPYRIGHT) file includes a list of contributors who claim
copyright on this project. This list may be incomplete; new contributors may
optionally add themselves to this list.

The easy-cast library is published under the terms of the Apache License, Version 2.0.
You may obtain a copy of this licence from the [LICENSE](LICENSE) file or on
the following webpage: <https://www.apache.org/licenses/LICENSE-2.0>
