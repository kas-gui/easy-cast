Easy-cast
=========

[![Test Status](https://github.com/kas-gui/easy-cast/workflows/Tests/badge.svg?event=push)](https://github.com/kas-gui/easy-cast/actions)
[![Docs](https://docs.rs/easy-cast/badge.svg)](https://docs.rs/easy-cast)

Type conversion, success expected

This library is written to make numeric type conversions easy. Such
conversions usually fall into one of the following cases:

-   the conversion must preserve values exactly (use [`From`] or [`Into`]
    or [`Conv`] or [`Cast`])
-   the conversion is expected to preserve values exactly, though this is
    not ensured by the types in question (use [`Conv`] or [`Cast`])
-   the conversion could fail and must be checked at run-time (use
    [`TryFrom`] or [`TryInto`] or [`Conv::try_conv`] or [`Cast::try_cast`])
-   the conversion is from floating point values to integers and should
    round to the "nearest" integer (use [`ConvFloat`] or [`CastFloat`])
-   the conversion is from `f32` to `f64` or vice-versa; in this case use of
    `as f32` / `as f64` is likely acceptable since `f32` has special
    representations for non-finite values and conversion to `f64` is exact
-   truncating conversion (modular arithmetic) is desired; in this case `as`
    probably does exactly what you want
-   saturating conversion is desired (less common; not supported here)

If you are wondering "why not just use `as`", there are a few reasons:

-   integer conversions may silently truncate
-   integer conversions to/from signed types silently reinterpret
-   prior to Rust 1.45.0 float-to-int conversions were not fully defined;
    since this version they use saturating conversion (NaN converts to 0)
-   you want some assurance (at least in debug builds) that the conversion
    will preserve values correctly without having to proof-read code

When should you *not* use this library?

-   Only numeric conversions are supported
-   Conversions from floats do not provide fine control of rounding modes
-   This library has not been thoroughly tested correctness

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

## Assertions

All type conversions which are potentially fallible assert on failure in
debug builds. In release builds assertions may be omitted, thus making
incorrect conversions possible.

If the `always_assert` feature flag is set, assertions will be turned on in
all builds. Some additional feature flags are available for finer-grained
control (see [Cargo.toml](Cargo.toml)).

## MSRV and no_std

The Minumum Supported Rust Version is 1.32.0 (first release of Edition 2018).

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
