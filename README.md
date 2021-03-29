Easy-cast
=========

[![Test Status](https://github.com/kas-gui/easy-cast/workflows/Tests/badge.svg?event=push)](https://github.com/kas-gui/easy-cast/actions)
[![Docs](https://docs.rs/easy-cast/badge.svg)](https://docs.rs/easy-cast)

Type conversion, success expected

Use the `Conv` and `Cast` traits when:

-   `From` and `Into` are not enough
-   it is expected that the value can be represented exactly by the target type
-   you could use `as`, but want some assurance it's doing the right thing
-   you are converting numbers (future versions *might* consider supporting
    other conversions)

Use the `ConvFloat` and `CastFloat` traits when:

-   You are converting from `f32` or `f64`
-   You specifically want the nearest or ceiling or floor, but don't need
    detailed control over rounding (e.g. round-to-even)

## Assertions

All type conversions which are potentially fallible assert on failure in
debug builds. In release builds assertions may be omitted, thus making
incorrect conversions possible.

If the `always_assert` feature flag is set, assertions will be turned on in
all builds. Some additional feature flags are available for finer-grained
control (see [Cargo.toml](Cargo.toml)).

## MSRV and no_std

The Minumum Supported Rust Version is 1.36.0 (older versions may work but are
untested).

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
