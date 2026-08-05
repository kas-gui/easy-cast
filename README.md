Easy-cast
=========

[![Test Status](https://github.com/kas-gui/easy-cast/workflows/Tests/badge.svg?event=push)](https://github.com/kas-gui/easy-cast/actions)
[![Docs](https://docs.rs/easy-cast/badge.svg)](https://docs.rs/easy-cast)

This library exists to make numeric type conversions **easy** and **generic** without resorting to the `as` keyword.

-   Use [`Cast`] and [`Conv`] instead of [`Into`] and [`From`] for exact conversions
-   Use [`CastApprox`] and [`ConvApprox`] for approximate conversions with implementation-defined rounding
-   Use [`CastTo`] and [`ConvTo`] for conversions with a specific [`Rounding`] mode

### Quick example

```rust
use easy_cast::{Cast, Conv, CastApprox, CastTo, Nearest};
let _: i32 = 15_usize.cast();           // exact conversion
let _ = usize::conv(20_u32);            // exact conversion
let _: f32 = u32::MAX.cast_approx();    // approximates to 2^32
let _: i32 = 11.9_f32.cast_to(Nearest); // rounds to 12
```

## Motivation

"Why not just use `as` / `.into()` / `.try_into()`", you ask?

-   You want some assurance that conversions will preserve values and not silently approximate, truncate, saturate or sign-extend like [`as` numeric casts]
-   You want simple `.cast()` syntax across all type conversions, not the inconsistent and incomplete mix that [`From`] and [`TryFrom`] provide
-   You want consistent `.cast_approx()` syntax across all type conversions
-   You want control over rounding: `.cast_to(Nearest)`, `.cast_to(Floor)` etc.
-   You want to use generics like `T: CastApprox<f64>`

Why might you *not* want to use this library?

-   You want saturating conversions (unimplemented)
-   You want non-numeric types ([`Into`] supports a lot more type conversions than [`Cast`] does)!

## Error handling and fallback behaviour

All traits provide two conversion methods; for example [`Cast`]:

-   `fn try_cast(self) -> Result<T, Self::Error>` for usage where error handling is required
-   `fn cast(self) -> T` for usage where success is expected

While the behaviour of `try_cast()` (and other `try_` methods) is obvious, `cast()` requires an explanation.

In debug builds, non-"try" methods like `cast()` must panic on failure. This is also the case if the `always_assert` feature flag is enabled (for this library's implementations).

Otherwise (in release builds without extra assertions enabled), more flexible behaviour is allowed: the implementations provided by `easy-cast` mostly reduce to [`as` numeric casts] (with rounding as required). This is designed to encourage usage of `.cast()` / `.conv(_)` instead of `_ as T` *even where you are pretty sure the conversion will succeed*.

## Features

### no_std support

The `std` feature is optional, enabled-by-default. Disabling it removes support for the `Floor`, `Ceil` and `Nearest` rounding modes.

The `libm` feature may be used instead of `std` to re-enable support for `Floor`, `Ceil` and `Nearest`.

[`From`]: https://doc.rust-lang.org/stable/std/convert/trait.From.html
[`Into`]: https://doc.rust-lang.org/stable/std/convert/trait.Into.html
[`TryFrom`]: https://doc.rust-lang.org/stable/std/convert/trait.TryFrom.html
[`TryInto`]: https://doc.rust-lang.org/stable/std/convert/trait.TryInto.html
[`Conv`]: https://docs.rs/easy-cast/latest/easy_cast/trait.Conv.html
[`Cast`]: https://docs.rs/easy-cast/latest/easy_cast/trait.Cast.html
[`Conv::try_conv`]: https://docs.rs/easy-cast/latest/easy_cast/trait.Conv.html#tymethod.try_conv
[`Conv::try_cast`]: https://docs.rs/easy-cast/latest/easy_cast/trait.Conv.html#tymethod.try_cast
[`ConvApprox`]: https://docs.rs/easy-cast/latest/easy_cast/trait.ConvApprox.html
[`CastApprox`]: https://docs.rs/easy-cast/latest/easy_cast/trait.CastApprox.html
[`ConvTo`]: https://docs.rs/easy-cast/latest/easy_cast/trait.ConvTo.html
[`CastTo`]: https://docs.rs/easy-cast/latest/easy_cast/trait.CastTo.html
[`Rounding`]: https://docs.rs/easy-cast/latest/easy_cast/trait.Rounding.html
[`as` numeric casts]: https://doc.rust-lang.org/reference/expressions/operator-expr.html#r-expr.as.numeric


Copyright and Licence
-------

The [COPYRIGHT](COPYRIGHT) file includes a list of contributors who claim
copyright on this project. This list may be incomplete; new contributors may
optionally add themselves to this list.

The easy-cast library is published under the terms of the Apache License, Version 2.0.
You may obtain a copy of this licence from the [LICENSE](LICENSE) file or on
the following webpage: <https://www.apache.org/licenses/LICENSE-2.0>
