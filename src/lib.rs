/*!
This crate provides an implementation of [RFC
8949](https://www.rfc-editor.org/rfc/rfc8949) — the Concise Binary Object
Representation (CBOR) — built on [serde](https://serde.rs).

CBOR adopts and modestly builds on the *data model* used by JSON, except the
encoding is in binary form. Its primary goals include a balance of
implementation size, message size and extensibility.

# Quick start

Use [`to_vec`]/[`to_writer`] to encode any [`serde::Serialize`] type and
[`from_slice`]/[`from_reader`] to decode any [`serde::Deserialize`] type:

```rust
use serde::{Deserialize, Serialize};

#[derive(Debug, PartialEq, Deserialize, Serialize)]
struct Photo {
    title: String,
    pixels: (u32, u32),
    tags: Vec<String>,
}

let photo = Photo {
    title: "Sunrise".into(),
    pixels: (1920, 1080),
    tags: vec!["morning".into(), "gradient".into()],
};

let bytes = cbor::to_vec(&photo).unwrap();
let back: Photo = cbor::from_slice(&bytes).unwrap();
assert_eq!(photo, back);
```

# Dynamic values

When the shape of the data is not known in advance, decode into a
[`Value`], the CBOR equivalent of `serde_json::Value`. The [`cbor!`] macro
builds `Value`s with a JSON-like syntax:

```rust
use cbor::{cbor, Value};

let value = cbor!({
    "code" => 415,
    "message" => null,
    "tags" => ["legacy", 1.5],
}).unwrap();

let bytes = cbor::to_vec(&value).unwrap();
let back: Value = cbor::from_slice(&bytes).unwrap();
assert_eq!(value, back);
```

`Value::serialized` and `Value::deserialized` convert between `Value` and
any type implementing the serde traits.

# Tags

CBOR data items can be wrapped in semantic [tags](tag) (RFC 8949 §3.4). The
wrapper types in the [`tag`] module capture and emit tags through serde:

```rust
use cbor::tag::RequireExact;

// Tag 32: a URI.
type Uri = RequireExact<String, 32>;

let uri: Uri = RequireExact("https://example.com".into());
let bytes = cbor::to_vec(&uri).unwrap();
assert_eq!(bytes[0], 0xd8); // tag(32)
```

# Allocation-free helpers

Two helpers inspect data without building it: [`validate`] checks that an
input is exactly one well-formed CBOR item (including text UTF-8 validity),
and [`serialized_size`] computes the exact encoded size of any
serializable value. Neither allocates heap memory.

```rust
let value = ("hello", vec![1u8, 2, 3]);
let bytes = cbor::to_vec(&value).unwrap();

assert_eq!(cbor::serialized_size(&value).unwrap(), bytes.len() as u64);
assert!(cbor::validate(&bytes[..]).is_ok());
assert!(cbor::validate(&bytes[..bytes.len() - 1]).is_err()); // truncated
```

# Diagnostic notation

[`diagnostic`] renders raw CBOR as the human-readable text form of
RFC 8949 §8 — handy for logs and debugging. Working on the wire, it can
show what a [`Value`] cannot represent: indefinite-length markers,
`undefined`, and unassigned simple values. `Value` implements
[`Display`](std::fmt::Display) with the same notation, and
[`Debug`](std::fmt::Debug) pretty-prints it with two-space indentation.

```rust
let bytes = hex::decode("bf61610161629f0203ffff").unwrap();
assert_eq!(
    cbor::diagnostic(&bytes[..]).unwrap(),
    r#"{_ "a": 1, "b": [_ 2, 3]}"#
);

let value = cbor::cbor!({ "k" => [1, -2.5, null] }).unwrap();
assert_eq!(value.to_string(), r#"{"k": [1, -2.5, null]}"#);
```

# Deterministic encoding

[`to_canonical_vec`]/[`to_canonical_writer`] produce output satisfying the
core deterministic encoding requirements of RFC 8949 §4.2.1: preferred
(smallest) serializations, definite lengths only, and map keys sorted in the
bytewise lexicographic order of their encodings. [`Value::canonicalize`]
applies the same normalization to a `Value` in place.

```rust
use std::collections::HashMap;

// HashMap iteration order is random, but the encoding is stable.
let map: HashMap<&str, i32> = [("z", 1), ("aa", 2), ("b", 3)].into();

let bytes = cbor::to_canonical_vec(&map).unwrap();
assert_eq!(bytes, cbor::to_canonical_vec(&map).unwrap());
assert_eq!(hex::encode(&bytes), "a3616203617a01626161 02".replace(' ', ""));
```

Many existing protocols instead use the older "Canonical CBOR" key order of
RFC 7049 §3.9 (kept as RFC 8949 §4.2.3), where shorter encoded keys sort
first. Pass [`KeyOrder::LengthFirst`] to the `*_with` variants for that:

```rust
use cbor::KeyOrder;

let map: std::collections::HashMap<i64, bool> = [(100, true), (-1, false)].into();

// Bytewise (RFC 8949 §4.2.1): 100 (0x1864) sorts before -1 (0x20).
let core = cbor::to_canonical_vec(&map).unwrap();
assert_eq!(hex::encode(&core), "a2 1864f5 20f4".replace(' ', ""));

// Length-first (RFC 7049 §3.9): -1 sorts before 100.
let legacy = cbor::to_canonical_vec_with(&map, KeyOrder::LengthFirst).unwrap();
assert_eq!(hex::encode(&legacy), "a2 20f4 1864f5".replace(' ', ""));
```

# Design decisions

This implementation is wire-compatible with
[`ciborium`](https://docs.rs/ciborium), whose design it follows:

* **Numbers are always encoded in their smallest lossless form**, as
  deterministic encoding (RFC 8949 §4.2.1) requires. Integer width in Rust
  is treated as an in-memory detail, not a wire property: `1u64` encodes as
  one byte, and that byte happily decodes into a `u128` or an `i8`.
* **`u128`/`i128` values outside the 64-bit range** are encoded as bignums
  (tags 2 and 3), and bignums small enough to fit are accepted for any
  integer type.
* **Maps are represented as `Vec<(Value, Value)>`** in [`Value`], preserving
  wire order and arbitrary (even duplicate) keys.
* **Be liberal in what you accept**: decoding handles indefinite-length
  items, segmented strings, half-width floats, leading zeros in bignums and
  unknown tags in most positions, even though encoding never produces most
  of those forms.
* **Deeply nested input fails with
  [`RecursionLimitExceeded`](de::Error::RecursionLimitExceeded)** instead of
  exhausting the stack; see [`de::Deserializer::with_recursion_limit`].

# History

`cbor` 0.4 and earlier (by Andrew Gallant) were built on the long-deprecated
`rustc-serialize` framework and predate both serde 1.0 and RFC 8949. Version
0.5 is a from-scratch rewrite; none of the old API survives.
*/

#![deny(missing_docs)]
#![forbid(unsafe_code)]

pub mod core;
pub mod de;
mod diag;
pub mod ser;
pub mod tag;
pub mod value;

#[doc(inline)]
pub use crate::de::{from_reader, from_slice, validate};
pub use crate::diag::diagnostic;
#[doc(inline)]
pub use crate::ser::{
    serialized_size, to_canonical_vec, to_canonical_vec_with, to_canonical_writer,
    to_canonical_writer_with, to_vec, to_writer,
};
#[doc(inline)]
pub use crate::value::{KeyOrder, Value};

/// Builds a [`Value`] from JSON-like syntax.
///
/// Maps use `=>` between keys and values; any expression implementing
/// [`serde::Serialize`] can be inlined, including nested `cbor!` maps and
/// arrays. The macro returns `Result<Value, value::Error>`.
///
/// ```rust
/// use cbor::cbor;
///
/// let value = cbor!({
///     "code" => 415,
///     "message" => null,
///     "continue" => false,
///     "extra" => { "numbers" => [8.2341e+4, 0.251425] },
/// }).unwrap();
/// ```
#[macro_export]
macro_rules! cbor {
    (@map {$($key:expr => $val:expr),*} $(,)?) => {{
        $crate::value::Value::Map(vec![
            $(
                ($crate::cbor!( $key )?, $crate::cbor!( $val )?)
            ),*
        ])
    }};

    (@map {$($key:expr => $val:expr),*} { $($nkey:tt)* } => $($next:tt)*) => {
        $crate::cbor!(
            @map
            { $($key => $val),* }
            $crate::cbor!({ $($nkey)* })? =>
            $($next)*
        )
    };

    (@map {$($key:expr => $val:expr),*} [ $($nkey:tt)* ] => $($next:tt)*) => {
        $crate::cbor!(
            @map
            { $($key => $val),* }
            $crate::cbor!([ $($nkey)* ])? =>
            $($next)*
        )
    };

    (@map {$($key:expr => $val:expr),*} $nkey:expr => { $($nval:tt)* }, $($next:tt)*) => {
        $crate::cbor!(
            @map
            { $($key => $val,)* $nkey => $crate::cbor!({ $($nval)* })? }
            $($next)*
        )
    };

    (@map {$($key:expr => $val:expr),*} $nkey:expr => [ $($nval:tt)* ], $($next:tt)*) => {
        $crate::cbor!(
            @map
            { $($key => $val,)* $nkey => $crate::cbor!([ $($nval)* ])? }
            $($next)*
        )
    };

    (@map {$($key:expr => $val:expr),*} $nkey:expr => $nval:expr, $($next:tt)*) => {
        $crate::cbor!(
            @map
            { $($key => $val,)* $nkey => $crate::cbor!($nval)? }
            $($next)*
        )
    };

    (@seq [$($val:expr),*] $(,)?) => {
        $crate::value::Value::Array(
            vec![$( $crate::cbor!($val)? ),*]
        )
    };

    (@seq [$($val:expr),*] { $($item:tt)* }, $($next:tt)*) => {
        $crate::cbor!(
            @seq
            [ $($val,)* $crate::cbor!({ $($item)* })? ]
            $($next)*
        )
    };

    (@seq [$($val:expr),*] [ $($item:tt)* ], $($next:tt)*) => {
        $crate::cbor!(
            @seq
            [ $($val,)* $crate::cbor!([ $($item)* ])? ]
            $($next)*
        )
    };

    (@seq [$($val:expr),*] $item:expr, $($next:tt)*) => {
        $crate::cbor!(
            @seq
            [ $($val,)* $item ]
            $($next)*
        )
    };

    ({ $($next:tt)* }) => {(|| {
        ::core::result::Result::<_, $crate::value::Error>::Ok($crate::cbor!(@map {} $($next)* ,))
    })()};

    ([ $($next:tt)* ]) => {(|| {
        ::core::result::Result::<_, $crate::value::Error>::Ok($crate::cbor!(@seq [] $($next)* ,))
    })()};

    ($val:expr) => {{
        #[allow(unused_imports)]
        use $crate::value::Value::Null as null;
        $crate::value::Value::serialized(&$val)
    }};
}
