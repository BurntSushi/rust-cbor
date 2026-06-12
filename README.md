# cbor

A serde implementation of [RFC 8949](https://www.rfc-editor.org/rfc/rfc8949)
— the Concise Binary Object Representation (CBOR) — for Rust.

[![CI](https://github.com/ldclabs/rust-cbor/actions/workflows/ci.yml/badge.svg)](https://github.com/ldclabs/rust-cbor/actions/workflows/ci.yml)
[![crates.io](https://img.shields.io/crates/v/cbor.svg)](https://crates.io/crates/cbor)
[![docs.rs](https://docs.rs/cbor/badge.svg)](https://docs.rs/cbor)

CBOR adopts and modestly builds on the *data model* used by JSON, except the
encoding is in binary form. Its primary goals include a balance of
implementation size, message size and extensibility.

Dual-licensed under MIT or the [UNLICENSE](http://unlicense.org).

## Status

This crate was created by [Andrew Gallant](https://github.com/BurntSushi) in
2015 and built on the pre-serde `rustc-serialize` framework; it went
unmaintained for many years. Version 0.5 is a from-scratch rewrite on top of
[serde](https://serde.rs), now maintained by [LDC Labs](https://github.com/ldclabs).
None of the 0.4 API survives.

The rewrite follows the design of (and is wire-compatible with)
[ciborium](https://github.com/enarx/ciborium) — many thanks to its authors.
If you need `no_std` support today, use ciborium; this crate currently
requires `std`.

## Features

* **Full serde integration** — `#[derive(Serialize, Deserialize)]` types
  encode and decode directly.
* **RFC 8949 preferred serialization** — integers and floats are always
  encoded in their smallest lossless form, including half-precision floats.
* **A dynamic [`Value`] type** — the CBOR analogue of `serde_json::Value`,
  with a `cbor!` macro for building values in JSON-like syntax.
* **Tag support** — capture and emit semantic tags (RFC 8949 §3.4) through
  the wrapper types in the `tag` module; `u128`/`i128` map to bignum tags
  automatically.
* **Deterministic encoding** — `to_canonical_vec`/`to_canonical_writer` and
  `Value::canonicalize` implement the core deterministic encoding
  requirements (RFC 8949 §4.2.1): bytewise lexicographic map key order,
  definite lengths, preferred serializations, normalized bignums and NaN.
  For protocols built on the older RFC 7049 §3.9 "Canonical CBOR" rule
  (kept as RFC 8949 §4.2.3, and used by ciborium's canonical module), the
  `*_with` variants take `KeyOrder::LengthFirst`.
* **Robust decoding** — indefinite-length items, segmented strings,
  duplicate map keys, unknown tags and CBOR sequences (RFC 8742) are all
  handled; recursion is depth-limited and forged lengths cannot trigger
  huge allocations.
* **A low-level header codec** — the `core` module exposes the pull/push
  `Header` interface for applications that need precise wire control.

## Usage

```toml
[dependencies]
cbor = "0.5"
```

### Type-based encoding and decoding

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

`to_writer` and `from_reader` work with any `std::io::Write`/`Read`, and
`Deserializer::into_iter` decodes a stream of concatenated items.

### Dynamic values

```rust
use cbor::{cbor, Value};

let value = cbor!({
    "code" => 415,
    "message" => null,
    "extra" => { "numbers" => [8.2341e+4, 0.251425] },
}).unwrap();

let bytes = cbor::to_vec(&value).unwrap();
let back: Value = cbor::from_slice(&bytes).unwrap();
assert_eq!(value, back);
```

### Tags

```rust
use cbor::tag::RequireExact;

// Tag 0: standard date/time string.
let datetime = RequireExact::<String, 0>("2013-03-21T20:04:00Z".into());
let bytes = cbor::to_vec(&datetime).unwrap();
assert_eq!(bytes[0], 0xc0);
```

## Design decisions

This implementation deliberately matches ciborium's wire behavior, so the
two crates interoperate byte for byte:

* Numbers always encode in their smallest lossless form, as deterministic
  encoding (RFC 8949 §4.2.1) requires. Integer width in Rust is treated as
  an in-memory detail, not a wire property.
* Enums encode as a bare string (unit variants) or a single-entry map
  `{variant: payload}` (everything else).
* `Value` maps are `Vec<(Value, Value)>`, preserving wire order and
  arbitrary keys.
* Decoding follows the robustness principle: indefinite lengths, segmented
  strings, half-width floats and unknown tags are accepted even though
  encoding never produces them.

## Command line tools

The workspace ships two small converters in `cbor_conv`:

```bash
$ echo '{"name": "example", "ok": true}' | json2cbor | cbor2json
{
  "name": "example",
  "ok": true
}
```

## Roadmap

* `no_std` + `alloc` support
* Benchmarks against other CBOR implementations

## Testing

`cargo test` runs the unit tests, a single integration-test binary and the
doc tests — including the RFC 8949 Appendix A vectors and fault-injection
tests for I/O failures and malformed input. Line coverage of the library is
100% (measured with `cargo llvm-cov`); the only never-executed regions are
five error branches that are unreachable on 64-bit targets or guard
conditions that cannot occur.

## Minimum supported Rust version

Rust 1.85.

## License

Dual-licensed under MIT or the [UNLICENSE](http://unlicense.org), like the
original crate.
