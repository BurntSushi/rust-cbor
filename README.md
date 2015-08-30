This crate provides an implementation of [RFC
7049](https://tools.ietf.org/html/rfc7049), which specifies Concise Binary
Object Representation (CBOR). CBOR adopts and modestly builds on the *data
model* used by JSON, except the encoding is in binary form. Its primary goals
include a balance of implementation size, message size and extensibility.

[![Build status](https://api.travis-ci.org/BurntSushi/rust-cbor.png)](https://travis-ci.org/BurntSushi/rust-cbor)
[![](http://meritbadge.herokuapp.com/cbor)](https://crates.io/crates/cbor)

Dual-licensed under MIT or the [UNLICENSE](http://unlicense.org).


### Documentation

The API is fully documented with examples:
[http://burntsushi.net/rustdoc/cbor/](http://burntsushi.net/rustdoc/cbor/).


### Installation

This crate works with Cargo and is on
[crates.io](https://crates.io/crates/cbor). The package is regularly updated.
Add it to your `Cargo.toml` like so:

```toml
[dependencies]
cbor = "0.3"
```


### Example: simple type based encoding and decoding

In this crate, there is a `Decoder` and an `Encoder`. All reading and writing
of CBOR must go through one of these types.

The following shows how use those types to encode and decode a sequence of data
items:

```rust
extern crate cbor;

use cbor::{Decoder, Encoder};

fn main() {
    // The data we want to encode. Each element in the list is encoded as its
    // own separate top-level data item.
    let data = vec![('a', 1), ('b', 2), ('c', 3)];

    // Create an in memory encoder. Use `Encoder::from_writer` to write to
    // anything that implements `Writer`.
    let mut e = Encoder::from_memory();
    e.encode(&data).unwrap();

    // Create an in memory decoder. Use `Decoder::from_reader` to read from
    // anything that implements `Reader`.
    let mut d = Decoder::from_bytes(e.as_bytes());
    let items: Vec<(char, i32)> = d.decode().collect::<Result<_, _>>().unwrap();

    assert_eq!(items, data);
}
```

There are [more examples in the docs](http://burntsushi.net/rustdoc/cbor/).


### Status of implementation

The big thing missing at the moment is indefinite length encoding. It's easy
enough to implement, but I'm still trying to think of the best way to expose it
in the API.

Otherwise, all core CBOR features are implemented. There is support for tags,
but none of the tags in the IANA registry are implemented. It isn't clear to me
whether these implementations should appear in this crate or in others. Perhaps
this would be a good use of Cargo's optional features.

Finally, CBOR maps are only allowed to have Unicode string keys. This was
easiest to implement, but perhaps this restriction should be lifted in the
future.


### Benchmarks

Here are some very rough (and too simplistic) benchmarks that compare CBOR with
JSON. Absolute performance is pretty bad (sans CBOR encoding), but this should
at least give a good ballpark for relative performance with JSON:

```
test decode_medium_cbor   ... bench:  15525074 ns/iter (+/- 348424) = 25 MB/s
test decode_medium_json   ... bench:  18356213 ns/iter (+/- 620645) = 30 MB/s
test decode_small_cbor    ... bench:      1299 ns/iter (+/- 6) = 30 MB/s
test decode_small_json    ... bench:      1471 ns/iter (+/- 11) = 38 MB/s
test encode_medium_cbor   ... bench:   1379671 ns/iter (+/- 24828) = 289 MB/s
test encode_medium_json   ... bench:   8053979 ns/iter (+/- 110462) = 70 MB/s
test encode_medium_tojson ... bench:  15589704 ns/iter (+/- 559355) = 36 MB/s
test encode_small_cbor    ... bench:      2685 ns/iter (+/- 69) = 14 MB/s
test encode_small_json    ... bench:       862 ns/iter (+/- 1) = 64 MB/s
test encode_small_tojson  ... bench:      1313 ns/iter (+/- 6) = 42 MB/s
test read_medium_cbor     ... bench:  10008308 ns/iter (+/- 101995) = 39 MB/s
test read_medium_json     ... bench:  14853023 ns/iter (+/- 510215) = 38 MB/s
test read_small_cbor      ... bench:       763 ns/iter (+/- 4) = 52 MB/s
test read_small_json      ... bench:      1127 ns/iter (+/- 4) = 49 MB/s
```

If these benchmarks are perplexing to you, then you might want to check out
[Erick Tryzelaar's series of blog
posts](http://erickt.github.io/blog/2014/10/28/serialization/)
on Rust's serialization infrastructure. In short,
[it's being worked on](https://github.com/erickt/rust-serde).

Relatedly, a compounding reason why decoding CBOR is so slow is because it is
decoded into an intermediate abstract syntax first. A faster (but more complex)
implementation would skip this step, but it is difficult to do performantly
with the existing serialization infrastructure. (The same approach is used
in JSON decoding too, but it should be much easier to eschew this with CBOR
since it doesn't have the complexity overhead of parsing text.)


### Alternatives

[TyOverby's excellent `bincode`](https://github.com/TyOverby/bincode) library
fulfills a similar use case as `cbor`: both crates serialize and deserialize
between Rust values and a binary representation. Here is a brief comparison
(please ping me if I've gotten any of this wrong or if I've left out other
crucial details):

* CBOR is an IETF standard with implementations in
  [many languages](http://cbor.io/impls.html). This means you can use CBOR
  to easily communicate with programs written in other programming languages.
* `cbor` tags every data item encoded, including every number. `bincode` does
  not, which means the compactness of the resulting binary data depends on your
  data. For example, using `cbor`, encoding a `Vec<u64>` will encode every
  integer using a variable width encoding while `bincode` will use 8 bytes for
  every number. This results in various trade offs in terms of serialization
  speed, the size of the data and the flexibility of encoding/decoding with
  Rust types. (e.g., With `bincode` you must decode with precisely the same
  integer size as what was encoded, but `cbor` can adjust on the fly and
  decode, e.g., an encoded `u16` into a `u64`.)
