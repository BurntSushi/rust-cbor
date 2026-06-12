# cbor_conv

Command line tools for converting between CBOR and JSON, built on the
[`cbor`](https://crates.io/crates/cbor) crate.

* `json2cbor` reads a stream of JSON values on stdin and writes each as a
  CBOR item to stdout.
* `cbor2json` reads a stream of CBOR items on stdin and writes each as a
  pretty-printed JSON value to stdout. Byte strings become hex strings,
  non-string map keys are JSON-encoded into strings, non-finite floats
  become null and tags are dropped (keeping the inner value).

```bash
$ echo '{"name": "example", "ok": true}' | json2cbor | cbor2json
{
  "name": "example",
  "ok": true
}
```
