//! Tests for error types, error plumbing and I/O failure paths.

use std::io::{self, Read, Write};

use serde::{Deserialize, Serialize};

struct FailWriter;

impl Write for FailWriter {
    fn write(&mut self, _: &[u8]) -> io::Result<usize> {
        Err(io::Error::other("sink broke"))
    }

    fn flush(&mut self) -> io::Result<()> {
        Err(io::Error::other("flush broke"))
    }
}

struct FailReader;

impl Read for FailReader {
    fn read(&mut self, _: &mut [u8]) -> io::Result<usize> {
        Err(io::Error::other("source broke"))
    }
}

// A type whose Serialize implementation always fails.
struct Unserializable;

impl Serialize for Unserializable {
    fn serialize<S: serde::Serializer>(&self, _: S) -> Result<S::Ok, S::Error> {
        Err(serde::ser::Error::custom("boom"))
    }
}

#[test]
fn ser_io_error() {
    let err = cbor::to_writer(&1u8, FailWriter).unwrap_err();
    assert!(matches!(err, cbor::ser::Error::Io(..)));
    assert!(err.to_string().contains("i/o error"));
    assert!(std::error::Error::source(&err).is_some());
}

#[test]
fn ser_value_error() {
    let err = cbor::to_vec(&Unserializable).unwrap_err();
    assert!(matches!(err, cbor::ser::Error::Value(..)));
    assert_eq!(err.to_string(), "value error: boom");
    assert!(std::error::Error::source(&err).is_none());
    assert!(format!("{err:?}").contains("Value"));

    // The canonical entry points surface the same failure.
    let err = cbor::to_canonical_vec(&Unserializable).unwrap_err();
    assert!(matches!(err, cbor::ser::Error::Value(..)));
}

#[test]
fn ser_from_io_error() {
    let err = cbor::ser::Error::from(io::Error::other("x"));
    assert!(matches!(err, cbor::ser::Error::Io(..)));
}

#[test]
fn serializer_from_encoder() {
    let mut buffer = Vec::new();
    let encoder = cbor::core::Encoder::from(&mut buffer);
    let mut serializer = cbor::ser::Serializer::from(encoder);
    7u8.serialize(&mut serializer).unwrap();
    assert_eq!(buffer, [0x07]);
}

#[test]
fn de_io_error() {
    let err = cbor::from_reader::<cbor::Value, _>(FailReader).unwrap_err();
    assert!(matches!(err, cbor::de::Error::Io(..)));
    assert!(err.to_string().contains("i/o error"));
    assert!(std::error::Error::source(&err).is_some());

    // A body shorter than its header claims is also an I/O error.
    let err = cbor::from_slice::<char>(&[0x61]).unwrap_err();
    assert!(matches!(err, cbor::de::Error::Io(..)));
}

#[test]
fn de_error_api() {
    use cbor::de::Error;

    assert_eq!(
        Error::semantic(2, "boom").to_string(),
        "semantic error at offset 2: boom"
    );
    assert_eq!(
        Error::semantic(None, "boom").to_string(),
        "semantic error: boom"
    );
    assert_eq!(Error::Syntax(7).to_string(), "syntax error at offset 7");
    assert_eq!(
        Error::RecursionLimitExceeded.to_string(),
        "recursion limit exceeded"
    );
    assert!(std::error::Error::source(&Error::Syntax(7)).is_none());

    let err = Error::from(io::Error::other("x"));
    assert!(matches!(err, Error::Io(..)));

    let err = Error::from(cbor::core::Error::Io(io::Error::other("x")));
    assert!(matches!(err, Error::Io(..)));
    let err = Error::from(cbor::core::Error::Syntax(3));
    assert!(matches!(err, Error::Syntax(3)));

    let err = <Error as serde::de::Error>::custom("boom");
    assert!(matches!(&err, Error::Semantic(None, m) if m == "boom"));
    assert!(format!("{err:?}").contains("Semantic"));
}

#[test]
fn core_error_api() {
    use cbor::core::Error;

    let err = Error::Io(io::Error::other("x"));
    assert!(err.to_string().contains("i/o error"));
    assert!(std::error::Error::source(&err).is_some());

    let err = Error::Syntax(5);
    assert_eq!(err.to_string(), "syntax error at offset 5");
    assert!(std::error::Error::source(&err).is_none());
    assert!(format!("{err:?}").contains("Syntax"));
}

#[test]
fn value_error_api() {
    use cbor::value::Error;

    let err = <Error as serde::ser::Error>::custom("boom");
    assert_eq!(err.to_string(), "boom");
    let err = <Error as serde::de::Error>::custom("boom");
    assert_eq!(err.to_string(), "boom");
    assert!(std::error::Error::source(&err).is_none());
    assert!(format!("{}", err.clone()).contains("boom"));
}

#[test]
fn encoder_helpers() {
    let mut buffer = Vec::new();
    let mut encoder = cbor::core::Encoder::from(&mut buffer);
    encoder.push(cbor::core::Header::Bytes(Some(2))).unwrap();
    encoder.write_all(b"hi").unwrap();
    encoder.flush().unwrap();
    assert_eq!(buffer, b"\x42hi");

    // Reserved simple values 24-31 encode to a two-byte form that any
    // conforming decoder rejects (RFC 8949 §3.3).
    let mut buffer = Vec::new();
    cbor::core::Encoder::from(&mut buffer)
        .push(cbor::core::Header::Simple(30))
        .unwrap();
    assert_eq!(buffer, [0xf8, 30]);
    assert!(matches!(
        cbor::from_slice::<cbor::Value>(&buffer),
        Err(cbor::de::Error::Syntax(0))
    ));
}

#[test]
fn bodies_larger_than_one_chunk() {
    // Bodies are read in 16 KiB chunks; cover the multi-chunk loop.
    let bytes = serde_bytes::ByteBuf::from(vec![0xabu8; 40_000]);
    let encoded = cbor::to_vec(&bytes).unwrap();
    let back: serde_bytes::ByteBuf = cbor::from_slice(&encoded).unwrap();
    assert_eq!(back, bytes);

    let text = "雨".repeat(20_000);
    let encoded = cbor::to_vec(&text).unwrap();
    let back: String = cbor::from_slice(&encoded).unwrap();
    assert_eq!(back, text);
}

#[derive(Debug, PartialEq, Deserialize, Serialize)]
struct Probe(u8);

#[test]
fn deserializer_offset() {
    let bytes = cbor::to_vec(&(1u64, "ab")).unwrap();
    let mut de = cbor::de::Deserializer::from_reader(&bytes[..]);
    assert_eq!(de.offset(), 0);
    let _: (u64, String) = serde::Deserialize::deserialize(&mut de).unwrap();
    assert_eq!(de.offset(), bytes.len());
}

#[test]
fn ser_io_error_in_every_integer_shape() {
    // Each scalar serializer propagates a writer failure.
    assert!(matches!(
        cbor::to_writer(&true, FailWriter),
        Err(cbor::ser::Error::Io(..))
    ));
    assert!(matches!(
        cbor::to_writer(&-1i64, FailWriter),
        Err(cbor::ser::Error::Io(..))
    ));
    assert!(matches!(
        cbor::to_writer(&7i64, FailWriter),
        Err(cbor::ser::Error::Io(..))
    ));
    assert!(matches!(
        cbor::to_writer(&2i128, FailWriter),
        Err(cbor::ser::Error::Io(..))
    ));
    assert!(matches!(
        cbor::to_writer(&-2i128, FailWriter),
        Err(cbor::ser::Error::Io(..))
    ));
    assert!(matches!(
        cbor::to_writer(&1.5f64, FailWriter),
        Err(cbor::ser::Error::Io(..))
    ));
}

#[test]
fn to_canonical_writer_works() {
    let mut buffer = Vec::new();
    cbor::to_canonical_writer(&1u8, &mut buffer).unwrap();
    assert_eq!(buffer, [0x01]);
}

// A writer that accepts a fixed number of bytes and then fails, to inject
// failures at precise positions inside an item.
struct LimitedWriter {
    left: usize,
}

impl Write for LimitedWriter {
    fn write(&mut self, data: &[u8]) -> io::Result<usize> {
        if self.left == 0 {
            return Err(io::Error::other("limit reached"));
        }
        let n = self.left.min(data.len());
        self.left -= n;
        Ok(n)
    }

    fn flush(&mut self) -> io::Result<()> {
        Ok(())
    }
}

#[derive(Serialize)]
enum EveryShape {
    Unit,
    Newtype(u32),
    Tuple(u32, u32),
    Struct { x: u32 },
}

#[test]
fn writer_failures_propagate_from_every_shape() {
    fn fails<T: Serialize>(value: &T) {
        assert!(matches!(
            cbor::to_writer(value, FailWriter),
            Err(cbor::ser::Error::Io(..))
        ));
    }

    fails(&"text");
    fails(&'x');
    fails(&serde_bytes::ByteBuf::from(vec![1u8]));
    fails(&1.5f32);
    fails(&Some(1u8));
    fails(&());
    fails(&vec![1u8]);
    fails(&(1u8, 2u8));
    fails(&std::collections::BTreeMap::from([(1u8, 2u8)]));
    fails(&Probe(1));
    fails(&EveryShape::Unit);
    fails(&EveryShape::Newtype(1));
    fails(&EveryShape::Tuple(1, 2));
    fails(&EveryShape::Struct { x: 1 });
    fails(&cbor::tag::AllowAny(None, 1u8));
    fails(&cbor::tag::AllowAny(Some(1), 1u8));
    fails(&cbor::Value::Tag(1, Box::new(cbor::Value::Null)));
    fails(&u128::MAX);
    fails(&i128::MIN);

    // And with the failure delayed past the first header, so the error
    // strikes inside element and body writes.
    fn fails_at<T: Serialize>(value: &T, left: usize) {
        assert!(matches!(
            cbor::to_writer(value, LimitedWriter { left }),
            Err(cbor::ser::Error::Io(..))
        ));
    }

    fails_at(&"text", 1); // text body
    fails_at(&serde_bytes::ByteBuf::from(vec![1u8]), 1); // bytes body
    fails_at(&vec![1u8, 2], 1); // array element
    fails_at(&std::collections::BTreeMap::from([(1u8, 2u8)]), 2); // map value
    fails_at(&EveryShape::Newtype(1), 1); // variant name
    fails_at(&EveryShape::Newtype(1), 9); // variant payload
    fails_at(&EveryShape::Tuple(1, 2), 7); // tuple header
    fails_at(&EveryShape::Struct { x: 1 }, 8); // struct field
    fails_at(&cbor::Value::Tag(1, Box::new(cbor::Value::Null)), 1); // tag payload
    fails_at(&u128::MAX, 1); // bignum body
    fails_at(&cbor::cbor!({"k" => [1]}).unwrap(), 1);
    fails_at(&cbor::cbor!({"k" => [1]}).unwrap(), 2);
    fails_at(&cbor::cbor!({"k" => [1]}).unwrap(), 4);
}

#[test]
fn writer_failures_propagate_from_core_helpers() {
    use cbor::core::Encoder;

    assert!(Encoder::from(FailWriter).bytes(b"x").is_err());
    assert!(Encoder::from(FailWriter).text("x").is_err());
    assert!(Encoder::from(LimitedWriter { left: 1 })
        .bytes(b"x")
        .is_err());
    assert!(Encoder::from(LimitedWriter { left: 1 }).text("x").is_err());
}

// An iterator without an exact size hint forces an indefinite-length
// container, whose Break also has to be written.
struct UnsizedSeq;

impl Serialize for UnsizedSeq {
    fn serialize<S: serde::Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        serializer.collect_seq((1u8..=2).filter(|_| true))
    }
}

#[test]
fn writer_failures_at_precise_offsets() {
    fn fails_at<T: Serialize>(value: &T, left: usize) {
        assert!(matches!(
            cbor::to_writer(value, LimitedWriter { left }),
            Err(cbor::ser::Error::Io(..))
        ));
    }

    #[derive(Serialize)]
    struct PlainStruct {
        x: u8,
    }

    fails_at(&i128::MIN, 1); // bignum body after the tag
    fails_at(&PlainStruct { x: 1 }, 1); // plain struct field name
    fails_at(&EveryShape::Tuple(1, 2), 1); // variant name
    fails_at(&EveryShape::Struct { x: 1 }, 1); // variant name
    fails_at(&EveryShape::Struct { x: 1 }, 9); // field name
    fails_at(&std::collections::BTreeMap::from([(1u8, 2u8)]), 1); // map key
    fails_at(&UnsizedSeq, 3); // the closing break
    fails_at(&cbor::tag::AllowAny(Some(1), "xx"), 1); // tagged payload
    fails_at(&cbor::Value::Array(vec![cbor::Value::Null]), 1); // array element
    fails_at(&cbor::cbor!({"k" => 1}).unwrap(), 1); // map key (Value)
}
