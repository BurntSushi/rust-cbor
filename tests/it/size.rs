//! Tests for `serialized_size`: the result must equal the actual encoded
//! length for every shape the serializer can produce.

use std::collections::BTreeMap;

use cbor::{cbor, Value};
use serde::{Deserialize, Serialize};

fn assert_size<T: ?Sized + Serialize>(value: &T) {
    let actual = cbor::to_vec(value).unwrap().len() as u64;
    assert_eq!(cbor::serialized_size(value).unwrap(), actual);
}

#[derive(Serialize, Deserialize)]
struct Struct {
    a: u8,
    b: String,
}

#[derive(Serialize)]
enum Enum {
    Unit,
    Newtype(u32),
    Tuple(u32, u32),
    Struct { x: u8 },
}

#[test]
fn integers() {
    for v in [
        0u64,
        23,
        24,
        255,
        256,
        65_535,
        65_536,
        u32::MAX as u64,
        u32::MAX as u64 + 1,
        u64::MAX,
    ] {
        assert_size(&v);
    }

    for v in [
        -1i64,
        -24,
        -25,
        -256,
        -257,
        -65_536,
        -65_537,
        i32::MIN as i64,
        i64::MIN,
        i64::MAX,
    ] {
        assert_size(&v);
    }

    assert_size(&7u8);
    assert_size(&-7i8);
    assert_size(&700u16);
    assert_size(&-700i16);
    assert_size(&70_000u32);
    assert_size(&-70_000i32);

    // 128-bit values inside and outside the bignum range.
    for v in [0u128, u64::MAX as u128, u64::MAX as u128 + 1, u128::MAX] {
        assert_size(&v);
    }
    for v in [
        0i128,
        i64::MIN as i128,
        -(u64::MAX as i128) - 1,
        -(u64::MAX as i128) - 2,
        i128::MIN,
        i128::MAX,
    ] {
        assert_size(&v);
    }
}

#[test]
fn floats() {
    for v in [
        0.0f64,
        -0.0,
        1.0,
        1.5,
        1.1,
        65504.0,
        100000.0,
        1.0e300,
        5.960464477539063e-8,
        f64::INFINITY,
        f64::NEG_INFINITY,
        f64::NAN,
        f64::from_bits(0x7ff8_dead_beef_0000), // NaN with payload
        -f64::NAN,
    ] {
        assert_size(&v);
    }
    assert_size(&1.5f32);
    assert_size(&f32::NAN);
}

#[test]
fn strings_and_bytes() {
    for len in [0usize, 1, 23, 24, 255, 256, 65_536] {
        assert_size(&"a".repeat(len));
        assert_size(&serde_bytes::ByteBuf::from(vec![0xab; len]));
    }

    for c in ['a', 'ß', '水', '🦀'] {
        assert_size(&c);
    }
}

#[test]
fn containers() {
    assert_size(&Option::<u8>::None);
    assert_size(&Some(42u8));
    assert_size(&());
    assert_size(&(0..30).collect::<Vec<u64>>());
    assert_size(&(1u8, "hi", 3u64));
    assert_size(&BTreeMap::from([("a", 1u8), ("long_key", 2)]));
    assert_size(&Struct {
        a: 7,
        b: "hello".into(),
    });
    assert_size(&Enum::Unit);
    assert_size(&Enum::Newtype(123));
    assert_size(&Enum::Tuple(1, 700));
    assert_size(&Enum::Struct { x: 9 });
}

#[test]
fn tags_and_values() {
    use cbor::tag::{AllowAny, RequireExact};

    assert_size(&RequireExact::<_, 42>("tagged"));
    assert_size(&AllowAny(Some(0x1_0000), 123u64));
    assert_size(&AllowAny(None, "plain"));

    let value = cbor!({
        "big" => u128::MAX,
        "nested" => [1, 2.5, null, {"k" => true}],
    })
    .unwrap();
    assert_size(&Value::Tag(99, Box::new(value)));
}

// serde only reports a sequence length when the size hint is exact, so a
// filtered iterator produces an indefinite-length array.
struct UnsizedSeq;

impl Serialize for UnsizedSeq {
    fn serialize<S: serde::Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        serializer.collect_seq((1u8..=3).filter(|_| true))
    }
}

#[test]
fn indefinite_containers() {
    assert_size(&UnsizedSeq);
}

// A type serialized through `collect_str`, which is implemented without
// buffering the formatted output.
struct Displayed;

impl std::fmt::Display for Displayed {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "id-{}-水", 42)
    }
}

impl Serialize for Displayed {
    fn serialize<S: serde::Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        serializer.collect_str(self)
    }
}

#[test]
fn collected_strings() {
    assert_size(&Displayed);
    assert_eq!(
        cbor::to_vec(&Displayed).unwrap(),
        cbor::to_vec(&"id-42-水").unwrap()
    );
    let back: String = cbor::from_slice(&cbor::to_vec(&Displayed).unwrap()).unwrap();
    assert_eq!(back, "id-42-水");
}

// Misbehaving Display implementations are reported as errors instead of
// producing corrupt output.
struct Shifty(std::cell::Cell<usize>, &'static [&'static str]);

impl std::fmt::Display for Shifty {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let n = self.0.get();
        self.0.set(n + 1);
        f.write_str(self.1[n.min(self.1.len() - 1)])
    }
}

impl Serialize for Shifty {
    fn serialize<S: serde::Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        serializer.collect_str(self)
    }
}

struct FailingDisplay;

impl std::fmt::Display for FailingDisplay {
    fn fmt(&self, _: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        Err(std::fmt::Error)
    }
}

impl Serialize for FailingDisplay {
    fn serialize<S: serde::Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        serializer.collect_str(self)
    }
}

#[test]
fn misbehaving_display_is_rejected() {
    // Grows between the measuring and the writing pass.
    let grow = Shifty(std::cell::Cell::new(0), &["ab", "abcd"]);
    assert!(matches!(
        cbor::to_vec(&grow),
        Err(cbor::ser::Error::Value(..))
    ));

    // Shrinks between the passes.
    let shrink = Shifty(std::cell::Cell::new(0), &["abcd", "ab"]);
    assert!(matches!(
        cbor::to_vec(&shrink),
        Err(cbor::ser::Error::Value(..))
    ));

    // Fails outright.
    assert!(matches!(
        cbor::to_vec(&FailingDisplay),
        Err(cbor::ser::Error::Value(..))
    ));

    // An I/O failure while streaming the body is an I/O error.
    struct Limited(usize);
    impl std::io::Write for Limited {
        fn write(&mut self, data: &[u8]) -> std::io::Result<usize> {
            if self.0 == 0 {
                return Err(std::io::Error::other("limit"));
            }
            let n = self.0.min(data.len());
            self.0 -= n;
            Ok(n)
        }
        fn flush(&mut self) -> std::io::Result<()> {
            Ok(())
        }
    }
    assert!(matches!(
        cbor::to_writer(&Displayed, Limited(1)),
        Err(cbor::ser::Error::Io(..))
    ));
    // And while writing the text header itself.
    assert!(matches!(
        cbor::to_writer(&Displayed, Limited(0)),
        Err(cbor::ser::Error::Io(..))
    ));
}

#[test]
fn errors_propagate() {
    struct Boom;

    impl Serialize for Boom {
        fn serialize<S: serde::Serializer>(&self, _: S) -> Result<S::Ok, S::Error> {
            Err(serde::ser::Error::custom("boom"))
        }
    }

    assert!(cbor::serialized_size(&Boom).is_err());
}
