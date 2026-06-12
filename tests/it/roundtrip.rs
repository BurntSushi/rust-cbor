//! Round-trip and wire-format tests for the serde interface.

use std::collections::BTreeMap;
use std::fmt::Debug;

use serde::de::DeserializeOwned;
use serde::{Deserialize, Serialize};

fn roundtrip<T: Serialize + DeserializeOwned + PartialEq + Debug>(value: T) {
    let bytes = cbor::to_vec(&value).unwrap();
    let back: T = cbor::from_slice(&bytes).unwrap();
    assert_eq!(value, back);
}

fn assert_wire<T: Serialize>(value: T, hex: &str) {
    assert_eq!(hex::encode(cbor::to_vec(&value).unwrap()), hex);
}

#[test]
fn primitives() {
    roundtrip(false);
    roundtrip(true);
    roundtrip(0u8);
    roundtrip(23u8);
    roundtrip(255u8);
    roundtrip(u16::MAX);
    roundtrip(u32::MAX);
    roundtrip(u64::MAX);
    roundtrip(i8::MIN);
    roundtrip(i16::MIN);
    roundtrip(i32::MIN);
    roundtrip(i64::MIN);
    roundtrip(0.0f32);
    roundtrip(1.625f32);
    roundtrip(core::f64::consts::PI);
    roundtrip('a');
    roundtrip('\u{6c34}');
    roundtrip(String::from("hello, world"));
    roundtrip(());
}

#[test]
fn big_integers() {
    roundtrip(u128::MAX);
    roundtrip(i128::MAX);
    roundtrip(i128::MIN);
    roundtrip(u64::MAX as u128 + 1);
    roundtrip(-(u64::MAX as i128) - 2);

    // Values within the u64/i64 range encode as plain integers...
    assert_wire(1u128, "01");
    assert_wire(-1i128, "20");
    // ...and beyond it as bignums.
    assert_wire(u64::MAX as u128 + 1, "c249010000000000000000");

    // A bignum that fits in a primitive type decodes into it.
    let small_bignum = hex::decode("c24101").unwrap(); // 2(h'01')
    assert_eq!(cbor::from_slice::<u8>(&small_bignum).unwrap(), 1);
}

#[test]
fn widening_and_narrowing() {
    // Integer width is not a wire property: anything fits anywhere as long
    // as the value is in range.
    let one = cbor::to_vec(&1u8).unwrap();
    assert_eq!(cbor::from_slice::<u64>(&one).unwrap(), 1);
    assert_eq!(cbor::from_slice::<i8>(&one).unwrap(), 1);
    assert_eq!(cbor::from_slice::<u128>(&one).unwrap(), 1);

    let big = cbor::to_vec(&300u64).unwrap();
    assert!(cbor::from_slice::<u8>(&big).is_err());

    let neg = cbor::to_vec(&-1i8).unwrap();
    assert!(cbor::from_slice::<u64>(&neg).is_err());

    // Floats decode at any width (f32 -> f64).
    let f = cbor::to_vec(&1.5f32).unwrap();
    assert_eq!(cbor::from_slice::<f64>(&f).unwrap(), 1.5);
}

#[test]
fn options() {
    roundtrip(Option::<u32>::None);
    roundtrip(Some(42u32));
    assert_wire(Option::<u32>::None, "f6");

    // Like in most formats, Some(None) collapses to null on the wire.
    let bytes = cbor::to_vec(&Some(Option::<String>::None)).unwrap();
    assert_eq!(
        cbor::from_slice::<Option<Option<String>>>(&bytes).unwrap(),
        None
    );

    // Undefined (0xf7) also decodes as None.
    assert_eq!(cbor::from_slice::<Option<u32>>(&[0xf7]).unwrap(), None);
}

#[test]
fn sequences_and_maps() {
    roundtrip(vec![1u32, 2, 3]);
    roundtrip((1u8, String::from("x"), 1.5f64));
    roundtrip([0u8; 0].to_vec());

    let mut map = BTreeMap::new();
    map.insert(String::from("a"), 1u32);
    map.insert(String::from("b"), 2u32);
    roundtrip(map);

    let mut intmap = BTreeMap::new();
    intmap.insert(-1i64, vec![1u8]);
    roundtrip(intmap);
}

#[test]
fn byte_strings() {
    let bytes = serde_bytes::ByteBuf::from(vec![1u8, 2, 3, 4]);
    let encoded = cbor::to_vec(&bytes).unwrap();
    assert_eq!(hex::encode(&encoded), "4401020304");
    let back: serde_bytes::ByteBuf = cbor::from_slice(&encoded).unwrap();
    assert_eq!(back, bytes);

    // Liberality: a byte string decodes as Vec<u8> (array of ints) and an
    // array of ints decodes as a byte buffer.
    let v: Vec<u8> = cbor::from_slice(&encoded).unwrap();
    assert_eq!(v, vec![1, 2, 3, 4]);

    let array = cbor::to_vec(&vec![1u8, 2, 3, 4]).unwrap();
    assert_eq!(hex::encode(&array), "8401020304");
    let back: serde_bytes::ByteBuf = cbor::from_slice(&array).unwrap();
    assert_eq!(back, bytes);
}

#[derive(Debug, PartialEq, Deserialize, Serialize)]
struct Plain {
    name: String,
    size: u64,
    tags: Vec<String>,
    ratio: Option<f64>,
}

#[derive(Debug, PartialEq, Deserialize, Serialize)]
struct Newtype(u32);

#[derive(Debug, PartialEq, Deserialize, Serialize)]
struct TupleStruct(u32, String);

#[derive(Debug, PartialEq, Deserialize, Serialize)]
struct Unit;

#[test]
fn structs() {
    roundtrip(Plain {
        name: "x".into(),
        size: 42,
        tags: vec!["a".into()],
        ratio: None,
    });
    roundtrip(Newtype(99));
    roundtrip(TupleStruct(1, "two".into()));
    roundtrip(Unit);

    // A struct is a map keyed by field names.
    assert_wire(Newtype(7), "07"); // newtype is transparent
    assert_wire(Unit, "f6"); // unit is null
}

#[derive(Debug, PartialEq, Deserialize, Serialize)]
enum Enum {
    Unit,
    Newtype(u32),
    Tuple(u32, u32),
    Struct { x: u32 },
}

#[test]
fn enums() {
    roundtrip(Enum::Unit);
    roundtrip(Enum::Newtype(42));
    roundtrip(Enum::Tuple(1, 2));
    roundtrip(Enum::Struct { x: 7 });
    roundtrip(vec![Enum::Unit, Enum::Newtype(0)]);

    // The wire format matches ciborium: a unit variant is a bare string,
    // anything else is a single-entry map keyed by the variant name.
    assert_wire(Enum::Unit, "64556e6974"); // "Unit"
    assert_wire(Enum::Newtype(42), "a1674e657774797065182a"); // {"Newtype": 42}
    assert_wire(Enum::Tuple(1, 2), "a1655475706c65820102"); // {"Tuple": [1, 2]}
    assert_wire(Enum::Struct { x: 7 }, "a166537472756374a1617807"); // {"Struct": {"x": 7}}
}

#[test]
fn skipped_and_unknown_fields() {
    #[derive(Debug, PartialEq, Deserialize, Serialize)]
    struct Small {
        name: String,
    }

    // Extra fields in the input are ignored.
    let full = cbor::to_vec(&Plain {
        name: "x".into(),
        size: 42,
        tags: vec![],
        ratio: Some(0.5),
    })
    .unwrap();

    let small: Small = cbor::from_slice(&full).unwrap();
    assert_eq!(small, Small { name: "x".into() });
}

#[test]
fn indefinite_containers_decode() {
    // [_ 1, 2] (indefinite array)
    let bytes = hex::decode("9f0102ff").unwrap();
    assert_eq!(cbor::from_slice::<Vec<u32>>(&bytes).unwrap(), vec![1, 2]);

    // {_ "a": 1} (indefinite map)
    let bytes = hex::decode("bf616101ff").unwrap();
    let map: BTreeMap<String, u32> = cbor::from_slice(&bytes).unwrap();
    assert_eq!(map.len(), 1);
    assert_eq!(map["a"], 1);

    // (_ "strea", "ming") (segmented text)
    let bytes = hex::decode("7f657374726561646d696e67ff").unwrap();
    assert_eq!(cbor::from_slice::<String>(&bytes).unwrap(), "streaming");

    // (_ h'0102', h'030405') (segmented bytes)
    let bytes = hex::decode("5f42010243030405ff").unwrap();
    let buf: serde_bytes::ByteBuf = cbor::from_slice(&bytes).unwrap();
    assert_eq!(buf.as_ref(), &[1, 2, 3, 4, 5]);
}

#[test]
fn unknown_tags_are_transparent() {
    // 4711("x") decodes as a plain string when a string is requested.
    let bytes = hex::decode("d912676178").unwrap();
    assert_eq!(cbor::from_slice::<String>(&bytes).unwrap(), "x");

    // 1(1363896240) decodes as a plain integer.
    let bytes = hex::decode("c11a514b67b0").unwrap();
    assert_eq!(cbor::from_slice::<u64>(&bytes).unwrap(), 1363896240);
}

#[test]
fn stream_of_items() {
    let mut buffer = Vec::new();
    cbor::to_writer(&1u32, &mut buffer).unwrap();
    cbor::to_writer(&"two", &mut buffer).unwrap();
    cbor::to_writer(&vec![3u8], &mut buffer).unwrap();

    let mut iter = cbor::de::Deserializer::from_reader(&buffer[..]).into_iter::<cbor::Value>();
    assert_eq!(iter.next().unwrap().unwrap(), cbor::Value::from(1));
    assert_eq!(iter.next().unwrap().unwrap(), cbor::Value::from("two"));
    assert_eq!(
        iter.next().unwrap().unwrap(),
        cbor::Value::Array(vec![cbor::Value::from(3)])
    );
    assert!(iter.next().is_none());

    // A truncated trailing item is an error, not a silent end.
    let mut truncated = Vec::new();
    cbor::to_writer(&1u32, &mut truncated).unwrap();
    truncated.extend_from_slice(&[0x19, 0x01]); // u16 header missing a byte

    let mut iter = cbor::de::Deserializer::from_reader(&truncated[..]).into_iter::<u32>();
    assert_eq!(iter.next().unwrap().unwrap(), 1);
    assert!(iter.next().unwrap().is_err());
}

#[test]
fn integer_wire_forms() {
    // Positive values through the signed entry points.
    assert_wire(7i8, "07");
    assert_wire(7i64, "07");
    assert_wire(2i128, "02");
    assert_wire(-2i128, "21");
}

// serde only reports a sequence length when the iterator's size hint is
// exact, so a filtered iterator produces an indefinite-length array.
struct Unsized;

impl Serialize for Unsized {
    fn serialize<S: serde::Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        serializer.collect_seq((1u8..=3).filter(|_| true))
    }
}

// A map of unknown size produces an indefinite-length map.
struct UnsizedMap;

impl Serialize for UnsizedMap {
    fn serialize<S: serde::Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        use serde::ser::SerializeMap;
        let mut acc = serializer.serialize_map(None)?;
        acc.serialize_entry(&1u8, &2u8)?;
        acc.end()
    }
}

#[test]
fn indefinite_containers_encode() {
    assert_wire(Unsized, "9f010203ff");
    assert_eq!(
        cbor::from_slice::<Vec<u8>>(&cbor::to_vec(&Unsized).unwrap()).unwrap(),
        vec![1, 2, 3]
    );

    assert_wire(UnsizedMap, "bf0102ff");
    let map: BTreeMap<u8, u8> = cbor::from_slice(&cbor::to_vec(&UnsizedMap).unwrap()).unwrap();
    assert_eq!(map, [(1, 2)].into());
}
